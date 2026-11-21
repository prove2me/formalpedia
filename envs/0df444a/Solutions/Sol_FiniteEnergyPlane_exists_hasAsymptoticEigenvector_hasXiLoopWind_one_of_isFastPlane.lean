-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T23:20:05.543186+00:00
-- url     : https://prove2.me/submissions/fe48caee-6905-456c-8ab0-43a1b4d53c4f

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_infDist_endW_le_of_hasAsymptoticEigenvector
import Theorems.Thm_FiniteEnergyPlane_asymptotic_eigenvector
import Theorems.Thm_FiniteEnergyPlane_exists_hasWindInfAt_of_hasAsymptoticEigenvector
import Theorems.Thm_FiniteEnergyPlane_hasEigenWind_of_isAsymptoticEigen
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_iff_hasWindInfAt_one
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv
import Theorems.Thm_FiniteEnergyPlane_exists_dlambdaDensity_ne_zero_of_isOpen
import Theorems.Thm_FiniteEnergyPlane_exists_ne_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique



/-! Helpers for the fast-plane eigen-rate lemmas (copied from the U glue, renamed). -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma dge_hasWindInfAt_unique {H : V 1 → ℝ} {u : ℂ → V 1} {e : ℝ → ℝ → ℂ} {ε : ℝ} {k m : ℤ}
    (hk : HasWindInfAt H u e ε k) (hm : HasWindInfAt H u e ε m) : k = m := by
  obtain ⟨s₀, hs₀⟩ := hk
  obtain ⟨s₁, hs₁⟩ := hm
  exact hasLoopWind_unique (hs₀ _ (le_max_left s₀ s₁)) (hs₁ _ (le_max_right s₀ s₁))

lemma dge_cylEnd_inv (s t : ℝ) : (cylEnd s t)⁻¹ = cylInf s t := by
  unfold cylEnd cylInf cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.ofReal_inv, ← Real.exp_neg, neg_neg, ← Complex.exp_neg]
  congr 2
  ring

lemma dge_endA_inv {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) :
    endA H (fun z => u z⁻¹) cylEnd = endA H u cylInf := by
  funext p
  simp only [endA, dge_cylEnd_inv]

lemma dge_endW_inv {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) :
    endW H (fun z => u z⁻¹) cylEnd = endW H u cylInf := by
  funext p
  simp only [endW, dge_cylEnd_inv]

lemma dge_cylEnd_eq : cylEnd = cylEndAt 0 := rfl

lemma dge_cylInf_log_arg {z : ℂ} (hz : z ≠ 0) :
    cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
  have hπ : (2 * π) ≠ 0 := by positivity
  unfold cylInf ccwLoop
  rw [mul_div_cancel₀ _ hπ, mul_div_cancel₀ _ hπ, Real.exp_log (norm_pos_iff.2 hz)]
  exact Complex.norm_mul_exp_arg_mul_I z

end FiniteEnergyPlane

/-! A fast plane has an asymptotic eigenvector of winding `1` at `∞`: Theorem 2.11 at the
puncture `0` of `u(1/z)`, the winding of the eigenvector equals `wind_∞ = 1`. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ (μ : ℝ) (v : ℝ → V 1), HasAsymptoticEigenvector H J u cylInf P 1 μ v ∧
      HasXiLoopWind P v 1 := by
  classical
  have hfe : IsFiniteEnergyCurve H J Set.univ u := hu.1
  have hP : P.IsPrime := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP
  have hW1 : HasWindInfAt H u cylInf 1 1 :=
    (isFastPlane_iff_hasWindInfAt_one H hH J hJ u hfe P hP huP).1 hu
  have hnc : ∃ z₁ z₂, u z₁ ≠ u z₂ :=
    exists_ne_of_isNondegenerateEnd H u cylInf P one_ne_zero huP
  obtain ⟨hũ, hdens⟩ := isFiniteEnergyCurve_comp_inv H hH J hJ u hfe
  have hndũ : IsNondegenerateEnd H (fun z => u z⁻¹) cylEnd P 1 := by
    unfold IsNondegenerateEnd
    rw [dge_endA_inv, dge_endW_inv]
    exact huP
  have hneũ : ∀ ρ > 0, ∃ z ∈ ball (0 : ℂ) ρ \ {0}, dlambdaDensity H (fun z => u z⁻¹) z ≠ 0 := by
    intro ρ hρ
    obtain ⟨w, hw, hdw⟩ := exists_dlambdaDensity_ne_zero_of_isOpen H hH J hJ u hfe hnc
      {w : ℂ | ρ⁻¹ < ‖w‖} (isOpen_lt continuous_const continuous_norm)
      ⟨((ρ⁻¹ + 1 : ℝ) : ℂ), by
        show ρ⁻¹ < ‖((ρ⁻¹ + 1 : ℝ) : ℂ)‖
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith⟩
    have hw' : ρ⁻¹ < ‖w‖ := hw
    have hwpos : 0 < ‖w‖ := lt_trans (inv_pos.2 hρ) hw'
    have hw0 : w ≠ 0 := norm_pos_iff.1 hwpos
    refine ⟨w⁻¹, ⟨?_, inv_ne_zero hw0⟩, ?_⟩
    · rw [mem_ball_zero_iff, norm_inv]
      exact (inv_lt_comm₀ hρ hwpos).1 hw'
    · rw [hdens _ (inv_ne_zero hw0), inv_inv]
      exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (inv_ne_zero hw0)))) hdw
  obtain ⟨μ, v, hv⟩ :=
    (asymptotic_eigenvector H hH J hJ (fun z => u z⁻¹) hũ P 1 (Or.inl rfl) hndũ).2 hneũ
  obtain ⟨k, hk, hWIũ⟩ := exists_hasWindInfAt_of_hasAsymptoticEigenvector H hH J hJ 0 1 one_pos
    (fun z => u z⁻¹) hũ P 1 (Or.inl rfl) μ v (by rw [← dge_cylEnd_eq]; exact hv)
  have hWI : HasWindInfAt H u cylInf 1 k := by
    have h := hWIũ
    rw [← dge_cylEnd_eq] at h
    unfold HasWindInfAt at h ⊢
    rwa [dge_endW_inv] at h
  have hk1 : k = 1 := dge_hasWindInfAt_unique hWI hW1
  subst hk1
  refine ⟨μ, v, ?_, hk⟩
  unfold HasAsymptoticEigenvector at hv ⊢
  rwa [dge_endW_inv] at hv

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ (μ : ℝ) (v : ℝ → V 1), HasAsymptoticEigenvector H J u cylInf P 1 μ v ∧
      HasXiLoopWind P v 1 :=
  FiniteEnergyPlane.exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane_aux H hH J hJ P u hu huP
