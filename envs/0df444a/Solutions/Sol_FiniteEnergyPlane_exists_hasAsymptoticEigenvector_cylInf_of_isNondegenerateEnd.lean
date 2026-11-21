-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T20:52:46.84584+00:00
-- url     : https://prove2.me/submissions/1719be8e-c07e-4ad2-ba34-35b26d95dd0a

import Definitions.Def_FiniteEnergyPlane_Asymptotics
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

/-! F child C1: a finite-energy plane with a nondegenerate end at `∞` has an asymptotic
eigenvector there (no spectral window). Copied from `DGA_Eig1` without the winding part. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hfe : IsFiniteEnergyCurve H J Set.univ u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ (μ : ℝ) (v : ℝ → V 1), HasAsymptoticEigenvector H J u cylInf P 1 μ v := by
  classical
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
  refine ⟨μ, v, ?_⟩
  unfold HasAsymptoticEigenvector at hv ⊢
  rwa [dge_endW_inv] at hv

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hfe : IsFiniteEnergyCurve H J Set.univ u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ (μ : ℝ) (v : ℝ → V 1), HasAsymptoticEigenvector H J u cylInf P 1 μ v :=
  exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd_aux H hH J hJ P u hfe huP
