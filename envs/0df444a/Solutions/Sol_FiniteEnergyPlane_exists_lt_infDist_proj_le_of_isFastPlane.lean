-- Prove2me | solution 1 for FiniteEnergyPlane.exists_lt_infDist_proj_le_of_isFastPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T21:14:10.062211+00:00
-- url     : https://prove2.me/submissions/be880dc1-48c0-4b5c-b0c0-6d72f7a357d9

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
import Theorems.Thm_FiniteEnergyPlane_exists_hasAsymptoticEigenvector_lt_of_isFastPlane



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

/-! A4b: the distance to the orbit decays at a rate strictly below the window. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A4: a fast plane approaches its orbit at a rate strictly faster than the window. -/
theorem exists_lt_infDist_proj_le_of_isFastPlane_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) :
    ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)) := by
  have hfe : IsFiniteEnergyCurve H J Set.univ u := hu.1
  obtain ⟨μ, hμδ, v, hv⟩ :=
    exists_hasAsymptoticEigenvector_lt_of_isFastPlane H hH J hJ P u hu huP δ hwin
  have hμ0 : μ < 0 := by have := hv.2.1; linarith
  refine ⟨μ, hμδ, ?_⟩
  obtain ⟨C₀, s₀, hC₀⟩ :=
    infDist_endW_le_of_hasAsymptoticEigenvector H hH J u cylInf P 1 μ v hv
  set ex : ℝ := μ / (2 * π) with hex
  have hπ : 0 < 2 * π := by positivity
  have hex0 : ex ≤ 0 := div_nonpos_of_nonpos_of_nonneg hμ0.le hπ.le
  set s₁ : ℝ := max s₀ 0 with hs₁
  set R : ℝ := Real.exp (2 * π * s₁) with hR
  have hR1 : 1 ≤ R := Real.one_le_exp (mul_nonneg hπ.le (le_max_right _ _))
  set Cf : ℝ := max C₀ 0 * ((2 : ℝ) ^ ex)⁻¹ with hCf
  have hfar : ∀ z : ℂ, R ≤ ‖z‖ →
      infDist (proj H (u z)) (Set.range P.x) ≤ Cf * (1 + ‖z‖) ^ ex := by
    intro z hz
    have hz1 : 1 ≤ ‖z‖ := hR1.trans hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
    have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
    set s : ℝ := Real.log ‖z‖ / (2 * π) with hs
    have hss : s₁ ≤ s := by
      rw [hs, le_div_iff₀ hπ]
      have h' : Real.exp (2 * π * s₁) ≤ ‖z‖ := hz
      have := Real.log_le_log (Real.exp_pos _) h'
      rw [Real.log_exp] at this
      linarith
    have hs0 : s₀ ≤ s := le_trans (le_max_left _ _) hss
    have h1 := hC₀ s hs0 (Complex.arg z / (2 * π))
    simp only [endW] at h1
    rw [dge_cylInf_log_arg hz0] at h1
    have hexp : Real.exp (1 * μ * s) = ‖z‖ ^ ex := by
      rw [Real.rpow_def_of_pos hzpos, hs, hex]
      congr 1
      field_simp
    have hhalf : ‖z‖ ^ ex ≤ ((1 + ‖z‖) / 2) ^ ex :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hex0
    rw [Real.div_rpow (by positivity) (by norm_num)] at hhalf
    have hpos : 0 ≤ Real.exp (1 * μ * s) := (Real.exp_pos _).le
    calc infDist (proj H (u z)) (Set.range P.x) ≤ C₀ * Real.exp (1 * μ * s) := h1
      _ ≤ max C₀ 0 * Real.exp (1 * μ * s) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ ≤ max C₀ 0 * ((1 + ‖z‖) ^ ex / (2 : ℝ) ^ ex) := by
          rw [hexp]
          exact mul_le_mul_of_nonneg_left hhalf (le_max_right _ _)
      _ = Cf * (1 + ‖z‖) ^ ex := by rw [hCf]; ring
  have hcont : Continuous fun z => infDist (proj H (u z)) (Set.range P.x) := by
    have hu_c : Continuous u := (contDiffOn_univ.1 hfe.1).continuous
    have hpu : Continuous fun z => proj H (u z) := continuous_iff_continuousAt.2 fun z =>
      ((contDiffAt_aCoord_proj H hH _ (hfe.2.1 z trivial)).2.continuousAt).comp
        hu_c.continuousAt
    exact (continuous_infDist_pt _).comp hpu
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hcont.continuousOn
  have hRpos : 0 < (1 + R) ^ ex := Real.rpow_pos_of_pos (by linarith) _
  set Cn : ℝ := max B 0 / (1 + R) ^ ex with hCn
  have hnear : ∀ z : ℂ, ‖z‖ ≤ R →
      infDist (proj H (u z)) (Set.range P.x) ≤ Cn * (1 + ‖z‖) ^ ex := by
    intro z hz
    have hb := hB z (mem_closedBall_zero_iff.2 hz)
    rw [Real.norm_eq_abs] at hb
    have hmono : (1 + R) ^ ex ≤ (1 + ‖z‖) ^ ex :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hex0
    calc infDist (proj H (u z)) (Set.range P.x) ≤ max B 0 :=
          (le_abs_self _).trans (hb.trans (le_max_left _ _))
      _ = Cn * (1 + R) ^ ex := by rw [hCn, div_mul_cancel₀ _ hRpos.ne']
      _ ≤ Cn * (1 + ‖z‖) ^ ex :=
          mul_le_mul_of_nonneg_left hmono (div_nonneg (le_max_right _ _) hRpos.le)
  refine ⟨max Cn Cf, fun z => ?_⟩
  have hp : 0 ≤ (1 + ‖z‖) ^ ex := Real.rpow_nonneg (by positivity) _
  rcases le_total ‖z‖ R with hz | hz
  · exact (hnear z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · exact (hfar z hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) :
    ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)) :=
  exists_lt_infDist_proj_le_of_isFastPlane_aux H hH J hJ P u hu huP δ hwin
