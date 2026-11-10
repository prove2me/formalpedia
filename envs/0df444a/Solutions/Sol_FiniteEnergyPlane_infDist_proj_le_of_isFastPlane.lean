-- Prove2me | solution 1 for FiniteEnergyPlane.infDist_proj_le_of_isFastPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T14:23:04.020205+00:00
-- url     : https://prove2.me/submissions/7e912abb-2027-4a0a-9b49-1cde670124ed

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



/-!
# A fast plane approaches its orbit at a window rate

Glue: `ũ(z) = u(z⁻¹)` turns `∞` into the puncture `0`; Theorem 2.11 gives an asymptotic eigenvalue
`μ < 0` with eigenvector `v`; Lemma 2.16 identifies the winding of `v` with `wind_∞ = 1` (fast), so
`μ` has winding `1` and the window forces `μ < δ`. The child bounds the distance by `C e^{μs}`, and
`e^{μs} = ‖z‖^{μ/2π} ≤ ‖z‖^{δ/2π}` at `z = e^{2π(s+it)}`; a compact ball covers the rest.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma idp_hasWindInfAt_unique {H : V 1 → ℝ} {u : ℂ → V 1} {e : ℝ → ℝ → ℂ} {ε : ℝ} {k m : ℤ}
    (hk : HasWindInfAt H u e ε k) (hm : HasWindInfAt H u e ε m) : k = m := by
  obtain ⟨s₀, hs₀⟩ := hk
  obtain ⟨s₁, hs₁⟩ := hm
  exact hasLoopWind_unique (hs₀ _ (le_max_left s₀ s₁)) (hs₁ _ (le_max_right s₀ s₁))

lemma idp_cylEnd_inv (s t : ℝ) : (cylEnd s t)⁻¹ = cylInf s t := by
  unfold cylEnd cylInf cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.ofReal_inv, ← Real.exp_neg, neg_neg, ← Complex.exp_neg]
  congr 2
  ring

lemma idp_endA_inv {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) :
    endA H (fun z => u z⁻¹) cylEnd = endA H u cylInf := by
  funext p
  simp only [endA, idp_cylEnd_inv]

lemma idp_endW_inv {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) :
    endW H (fun z => u z⁻¹) cylEnd = endW H u cylInf := by
  funext p
  simp only [endW, idp_cylEnd_inv]

lemma idp_cylEnd_eq : cylEnd = cylEndAt 0 := rfl

lemma idp_cylInf_log_arg {z : ℂ} (hz : z ≠ 0) :
    cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
  have hπ : (2 * π) ≠ 0 := by positivity
  unfold cylInf ccwLoop
  rw [mul_div_cancel₀ _ hπ, mul_div_cancel₀ _ hπ, Real.exp_log (norm_pos_iff.2 hz)]
  exact Complex.norm_mul_exp_arg_mul_I z

theorem infDist_proj_le_of_isFastPlane_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) :
    ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (δ / (2 * π)) := by
  classical
  have hfe : IsFiniteEnergyCurve H J Set.univ u := hu.1
  have hP : P.IsPrime := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP
  have hW1 : HasWindInfAt H u cylInf 1 1 :=
    (isFastPlane_iff_hasWindInfAt_one H hH J hJ u hfe P hP huP).1 hu
  have hnc : ∃ z₁ z₂, u z₁ ≠ u z₂ :=
    exists_ne_of_isNondegenerateEnd H u cylInf P one_ne_zero huP
  -- the inverted curve `ũ(z) = u(z⁻¹)` near `0`
  obtain ⟨hũ, hdens⟩ := isFiniteEnergyCurve_comp_inv H hH J hJ u hfe
  have hndũ : IsNondegenerateEnd H (fun z => u z⁻¹) cylEnd P 1 := by
    unfold IsNondegenerateEnd
    rw [idp_endA_inv, idp_endW_inv]
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
  -- asymptotic eigenvalue and its winding
  obtain ⟨μ, v, hv⟩ :=
    (asymptotic_eigenvector H hH J hJ (fun z => u z⁻¹) hũ P 1 (Or.inl rfl) hndũ).2 hneũ
  obtain ⟨k, hk, hWIũ⟩ := exists_hasWindInfAt_of_hasAsymptoticEigenvector H hH J hJ 0 1 one_pos
    (fun z => u z⁻¹) hũ P 1 (Or.inl rfl) μ v (by rw [← idp_cylEnd_eq]; exact hv)
  have hWI : HasWindInfAt H u cylInf 1 k := by
    have h := hWIũ
    rw [← idp_cylEnd_eq] at h
    unfold HasWindInfAt at h ⊢
    rwa [idp_endW_inv] at h
  have hk1 : k = 1 := idp_hasWindInfAt_unique hWI hW1
  subst hk1
  have hEW : HasEigenWind J P μ 1 := hasEigenWind_of_isAsymptoticEigen H hH J hJ P μ v 1 hv.1 hk
  have hμδ : μ < δ := by
    rcases hwin μ 1 hEW with h | h
    · exact h.1
    · exact absurd h.2 (by norm_num)
  -- distance along the end
  obtain ⟨C₀, s₀, hC₀⟩ :=
    infDist_endW_le_of_hasAsymptoticEigenvector H hH J (fun z => u z⁻¹) cylEnd P 1 μ v hv
  set ex : ℝ := δ / (2 * π) with hex
  have hπ : 0 < 2 * π := by positivity
  have hex0 : ex ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ.le hπ.le
  set s₁ : ℝ := max s₀ 0 with hs₁
  set R : ℝ := Real.exp (2 * π * s₁) with hR
  have hR1 : 1 ≤ R := Real.one_le_exp (mul_nonneg hπ.le (le_max_right _ _))
  -- far region
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
    rw [idp_endW_inv] at h1
    simp only [endW] at h1
    rw [idp_cylInf_log_arg hz0] at h1
    have hexp : Real.exp (1 * μ * s) = ‖z‖ ^ (μ / (2 * π)) := by
      rw [Real.rpow_def_of_pos hzpos, hs]
      congr 1
      field_simp
    have hmono : ‖z‖ ^ (μ / (2 * π)) ≤ ‖z‖ ^ ex :=
      Real.rpow_le_rpow_of_exponent_le hz1 (div_le_div_of_nonneg_right hμδ.le hπ.le)
    have hhalf : ‖z‖ ^ ex ≤ ((1 + ‖z‖) / 2) ^ ex :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hex0
    rw [Real.div_rpow (by positivity) (by norm_num)] at hhalf
    have hpos : 0 ≤ Real.exp (1 * μ * s) := (Real.exp_pos _).le
    calc infDist (proj H (u z)) (Set.range P.x) ≤ C₀ * Real.exp (1 * μ * s) := h1
      _ ≤ max C₀ 0 * Real.exp (1 * μ * s) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ ≤ max C₀ 0 * ((1 + ‖z‖) ^ ex / (2 : ℝ) ^ ex) := by
          rw [hexp]
          exact mul_le_mul_of_nonneg_left (hmono.trans hhalf) (le_max_right _ _)
      _ = Cf * (1 + ‖z‖) ^ ex := by rw [hCf]; ring
  -- near region
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

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) :
    ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (δ / (2 * π)) :=
  infDist_proj_le_of_isFastPlane_aux H hH J hJ P u hu huP δ hδ hwin
