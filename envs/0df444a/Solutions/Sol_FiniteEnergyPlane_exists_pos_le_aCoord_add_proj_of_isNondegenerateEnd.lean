-- Prove2me | solution 1 for FiniteEnergyPlane.exists_pos_le_aCoord_add_proj_of_isNondegenerateEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T15:55:22.195193+00:00
-- url     : https://prove2.me/submissions/868c5894-3c4c-440a-b0d9-bcd07c637ef8

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_eq_of_aCoord_eq_of_proj_eq
import Theorems.Thm_FiniteEnergyPlane_continuous_aCoord_proj_comp



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_pos_le_aCoord_add_proj_of_isNondegenerateEnd_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V n) (hu0 : ∀ z, u z ≠ 0)
    (huc : Continuous u) (hui : Function.Injective u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ η > 0, ∀ z, ρ ≤ ‖z‖ →
      η ≤ |aCoord H (u z) - aCoord H (u 0)| + ‖proj H (u z) - proj H (u 0)‖ := by
  obtain ⟨d, c, b, -, h1, -⟩ := huP
  obtain ⟨s₀, hs₀⟩ := h1 1 one_pos
  have hT := P.T_pos
  set s₁ : ℝ := max s₀ ((aCoord H (u 0) + 2 - d) / P.T) with hs₁
  have hs₁a : s₀ ≤ s₁ := le_max_left _ _
  have hs₁b : aCoord H (u 0) + 2 - d ≤ P.T * s₁ := by
    have := le_max_right s₀ ((aCoord H (u 0) + 2 - d) / P.T)
    rw [← hs₁, div_le_iff₀ hT] at this
    linarith
  set R : ℝ := Real.exp (2 * π * s₁) with hR
  have hRpos : 0 < R := Real.exp_pos _
  have hfar : ∀ z : ℂ, R ≤ ‖z‖ → aCoord H (u 0) + 1 ≤ aCoord H (u z) := by
    intro z hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hRpos hz
    set s : ℝ := Real.log ‖z‖ / (2 * π) with hs
    have h2pi : (0 : ℝ) < 2 * π := by positivity
    have hexp : Real.exp (2 * π * s) = ‖z‖ := by
      rw [hs, mul_div_cancel₀ _ h2pi.ne', Real.exp_log hzpos]
    have hss : s₁ ≤ s := by
      rw [hs, le_div_iff₀ h2pi, Real.le_log_iff_exp_le hzpos, mul_comm]
      exact hz
    have hcyl : cylInf s (Complex.arg z / (2 * π)) = z := by
      unfold cylInf ccwLoop
      rw [hexp]
      have e : ((2 * π * (Complex.arg z / (2 * π)) : ℝ) : ℂ) = (Complex.arg z : ℂ) := by
        congr 1
        field_simp
      rw [e]
      exact Complex.norm_mul_exp_arg_mul_I z
    have := hs₀ s (hs₁a.trans hss) (Complex.arg z / (2 * π))
    simp only [endA, hcyl, Real.norm_eq_abs, one_mul] at this
    have h3 := (abs_le.mp this).1
    have h4 : P.T * s₁ ≤ P.T * s := mul_le_mul_of_nonneg_left hss hT.le
    linarith
  obtain ⟨hac, hpc⟩ := continuous_aCoord_proj_comp H hH u hu0 huc
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) R ∩ {z | ρ ≤ ‖z‖}) :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hφc : ContinuousOn (fun z =>
      |aCoord H (u z) - aCoord H (u 0)| + ‖proj H (u z) - proj H (u 0)‖)
      (Metric.closedBall (0 : ℂ) R ∩ {z | ρ ≤ ‖z‖}) :=
    Continuous.continuousOn (by fun_prop)
  obtain ⟨η₀, hη₀, hη⟩ := hcomp.exists_forall_le' hφc (a := 0) (by
    rintro z ⟨-, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      have hz' : ρ ≤ ‖(0 : ℂ)‖ := hz
      rw [norm_zero] at hz'
      linarith
    by_contra hcon
    have hle : |aCoord H (u z) - aCoord H (u 0)| + ‖proj H (u z) - proj H (u 0)‖ ≤ 0 :=
      not_lt.mp hcon
    have ha := abs_nonneg (aCoord H (u z) - aCoord H (u 0))
    have hp := norm_nonneg (proj H (u z) - proj H (u 0))
    have ha0 : aCoord H (u z) = aCoord H (u 0) :=
      sub_eq_zero.mp (abs_eq_zero.mp (by linarith))
    have hp0 : proj H (u z) = proj H (u 0) :=
      sub_eq_zero.mp (norm_eq_zero.mp (by linarith))
    exact hz0 (hui (eq_of_aCoord_eq_of_proj_eq H hH (hu0 z) (hu0 0) ha0 hp0)))
  refine ⟨min 1 η₀, lt_min one_pos hη₀, fun z hz => ?_⟩
  by_cases hzR : R ≤ ‖z‖
  · have h5 := hfar z hzR
    have h6 := le_abs_self (aCoord H (u z) - aCoord H (u 0))
    have h7 := norm_nonneg (proj H (u z) - proj H (u 0))
    have h8 := min_le_left 1 η₀
    linarith
  · have hmem : z ∈ Metric.closedBall (0 : ℂ) R ∩ {z | ρ ≤ ‖z‖} :=
      ⟨by simpa using (not_le.mp hzR).le, hz⟩
    exact (min_le_right 1 η₀).trans (hη z hmem)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V n) (hu0 : ∀ z, u z ≠ 0)
    (huc : Continuous u) (hui : Function.Injective u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ η > 0, ∀ z, ρ ≤ ‖z‖ →
      η ≤ |aCoord H (u z) - aCoord H (u 0)| + ‖proj H (u z) - proj H (u 0)‖ :=
  exists_pos_le_aCoord_add_proj_of_isNondegenerateEnd_aux H hH P u hu0 huc hui huP ρ hρ
