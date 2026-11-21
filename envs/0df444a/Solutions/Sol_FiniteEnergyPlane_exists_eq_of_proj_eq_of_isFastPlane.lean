-- Prove2me | solution 1 for FiniteEnergyPlane.exists_eq_of_proj_eq_of_isFastPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T21:15:33.093803+00:00
-- url     : https://prove2.me/submissions/58f150a5-af94-4c04-a766-9e4d08119638

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_exists_eq_of_endW_eq_of_hasAsymptoticEigenvector
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj



/-! Glue for F `exists_eq_of_proj_eq_of_isFastPlane` (Hryniewicz (100)). -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma pef_cylInf_rep (z : ℂ) (hz : z ≠ 0) :
    ∃ t : ℝ, cylInf (Real.log ‖z‖ / (2 * π)) t = z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hexp : Real.exp (2 * π * (Real.log ‖z‖ / (2 * π))) = ‖z‖ := by
    rw [mul_div_cancel₀ _ h2pi.ne', Real.exp_log hzpos]
  refine ⟨Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [hexp]
  have e : ((2 * π * (Complex.arg z / (2 * π)) : ℝ) : ℂ) = (Complex.arg z : ℂ) := by
    congr 1
    field_simp
  rw [e]
  exact Complex.norm_mul_exp_arg_mul_I z

theorem exists_eq_of_proj_eq_of_isFastPlane_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hmiss : ∀ z, proj H (u z) ∉ Set.range P.x) :
    ∃ R : ℝ, ∀ z z' : ℂ, R ≤ ‖z‖ → proj H (u z) = proj H (u z') → z = z' := by
  have hP := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP
  obtain ⟨μ, v, hv⟩ :=
    exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd H hH J hJ P u hu.1 huP
  obtain ⟨S, hS⟩ := exists_eq_of_endW_eq_of_hasAsymptoticEigenvector H hH J hJ P hP u huP μ v hv
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  set R₂ := Real.exp (2 * π * S) with hR₂
  have hR₂pos : 0 < R₂ := Real.exp_pos _
  have hu0 : ∀ z, u z ≠ 0 := fun z => hu.1.2.1 z (Set.mem_univ z)
  have hucont : Continuous u := (contDiffOn_univ.1 hu.1.1).continuous
  have hpc : Continuous fun z => proj H (u z) :=
    continuous_iff_continuousAt.2 fun z =>
      ((contDiffAt_aCoord_proj H hH (u z) (hu0 z)).2.continuousAt).comp hucont.continuousAt
  have hxc : Continuous P.x := continuous_iff_continuousAt.2 fun τ => (P.hasDerivAt τ).continuousAt
  have hrange : IsCompact (Set.range P.x) := by
    have : Set.range P.x = P.x '' Set.Icc 0 P.T := by
      ext y
      constructor
      · rintro ⟨τ, rfl⟩
        obtain ⟨σ, hσ, hfσ⟩ := (show Function.Periodic P.x P.T from P.periodic).exists_mem_Ico₀
          P.T_pos τ
        exact ⟨σ, Set.Ico_subset_Icc_self hσ, hfσ.symm⟩
      · rintro ⟨σ, -, rfl⟩; exact ⟨σ, rfl⟩
    rw [this]; exact isCompact_Icc.image hxc
  have hne : (Set.range P.x).Nonempty := ⟨P.x 0, 0, rfl⟩
  have hfpos : ∀ z, 0 < infDist (proj H (u z)) (Set.range P.x) := fun z =>
    (hrange.isClosed.notMem_iff_infDist_pos hne).1 (hmiss z)
  obtain ⟨z₀, -, hz₀⟩ := (isCompact_closedBall (0 : ℂ) R₂).exists_isMinOn
    ⟨0, mem_closedBall_self hR₂pos.le⟩
    ((continuous_infDist_pt (Set.range P.x)).comp hpc).continuousOn
  set d₀ := infDist (proj H (u z₀)) (Set.range P.x) with hd₀
  have hd₀pos : 0 < d₀ := hfpos z₀
  obtain ⟨d, c₁, b, hb, -, hw⟩ := huP
  obtain ⟨s₂, hs₂⟩ := hw (d₀ / 2) (by positivity)
  refine ⟨max (max R₂ (Real.exp (2 * π * max s₂ 0))) 1, fun z z' hz hzz' => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hlog : ∀ (w : ℂ) (A : ℝ), 0 < ‖w‖ → Real.exp (2 * π * A) ≤ ‖w‖ →
      A ≤ Real.log ‖w‖ / (2 * π) := by
    intro w A hw hA
    rw [le_div_iff₀ h2pi, mul_comm]
    exact (Real.le_log_iff_exp_le hw).2 hA
  obtain ⟨t, ht⟩ := pef_cylInf_rep z hz0
  set s := Real.log ‖z‖ / (2 * π) with hs
  have hsS : S ≤ s := hlog z S hzpos (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hz))
  have hs2 : max s₂ 0 ≤ s :=
    hlog z _ hzpos (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hz))
  have hclose : infDist (proj H (u z)) (Set.range P.x) ≤ d₀ / 2 := by
    have h1 := hs₂ s (le_trans (le_max_left _ _) hs2) t
    have hexp : 1 ≤ Real.exp (b * s) :=
      Real.one_le_exp (mul_nonneg hb.le (le_trans (le_max_right _ _) hs2))
    simp only at h1
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    calc infDist (proj H (u z)) (Set.range P.x)
        ≤ dist (proj H (u z)) (P.x (1 * P.T * t + c₁)) := infDist_le_dist_of_mem ⟨_, rfl⟩
      _ = ‖endW H u cylInf (s, t) - P.x (1 * P.T * t + c₁)‖ := by
          rw [dist_eq_norm]; simp only [endW, ht]
      _ ≤ Real.exp (b * s) * ‖endW H u cylInf (s, t) - P.x (1 * P.T * t + c₁)‖ :=
          le_mul_of_one_le_left (norm_nonneg _) hexp
      _ ≤ d₀ / 2 := h1
  by_cases hz' : ‖z'‖ ≤ R₂
  · exfalso
    have hmin : d₀ ≤ infDist (proj H (u z')) (Set.range P.x) :=
      hz₀ (mem_closedBall_zero_iff.2 hz')
    rw [← hzz'] at hmin
    linarith
  · push_neg at hz'
    have hz'pos : 0 < ‖z'‖ := lt_trans hR₂pos hz'
    obtain ⟨t', ht'⟩ := pef_cylInf_rep z' (norm_pos_iff.1 hz'pos)
    have hs' : S ≤ Real.log ‖z'‖ / (2 * π) := hlog z' S hz'pos hz'.le
    have := hS s _ t t' hsS hs' (by simp only [endW, ht, ht']; exact hzz')
    rw [ht, ht'] at this
    exact this

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hmiss : ∀ z, proj H (u z) ∉ Set.range P.x) :
    ∃ R : ℝ, ∀ z z' : ℂ, R ≤ ‖z‖ → proj H (u z) = proj H (u z') → z = z' :=
  exists_eq_of_proj_eq_of_isFastPlane_aux H hH J hJ P u hu huP hmiss
