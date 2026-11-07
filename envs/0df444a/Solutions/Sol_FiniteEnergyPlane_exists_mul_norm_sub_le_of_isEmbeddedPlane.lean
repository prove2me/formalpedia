-- Prove2me | solution 1 for FiniteEnergyPlane.exists_mul_norm_sub_le_of_isEmbeddedPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T16:48:58.34638+00:00
-- url     : https://prove2.me/submissions/2666718f-7201-473c-92c6-530e132bd6df

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_eq_of_aCoord_eq_of_proj_eq
import Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_sub_le_of_isCompact_pairs
import Theorems.Thm_FiniteEnergyPlane_exists_mul_abs_sub_le_norm_sub_of_isPrime
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_aCoord_proj_comp_iff
import Theorems.Thm_FiniteEnergyPlane_exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_sub_le_of_hasExpAsymptoticsEnd



namespace FiniteEnergyPlane

open scoped Real

theorem emb_exists_cylInf_eq (z : ℂ) (hz : z ≠ 0) :
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

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem emb_aCoord_large {n : ℕ} (H : V n → ℝ) (P : ReebOrbit H) (u : ℂ → V n)
    (huP : IsNondegenerateEnd H u cylInf P 1) (M : ℝ) :
    ∃ R > 0, ∀ z : ℂ, R ≤ ‖z‖ → M ≤ aCoord H (u z) := by
  obtain ⟨d, c, b, -, h1, -⟩ := huP
  obtain ⟨s₀, hs₀⟩ := h1 1 one_pos
  have hT := P.T_pos
  set s₁ : ℝ := max s₀ ((M + 1 - d) / P.T) with hs₁
  have hs₁a : s₀ ≤ s₁ := le_max_left _ _
  have hs₁b : M + 1 - d ≤ P.T * s₁ := by
    have := le_max_right s₀ ((M + 1 - d) / P.T)
    rw [← hs₁, div_le_iff₀ hT] at this
    linarith
  refine ⟨Real.exp (2 * π * s₁), Real.exp_pos _, fun z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := (Real.exp_pos _).trans_le hz
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨t, ht⟩ := emb_exists_cylInf_eq z (norm_pos_iff.1 hzpos)
  set s : ℝ := Real.log ‖z‖ / (2 * π) with hs
  have hss : s₁ ≤ s := by
    rw [hs, le_div_iff₀ h2pi, Real.le_log_iff_exp_le hzpos, mul_comm]; exact hz
  have := hs₀ s (hs₁a.trans hss) t
  simp only [endA, ht, Real.norm_eq_abs, one_mul] at this
  have h3 := (abs_le.mp this).1
  have h4 : P.T * s₁ ≤ P.T * s := mul_le_mul_of_nonneg_left hss hT.le
  linarith

/-- An embedded fast plane asymptotic to `P` at `∞` satisfies a global lower Lipschitz bound in its
symplectization coordinates, in the scale `1 + ‖z‖ + ‖z'‖`. -/
theorem exists_mul_norm_sub_le_of_isEmbeddedPlane_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u) :
    ∃ c > 0, ∀ z z' : ℂ, c * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) *
      (|aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖) := by
  have hfe := hu.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfe.2.1 z (Set.mem_univ z)
  have hus : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfe.1
  have hprime := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP
  obtain ⟨b, hb, hexp⟩ := exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd H hH J hJ u hfe P huP
  obtain ⟨c₀, hc₀, hsep⟩ := exists_mul_abs_sub_le_norm_sub_of_isPrime H hH P hprime
  obtain ⟨c₁, hc₁, R, hR, hfar⟩ :=
    exists_mul_norm_sub_le_of_hasExpAsymptoticsEnd H u P b hb hexp c₀ hc₀ hsep
  -- the coordinates as a `C¹` map
  set G : ℂ → ℝ × V 1 := fun w => (aCoord H (u w), proj H (u w)) with hG
  have hGc : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro z
    obtain ⟨ha, hp⟩ := contDiffAt_aCoord_proj H hH (u z) (hu0 z)
    have hu1 : ContDiffAt ℝ 1 u z := (hus.of_le (by exact_mod_cast le_top)).contDiffAt
    exact (ContDiffAt.comp z (ha.of_le (by exact_mod_cast le_top)) hu1).prodMk
      (ContDiffAt.comp z (hp.of_le (by exact_mod_cast le_top)) hu1)
  -- bound on the ball of radius `R`
  have haC : Continuous fun z => aCoord H (u z) := by
    have : (fun z => aCoord H (u z)) = fun z => (G z).1 := rfl
    rw [this]
    exact continuous_fst.comp hGc.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image haC.continuousOn
  obtain ⟨R₀, hR₀, hlarge⟩ := emb_aCoord_large H P u huP (M + 1)
  set R' : ℝ := max R R₀ with hR'
  have hRR' : R ≤ R' := le_max_left _ _
  have hlarge' : ∀ z : ℂ, R' ≤ ‖z‖ → M + 1 ≤ aCoord H (u z) := fun z hz =>
    hlarge z ((le_max_right _ _).trans hz)
  -- the compact part
  obtain ⟨c₂, hc₂, hcpt⟩ := exists_mul_norm_sub_le_of_isCompact_pairs G hGc
    (closedBall (0 : ℂ) R' ×ˢ closedBall (0 : ℂ) R')
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    (fun p _ hne heq => hne (hue.1 (eq_of_aCoord_eq_of_proj_eq H hH (hu0 _) (hu0 _)
      (congrArg Prod.fst heq) (congrArg Prod.snd heq))))
    (fun p _ _ => (injective_fderiv_aCoord_proj_comp_iff H hH u p.1
      (hus.differentiable (by simp) _) (hu0 _)).2 (hue.2 _))
  refine ⟨min c₁ (min c₂ 1), lt_min hc₁ (lt_min hc₂ one_pos), fun z z' => ?_⟩
  set Sc : ℝ := 1 + ‖z‖ + ‖z'‖ with hSc
  have hSc1 : 1 ≤ Sc := by rw [hSc]; linarith [norm_nonneg z, norm_nonneg z']
  set Δ : ℝ := |aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖ with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hzz : 0 ≤ ‖z - z'‖ := norm_nonneg _
  by_cases hcase1 : ‖z‖ ≤ R' ∧ ‖z'‖ ≤ R'
  · have h := hcpt (z, z') ⟨mem_closedBall_zero_iff.2 hcase1.1, mem_closedBall_zero_iff.2 hcase1.2⟩
    have hnorm : ‖G z - G z'‖ ≤ Δ := by
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · simp only [hG, Prod.fst_sub, Real.norm_eq_abs]
        have := norm_nonneg (proj H (u z) - proj H (u z'))
        rw [hΔ]; linarith
      · simp only [hG, Prod.snd_sub]
        have := abs_nonneg (aCoord H (u z) - aCoord H (u z'))
        rw [hΔ]; linarith
    calc min c₁ (min c₂ 1) * ‖z - z'‖ ≤ c₂ * ‖z - z'‖ := by
          gcongr
          exact (min_le_right _ _).trans (min_le_left _ _)
      _ ≤ Δ := h.trans hnorm
      _ ≤ Sc * Δ := by nlinarith
  by_cases hcase2 : R ≤ ‖z‖ ∧ R ≤ ‖z'‖
  · calc min c₁ (min c₂ 1) * ‖z - z'‖ ≤ c₁ * ‖z - z'‖ := by
          gcongr
          exact min_le_left _ _
      _ ≤ Sc * Δ := hfar z z' hcase2.1 hcase2.2
  -- mixed pairs
  have hsplit : 1 ≤ Δ := by
    have hsmall : ∀ w w' : ℂ, ‖w‖ < R → R' < ‖w'‖ → 1 ≤ aCoord H (u w') - aCoord H (u w) := by
      intro w w' hw hw'
      have h1 : aCoord H (u w) ≤ M :=
        hM ⟨w, mem_closedBall_zero_iff.2 hw.le, rfl⟩
      have h2 := hlarge' w' hw'.le
      linarith
    have hn := norm_nonneg (proj H (u z) - proj H (u z'))
    rw [hΔ]
    by_cases hzR : ‖z‖ < R
    · have hz' : R' < ‖z'‖ := by
        by_contra hcon
        exact hcase1 ⟨hzR.le.trans hRR', not_lt.1 hcon⟩
      have := hsmall z z' hzR hz'
      have h3 := neg_abs_le (aCoord H (u z) - aCoord H (u z'))
      linarith
    · have hz'R : ‖z'‖ < R := by
        by_contra hcon
        exact hcase2 ⟨not_lt.1 hzR, not_lt.1 hcon⟩
      have hz : R' < ‖z‖ := by
        by_contra hcon
        exact hcase1 ⟨not_lt.1 hcon, hz'R.le.trans hRR'⟩
      have := hsmall z' z hz'R hz
      have h3 := le_abs_self (aCoord H (u z) - aCoord H (u z'))
      linarith
  have hz1 : ‖z - z'‖ ≤ Sc := by
    have := norm_sub_le z z'
    rw [hSc]; linarith
  calc min c₁ (min c₂ 1) * ‖z - z'‖ ≤ 1 * ‖z - z'‖ := by
        gcongr
        exact (min_le_right _ _).trans (min_le_right _ _)
    _ ≤ Sc * 1 := by linarith
    _ ≤ Sc * Δ := by gcongr

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u) :
    ∃ c > 0, ∀ z z' : ℂ, c * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) *
      (|aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖) :=
  exists_mul_norm_sub_le_of_isEmbeddedPlane_aux H hH J hJ P u hu huP hue
