-- Prove2me | solution 1 for FiniteEnergyPlane.isFastPlane_shiftA
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T10:49:44.069021+00:00
-- url     : https://prove2.me/submissions/ab865ffe-5c2b-41f9-a45f-db52f1fbcff9

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Radial scaling in the symplectization: `proj` is invariant and `a` shifts by `log c / 2`. -/
theorem ff_proj_aCoord_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (c : ℝ) (hc : 0 < c) (y : V n) (hy : y ≠ 0) :
    proj H (c • y) = proj H y ∧ aCoord H (c • y) = aCoord H y + Real.log c / 2 := by
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 y hy
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := ⟨r, hr0, hr1⟩
  have e2 : ∃ r : ℝ, 0 < r ∧ H (r • (c • y)) = 1 :=
    ⟨r / c, div_pos hr0 hc, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']; exact hr1⟩
  have h1 : scaleToS H y = r := by
    unfold scaleToS
    rw [dif_pos e1]
    exact hru _ (Classical.choose_spec e1)
  have h2 : scaleToS H (c • y) = r / c := by
    unfold scaleToS
    rw [dif_pos e2]
    have hs2 := Classical.choose_spec e2
    have := hru (Classical.choose e2 * c) ⟨mul_pos hs2.1 hc, by rw [← smul_smul]; exact hs2.2⟩
    rw [← this, mul_div_cancel_right₀ _ hc.ne']
  refine ⟨?_, ?_⟩
  · unfold proj
    rw [h1, h2, smul_smul, div_mul_cancel₀ _ hc.ne']
  · unfold aCoord
    rw [h1, h2, Real.log_div hr0.ne' hc.ne']
    ring

theorem isNondegenerateEnd_shiftA_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u : ℂ → V n) (hu : ∀ z, u z ≠ 0) (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε : ℝ)
    (h : IsNondegenerateEnd H u e P ε) (c : ℝ) :
    IsNondegenerateEnd H (shiftA c u) e P ε := by
  obtain ⟨d, c', b, hb, h1, h2⟩ := h
  have hexp := Real.exp_pos (2 * c)
  have hs : ∀ z, proj H (shiftA c u z) = proj H (u z) ∧
      aCoord H (shiftA c u z) = aCoord H (u z) + c := by
    intro z
    have := ff_proj_aCoord_smul H hH _ hexp (u z) (hu z)
    refine ⟨this.1, ?_⟩
    have h3 := this.2
    rw [Real.log_exp] at h3
    simpa [shiftA, mul_div_assoc] using h3
  refine ⟨d + c, c', b, hb, ?_, ?_⟩
  · convert h1 using 2 with p
    simp only [endA, (hs _).2]
    ring
  · convert h2 using 3 with p
    simp only [endW, (hs _).1]

theorem isFastPlane_shiftA_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (c : ℝ) : IsFastPlane H J (shiftA c u) := by
  obtain ⟨hfe, ⟨P, hP, hnd⟩, hwind⟩ := hu
  have hexp := Real.exp_pos (2 * c)
  have h0 : ∀ z, u z ≠ 0 := fun z => hfe.2.1 z (Set.mem_univ z)
  refine ⟨?_, ⟨P, hP, isNondegenerateEnd_shiftA_aux H hH u h0 cylInf P 1 hnd c⟩, ?_⟩
  · have := (rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ u hfe 0 1 one_pos _ hexp).1
    have e : shiftA c u = fun w => Real.exp (2 * c) • u w := rfl
    rw [e]
    simpa using this
  · have hpi : piDs H (shiftA c u) = piDs H u := by
      have hw : (fun z => proj H (shiftA c u z)) = fun z => proj H (u z) := by
        funext z
        exact (ff_proj_aCoord_smul H hH _ hexp (u z) (h0 z)).1
      funext z
      have hw' : proj H (shiftA c u z) = proj H (u z) := congrFun hw z
      simp only [piDs, hw, hw']
    simpa only [HasWindPi, hpi] using hwind

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (c : ℝ) : IsFastPlane H J (shiftA c u) :=
  isFastPlane_shiftA_aux H hH J hJ u hu c
