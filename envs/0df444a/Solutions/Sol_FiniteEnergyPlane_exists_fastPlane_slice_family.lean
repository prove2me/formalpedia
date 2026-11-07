-- Prove2me | solution 1 for FiniteEnergyPlane.exists_fastPlane_slice_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T11:27:23.361085+00:00
-- url     : https://prove2.me/submissions/2e948f0a-cfb6-4e41-af3a-8f97b4f8db12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_shiftA
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
import Theorems.Thm_FiniteEnergyPlane_exists_fastPlane_close_family
import Theorems.Thm_FiniteEnergyPlane_range_eq_or_disjoint_of_isCylCloseTo
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The scale `e^{2c}` adds `c` to `aCoord` and leaves `proj` unchanged. -/
theorem fs_proj_aCoord_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) (c : ℝ) :
    proj H (Real.exp (2 * c) • y) = proj H y ∧
      aCoord H (Real.exp (2 * c) • y) = aCoord H y + c := by
  have hc0 := Real.exp_pos (2 * c)
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 y hy
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := ⟨r, hr0, hr1⟩
  have e2 : ∃ r : ℝ, 0 < r ∧ H (r • (Real.exp (2 * c) • y)) = 1 :=
    ⟨r / Real.exp (2 * c), div_pos hr0 hc0, by rw [smul_smul, div_mul_cancel₀ _ hc0.ne']; exact hr1⟩
  have h1 : scaleToS H y = r := by
    unfold scaleToS
    rw [dif_pos e1]
    exact hru _ (Classical.choose_spec e1)
  have h2 : scaleToS H (Real.exp (2 * c) • y) = r / Real.exp (2 * c) := by
    unfold scaleToS
    rw [dif_pos e2]
    have hs2 := Classical.choose_spec e2
    have := hru (Classical.choose e2 * Real.exp (2 * c))
      ⟨mul_pos hs2.1 hc0, by rw [← smul_smul]; exact hs2.2⟩
    rw [← this, mul_div_cancel_right₀ _ hc0.ne']
  refine ⟨?_, ?_⟩
  · unfold proj
    rw [h1, h2, smul_smul, div_mul_cancel₀ _ hc0.ne']
  · unfold aCoord
    rw [h1, h2, Real.log_div hr0.ne' hc0.ne', Real.log_exp]
    ring

/-- Translates of a plane stay close by the size of the translation. -/
theorem fs_isCylCloseTo_shiftA (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (ε c : ℝ) (hc : |c| ≤ ε) (f u : ℂ → V 1) (hf : ∀ z, f z ≠ 0)
    (hclose : IsCylCloseTo H ε f u) :
    IsCylCloseTo H (2 * ε) (shiftA c f) u := by
  have hp : (fun w => proj H (shiftA c f w)) = fun w => proj H (f w) := by
    funext w; exact (fs_proj_aCoord_smul H hH (f w) (hf w) c).1
  have ha : (fun w => aCoord H (shiftA c f w)) = fun w => aCoord H (f w) + c := by
    funext w; exact (fs_proj_aCoord_smul H hH (f w) (hf w) c).2
  intro z
  obtain ⟨h1, h2, h3⟩ := hclose z
  have hε : 0 ≤ ε := (abs_nonneg c).trans hc
  refine ⟨?_, ?_, ?_⟩
  · have : aCoord H (shiftA c f z) = aCoord H (f z) + c := congrFun ha z
    rw [this]
    have e : aCoord H (f z) + c - aCoord H (u z) = (aCoord H (f z) - aCoord H (u z)) + c := by ring
    rw [e]
    linarith [abs_add_le (aCoord H (f z) - aCoord H (u z)) c]
  · have : proj H (shiftA c f z) = proj H (f z) := congrFun hp z
    rw [this]
    linarith
  · rw [hp, ha, fderiv_add_const]
    linarith

theorem exists_fastPlane_slice_family_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r, IsFastPlane H J (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1) ∧
      Set.InjOn (fun q : ℂ × ℝ × ℝ => Real.exp (2 * q.2.1) • g (q.1, q.2.2))
        (Set.univ ×ˢ (Set.Ioo (-r) r ×ˢ Set.Ioo (-r) r)) ∧
      ∀ z, ∀ t ∈ Set.Ioo (-r) r, ∀ (Δ : ℂ) (δt lam : ℝ),
        fderiv ℝ g (z, t) (Δ, δt) + lam • g (z, t) = 0 → Δ = 0 ∧ δt = 0 ∧ lam = 0 := by
  obtain ⟨ε, hε, hdisj⟩ := range_eq_or_disjoint_of_isCylCloseTo H hH J hJ P hcz u hu huP hue
  obtain ⟨r₁, hr₁, g, hg, hg0, hmem, hdist, hder⟩ :=
    exists_fastPlane_close_family H hH J hJ P hcz u hu huP hue l hl (ε / 2) (by positivity)
  set r := min r₁ (ε / 2) with hr_def
  have hr : 0 < r := lt_min hr₁ (by positivity)
  have hsub : Set.Ioo (-r) r ⊆ Set.Ioo (-r₁) r₁ := by
    intro x hx
    have h := min_le_left r₁ (ε / 2)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsmall : ∀ c ∈ Set.Ioo (-r) r, |c| ≤ ε / 2 := by
    intro c hc
    have h := min_le_right r₁ (ε / 2)
    exact abs_le.2 ⟨by linarith [hc.1], by linarith [hc.2]⟩
  refine ⟨r, hr, g, hg.mono (Set.prod_mono subset_rfl hsub), hg0,
    fun t ht => ⟨(hmem t (hsub ht)).1, (hmem t (hsub ht)).2.1⟩, ?_,
    fun z t ht => hder z t (hsub ht)⟩
  rintro ⟨z, c, t⟩ ⟨-, hc, ht⟩ ⟨z', c', t'⟩ ⟨-, hc', ht'⟩ h
  simp only at hc ht hc' ht' h
  obtain ⟨hf, hn, he, hcl⟩ := hmem t (hsub ht)
  obtain ⟨hf', hn', he', hcl'⟩ := hmem t' (hsub ht')
  have h0 : ∀ z, g (z, t) ≠ 0 := fun z => hf.1.2.1 z (Set.mem_univ z)
  have h0' : ∀ z, g (z, t') ≠ 0 := fun z => hf'.1.2.1 z (Set.mem_univ z)
  have htwo : 2 * (ε / 2) = ε := by ring
  have hc1 := fs_isCylCloseTo_shiftA H hH (ε / 2) c (hsmall c hc) _ u h0 hcl
  have hc2 := fs_isCylCloseTo_shiftA H hH (ε / 2) c' (hsmall c' hc') _ u h0' hcl'
  rw [htwo] at hc1 hc2
  have hpt : shiftA c (fun z => g (z, t)) z = shiftA c' (fun z => g (z, t')) z' := h
  rcases hdisj _ _ (isFastPlane_shiftA H hH J hJ _ hf c)
      (isNondegenerateEnd_shiftA H hH _ h0 cylInf P 1 hn c) hc1
      (isFastPlane_shiftA H hH J hJ _ hf' c')
      (isNondegenerateEnd_shiftA H hH _ h0' cylInf P 1 hn' c') hc2 with hrange | hd
  · obtain ⟨rfl, rfl⟩ := hdist c (hsub hc) t (hsub ht) c' (hsub hc') t' (hsub ht') hrange
    have hE := Real.exp_pos (2 * c)
    have : g (z, t) = g (z', t) := smul_right_injective _ hE.ne' hpt
    have hzz : z = z' := he.1 this
    rw [hzz]
  · exact absurd (⟨z', hpt.symm⟩ : shiftA c (fun z => g (z, t)) z ∈
      Set.range (shiftA c' (fun z => g (z, t')))) (Set.disjoint_left.1 hd ⟨z, rfl⟩)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r, IsFastPlane H J (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1) ∧
      Set.InjOn (fun q : ℂ × ℝ × ℝ => Real.exp (2 * q.2.1) • g (q.1, q.2.2))
        (Set.univ ×ˢ (Set.Ioo (-r) r ×ˢ Set.Ioo (-r) r)) ∧
      ∀ z, ∀ t ∈ Set.Ioo (-r) r, ∀ (Δ : ℂ) (δt lam : ℝ),
        fderiv ℝ g (z, t) (Δ, δt) + lam • g (z, t) = 0 → Δ = 0 ∧ δt = 0 ∧ lam = 0 :=
  exists_fastPlane_slice_family_aux H hH J hJ P hcz u hu huP hue l hl
