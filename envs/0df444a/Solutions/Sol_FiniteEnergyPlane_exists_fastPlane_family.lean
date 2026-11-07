-- Prove2me | solution 1 for FiniteEnergyPlane.exists_fastPlane_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T10:51:28.126507+00:00
-- url     : https://prove2.me/submissions/e2de6a2c-44f7-41f8-b915-13075da1bd22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_shiftA
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
import Theorems.Thm_FiniteEnergyPlane_exists_fastPlane_slice_family
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_fastPlane_family_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ r > 0, ∃ f : ℂ × ℂ → V 1, ContDiffOn ℝ l f (Set.univ ×ˢ ball (0 : ℂ) r) ∧ Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p)) ∧
      (∀ z, f (z, 0) = u z) ∧
      (∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
        IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ))) ∧
      ∀ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) → ∃ τ : ℕ → ℂ, Tendsto τ atTop (𝓝 0) ∧
        ∀ᶠ k in atTop, τ k ∈ ball (0 : ℂ) r ∧
          Set.range (shiftA (c k) u) = Set.range (fun z => f (z, τ k)) := by
  obtain ⟨r, hr, g, hg, hg0, hfast, hinj, hder⟩ :=
    exists_fastPlane_slice_family H hH J hJ P hcz u hu huP hue l hl
  -- parameters in the ball have real and imaginary parts in the interval
  have hre : ∀ τ ∈ ball (0 : ℂ) r, τ.re ∈ Set.Ioo (-r) r ∧ τ.im ∈ Set.Ioo (-r) r := by
    intro τ hτ
    have hn : ‖τ‖ < r := by simpa using hτ
    have h1 := Complex.abs_re_le_norm τ
    have h2 := Complex.abs_im_le_norm τ
    exact ⟨abs_lt.1 (h1.trans_lt hn), abs_lt.1 (h2.trans_lt hn)⟩
  let imL : ℂ × ℂ →L[ℝ] ℂ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).prod (Complex.imCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ))
  let reL : ℂ × ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)
  let f : ℂ × ℂ → V 1 := fun p => Real.exp (2 * p.2.re) • g (p.1, p.2.im)
  have hT : IsOpen ((Set.univ : Set ℂ) ×ˢ Set.Ioo (-r) r) := isOpen_univ.prod isOpen_Ioo
  have hmaps : Set.MapsTo imL ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) r) ((Set.univ : Set ℂ) ×ˢ Set.Ioo (-r) r) := by
    rintro ⟨z, τ⟩ ⟨-, hτ⟩
    exact ⟨Set.mem_univ _, (hre τ hτ).2⟩
  refine ⟨r, hr, f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `C^l`
    have h1 : ContDiffOn ℝ l (fun p : ℂ × ℂ => g (imL p)) ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) r) :=
      hg.comp imL.contDiff.contDiffOn hmaps
    have h2 : ContDiff ℝ l (fun p : ℂ × ℂ => Real.exp (2 * p.2.re)) :=
      Real.contDiff_exp.comp (contDiff_const.mul reL.contDiff)
    exact h2.contDiffOn.smul h1
  · -- injectivity
    rintro ⟨z, τ⟩ ⟨-, hτ⟩ ⟨z', τ'⟩ ⟨-, hτ'⟩ h
    have hh : (fun q : ℂ × ℝ × ℝ => Real.exp (2 * q.2.1) • g (q.1, q.2.2)) (z, τ.re, τ.im) =
        (fun q : ℂ × ℝ × ℝ => Real.exp (2 * q.2.1) • g (q.1, q.2.2)) (z', τ'.re, τ'.im) := h
    have := hinj ⟨Set.mem_univ _, (hre τ hτ).1, (hre τ hτ).2⟩
      ⟨Set.mem_univ _, (hre τ' hτ').1, (hre τ' hτ').2⟩ hh
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, h1, h2⟩ := this
    have : τ = τ' := Complex.ext h1 h2
    rw [this]
  · -- injective derivative
    rintro ⟨z, τ⟩ ⟨-, hτ⟩
    have hmem : imL (z, τ) ∈ (Set.univ : Set ℂ) ×ˢ Set.Ioo (-r) r := hmaps ⟨Set.mem_univ _, hτ⟩
    have hgd : DifferentiableAt ℝ g (imL (z, τ)) :=
      ((hg _ hmem).contDiffAt (hT.mem_nhds hmem)).differentiableAt
        (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hl))
    have hγ : HasFDerivAt (fun p : ℂ × ℂ => g (imL p))
        ((fderiv ℝ g (imL (z, τ))).comp imL) (z, τ) :=
      hgd.hasFDerivAt.comp _ imL.hasFDerivAt
    have hφ : HasFDerivAt (fun p : ℂ × ℂ => Real.exp (2 * p.2.re))
        (Real.exp (2 * τ.re) • ((2 : ℝ) • reL)) (z, τ) := by
      have : HasFDerivAt (fun p : ℂ × ℂ => 2 * reL p) ((2 : ℝ) • reL) (z, τ) :=
        reL.hasFDerivAt.const_mul 2
      exact this.exp
    have hf := hφ.smul hγ
    have hfd : fderiv ℝ f (z, τ) = _ := hf.fderiv
    rw [hfd]
    refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨Δ, δ⟩ h0
    have hE := Real.exp_pos (2 * τ.re)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply] at h0
    have h1 : fderiv ℝ g (z, τ.im) (Δ, δ.im) + (2 * δ.re) • g (z, τ.im) = 0 := by
      have h2 : Real.exp (2 * τ.re) • (fderiv ℝ g (z, τ.im) (Δ, δ.im) +
          (2 * δ.re) • g (z, τ.im)) = 0 := by
        have e1 : imL (z, τ) = (z, τ.im) := rfl
        have e2 : imL (Δ, δ) = (Δ, δ.im) := rfl
        have e3 : reL (Δ, δ) = δ.re := rfl
        simp only [e1, e2, e3, smul_eq_mul] at h0
        rw [← h0, smul_add, smul_smul]
      exact (smul_eq_zero.1 h2).resolve_left hE.ne'
    obtain ⟨h3, h4, h5⟩ := hder z τ.im (hre τ hτ).2 Δ δ.im _ h1
    have h6 : δ.re = 0 := by linarith
    have : δ = 0 := Complex.ext h6 h4
    simp [h3, this]
  · -- central slice
    intro z
    simp [f, hg0]
  · -- slices
    intro τ hτ
    obtain ⟨h1, h2⟩ := hfast τ.im (hre τ hτ).2
    have hslice : (fun z => f (z, τ)) = shiftA τ.re (fun z => g (z, τ.im)) := rfl
    have h0 : ∀ z, g (z, τ.im) ≠ 0 := fun z => h1.1.2.1 z (Set.mem_univ z)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hslice]; exact isFastPlane_shiftA H hH J hJ _ h1 _
    · rw [hslice]; exact isNondegenerateEnd_shiftA H hH _ h0 cylInf P 1 h2 _
    · intro z z' h
      have hh : (fun q : ℂ × ℝ × ℝ => Real.exp (2 * q.2.1) • g (q.1, q.2.2)) (z, τ.re, τ.im) =
          (fun q : ℂ × ℝ × ℝ => Real.exp (2 * q.2.1) • g (q.1, q.2.2)) (z', τ.re, τ.im) := h
      have := hinj ⟨Set.mem_univ _, (hre τ hτ).1, (hre τ hτ).2⟩
        ⟨Set.mem_univ _, (hre τ hτ).1, (hre τ hτ).2⟩ hh
      exact (Prod.mk.inj this).1
    · intro z
      have hmem : (z, τ.im) ∈ (Set.univ : Set ℂ) ×ˢ Set.Ioo (-r) r :=
        ⟨Set.mem_univ _, (hre τ hτ).2⟩
      have hgd : DifferentiableAt ℝ g (z, τ.im) :=
        ((hg _ hmem).contDiffAt (hT.mem_nhds hmem)).differentiableAt
          (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hl))
      have hin : HasFDerivAt (fun w : ℂ => (w, τ.im))
          (ContinuousLinearMap.inl ℝ ℂ ℝ) z :=
        (hasFDerivAt_id z).prodMk (hasFDerivAt_const τ.im z)
      have hd : HasFDerivAt (fun w : ℂ => f (w, τ))
          (Real.exp (2 * τ.re) • (fderiv ℝ g (z, τ.im)).comp (ContinuousLinearMap.inl ℝ ℂ ℝ)) z :=
        by
          have h := (hgd.hasFDerivAt.comp z hin).const_smul (Real.exp (2 * τ.re))
          exact h
      rw [hd.fderiv]
      refine (injective_iff_map_eq_zero _).2 ?_
      intro Δ h0'
      have hE := Real.exp_pos (2 * τ.re)
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply] at h0'
      have h3 := (smul_eq_zero.1 h0').resolve_left hE.ne'
      exact (hder z τ.im (hre τ hτ).2 Δ 0 0 (by simpa using h3)).1
  · -- the translations are slices
    intro c hc
    refine ⟨fun k => (c k : ℂ), ?_, ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).comp hc
      simpa [Function.comp_def] using this
    · have hsmall : ∀ᶠ k in atTop, |c k| < r := by
        have := (hc.abs).eventually (gt_mem_nhds (by simpa using hr : |(0 : ℝ)| < r))
        exact this
      filter_upwards [hsmall] with k hk
      refine ⟨by simpa using hk, ?_⟩
      have : shiftA (c k) u = fun z => f (z, (c k : ℂ)) := by
        funext z
        simp [shiftA, f, hg0]
      rw [this]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ r > 0, ∃ f : ℂ × ℂ → V 1, ContDiffOn ℝ l f (Set.univ ×ˢ ball (0 : ℂ) r) ∧ Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p)) ∧
      (∀ z, f (z, 0) = u z) ∧
      (∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
        IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ))) ∧
      ∀ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) → ∃ τ : ℕ → ℂ, Tendsto τ atTop (𝓝 0) ∧
        ∀ᶠ k in atTop, τ k ∈ ball (0 : ℂ) r ∧
          Set.range (shiftA (c k) u) = Set.range (fun z => f (z, τ k)) :=
  exists_fastPlane_family_aux H hH J hJ P hcz u hu huP hue l hl
