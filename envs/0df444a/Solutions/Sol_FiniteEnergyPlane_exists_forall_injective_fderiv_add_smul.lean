-- Prove2me | solution 1 for FiniteEnergyPlane.exists_forall_injective_fderiv_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-08T22:44:39.434537+00:00
-- url     : https://prove2.me/submissions/767d37a0-ce7e-4554-88a9-1f48a30c492f

import Mathlib



namespace FiniteEnergyPlane

open Topology

theorem exists_forall_injective_fderiv_add_smul_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) (hr : 0 < r) (g : ℂ × ℝ → E)
    (hg : ContDiffOn ℝ 1 g (Set.univ ×ˢ Set.Ioo (-r) r)) (z₀ : ℂ)
    (h0 : ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (z₀, 0) (Δ, δt) + lam • g (z₀, 0) = 0 →
      Δ = 0 ∧ δt = 0 ∧ lam = 0) :
    ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ (Δ : ℂ) (δt lam : ℝ),
      fderiv ℝ g (z₀, t) (Δ, δt) + lam • g (z₀, t) = 0 → Δ = 0 ∧ δt = 0 ∧ lam = 0 := by
  set A : ℂ × ℝ × ℝ →L[ℝ] ℂ × ℝ := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ))) with hA
  set B : ℂ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ)) with hB
  set T : ℝ → (ℂ × ℝ × ℝ →L[ℝ] E) := fun t =>
    (fderiv ℝ g (z₀, t)).comp A + B.smulRight (g (z₀, t)) with hT
  have hTapp : ∀ t (x : ℂ × ℝ × ℝ), T t x = fderiv ℝ g (z₀, t) (x.1, x.2.1) + x.2.2 • g (z₀, t) := by
    intro t x
    simp [hT, hA, hB]
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo (-r) r : Set (ℂ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hemb : Continuous (fun t : ℝ => ((z₀, t) : ℂ × ℝ)) := continuous_const.prodMk continuous_id
  have hmaps : Set.MapsTo (fun t : ℝ => ((z₀, t) : ℂ × ℝ)) (Set.Ioo (-r) r)
      (Set.univ ×ˢ Set.Ioo (-r) r) := fun t ht => ⟨Set.mem_univ _, ht⟩
  have hDc : ContinuousOn (fun t : ℝ => fderiv ℝ g (z₀, t)) (Set.Ioo (-r) r) :=
    (hg.continuousOn_fderiv_of_isOpen hopen le_rfl).comp hemb.continuousOn hmaps
  have hgc : ContinuousOn (fun t : ℝ => g (z₀, t)) (Set.Ioo (-r) r) :=
    hg.continuousOn.comp hemb.continuousOn hmaps
  have hTc : ContinuousOn T (Set.Ioo (-r) r) := by
    have h1 : ContinuousOn (fun t => (fderiv ℝ g (z₀, t)).comp A) (Set.Ioo (-r) r) :=
      ((ContinuousLinearMap.compL ℝ (ℂ × ℝ × ℝ) (ℂ × ℝ) E).flip A).continuous.comp_continuousOn hDc
    have h2 : ContinuousOn (fun t => B.smulRight (g (z₀, t))) (Set.Ioo (-r) r) :=
      (ContinuousLinearMap.smulRightL ℝ (ℂ × ℝ × ℝ) E B).continuous.comp_continuousOn hgc
    exact h1.add h2
  have hT0 : Function.Injective (T 0) := by
    refine (injective_iff_map_eq_zero (T 0)).mpr ?_
    intro x hx
    have hx' : fderiv ℝ g (z₀, 0) (x.1, x.2.1) + x.2.2 • g (z₀, 0) = 0 := by
      rw [← hTapp]; exact hx
    obtain ⟨h1, h2, h3⟩ := h0 x.1 x.2.1 x.2.2 hx'
    ext <;> simp [h1, h2, h3]
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  have hnhds : T ⁻¹' {L | Function.Injective L} ∈ 𝓝 (0 : ℝ) := by
    have := (hTc.continuousAt (isOpen_Ioo.mem_nhds hmem0)).preimage_mem_nhds
      (ContinuousLinearMap.isOpen_injective.mem_nhds hT0)
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨min ε r, ⟨lt_min hε hr, min_le_right _ _⟩, ?_⟩
  intro t ht Δ δt lam h
  have htb : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1, min_le_left ε r], by linarith [ht.2, min_le_left ε r]⟩
  have hinj : Function.Injective (T t) := hball htb
  have hz : T t (Δ, δt, lam) = T t 0 := by
    rw [hTapp, map_zero]; exact h
  have := hinj hz
  simp only [Prod.mk_eq_zero] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open Topology

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) (hr : 0 < r) (g : ℂ × ℝ → E)
    (hg : ContDiffOn ℝ 1 g (Set.univ ×ˢ Set.Ioo (-r) r)) (z₀ : ℂ)
    (h0 : ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (z₀, 0) (Δ, δt) + lam • g (z₀, 0) = 0 →
      Δ = 0 ∧ δt = 0 ∧ lam = 0) :
    ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ (Δ : ℂ) (δt lam : ℝ),
      fderiv ℝ g (z₀, t) (Δ, δt) + lam • g (z₀, t) = 0 → Δ = 0 ∧ δt = 0 ∧ lam = 0 :=
  exists_forall_injective_fderiv_add_smul_aux r hr g hg z₀ h0
