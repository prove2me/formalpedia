-- Prove2me | solution 1 for FiniteEnergyPlane.contDiffOn_of_apply_eq_of_injective_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T11:39:10.70964+00:00
-- url     : https://prove2.me/submissions/07a163e3-c5ea-4e3e-b123-74a727231afc

import Mathlib



/-! A solution `ρ` of `F (t, ρ t) = g t` is as regular as `F` and `g`, when the partial
derivatives `∂_w F (t, ·)` at `ρ t` are injective and `ρ` is continuous. -/

namespace FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

theorem contDiffOn_of_apply_eq_of_injective_fderiv_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {l : ℕ} (hl : 1 ≤ l) {S : Set ℝ} (hS : IsOpen S)
    {F : ℝ × ℂ → E} {g : ℝ → E} {ρ : ℝ → ℂ}
    (hF : ContDiffOn ℝ l F (S ×ˢ Set.univ)) (hg : ContDiffOn ℝ l g S) (hρ : ContinuousOn ρ S)
    (heq : ∀ t ∈ S, F (t, ρ t) = g t)
    (hinj : ∀ t ∈ S, Function.Injective (fderiv ℝ (fun w => F (t, w)) (ρ t))) :
    ContDiffOn ℝ l ρ S := by
  intro t₀ ht₀
  apply ContDiffAt.contDiffWithinAt
  set u : ℝ × ℂ := (t₀, ρ t₀) with hu
  have hSn : S ∈ 𝓝 t₀ := hS.mem_nhds ht₀
  have hSu : S ×ˢ (Set.univ : Set ℂ) ∈ 𝓝 u := prod_mem_nhds hSn Filter.univ_mem
  have hFu : ContDiffAt ℝ l F u := hF.contDiffAt hSu
  have hgt : ContDiffAt ℝ l g t₀ := hg.contDiffAt hSn
  have pn : ((l : ℕ∞ω)) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
  -- the left inverse
  set D : ℂ →L[ℝ] E := fderiv ℝ (fun w => F (t₀, w)) (ρ t₀) with hD
  have hker : LinearMap.ker (D : ℂ →ₗ[ℝ] E) = ⊥ :=
    LinearMap.ker_eq_bot.2 (hinj t₀ ht₀)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective (D : ℂ →ₗ[ℝ] E) hker
  set L : E →L[ℝ] ℂ := LinearMap.toContinuousLinearMap L' with hL
  have hLD : ∀ w, L (D w) = w := fun w => by
    change L' (D w) = w
    simpa using congrArg (fun φ : ℂ →ₗ[ℝ] ℂ => φ w) hL'
  -- the implicit equation
  set f : ℝ × ℂ → ℂ := fun p => L (F p - g p.1) with hf
  have hgfst : ContDiffAt ℝ l (fun p : ℝ × ℂ => g p.1) u := hgt.comp u contDiffAt_fst
  have cdf : ContDiffAt ℝ l f u := L.contDiff.contDiffAt.comp u (hFu.sub hgfst)
  have hFd : HasFDerivAt F (fderiv ℝ F u) u := (hFu.differentiableAt pn).hasFDerivAt
  have hgd : HasFDerivAt (fun p : ℝ × ℂ => g p.1) (fderiv ℝ (fun p : ℝ × ℂ => g p.1) u) u :=
    (hgfst.differentiableAt pn).hasFDerivAt
  have hfd : HasFDerivAt f (L.comp (fderiv ℝ F u - fderiv ℝ (fun p : ℝ × ℂ => g p.1) u)) u :=
    L.hasFDerivAt.comp u (hFd.sub hgd)
  -- the slice derivative
  have hslice : HasFDerivAt (fun w => F (t₀, w)) ((fderiv ℝ F u).comp
      (ContinuousLinearMap.inr ℝ ℝ ℂ)) (ρ t₀) := by
    have h1 : HasFDerivAt (fun w : ℂ => (t₀, w)) (ContinuousLinearMap.inr ℝ ℝ ℂ) (ρ t₀) :=
      hasFDerivAt_prodMk_right t₀ (ρ t₀)
    exact hFd.comp (ρ t₀) h1
  have hDeq : D = (fderiv ℝ F u).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) := hslice.fderiv
  have hgslice : (fderiv ℝ (fun p : ℝ × ℂ => g p.1) u).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) = 0 := by
    have h1 : HasFDerivAt (fun w : ℂ => g ((t₀, w) : ℝ × ℂ).1)
        ((fderiv ℝ (fun p : ℝ × ℂ => g p.1) u).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) (ρ t₀) :=
      hgd.comp (ρ t₀) (hasFDerivAt_prodMk_right t₀ (ρ t₀))
    have h2 : HasFDerivAt (fun w : ℂ => g ((t₀, w) : ℝ × ℂ).1) (0 : ℂ →L[ℝ] E) (ρ t₀) :=
      hasFDerivAt_const (g t₀) (ρ t₀)
    exact h1.unique h2
  have hid : (fderiv ℝ f u).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) = ContinuousLinearMap.id ℝ ℂ := by
    rw [hfd.fderiv]
    ext1 w
    have e1 := congrArg (fun φ : ℂ →L[ℝ] E => φ w) hDeq
    have e2 := congrArg (fun φ : ℂ →L[ℝ] E => φ w) hgslice
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.zero_apply] at e1 e2
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    rw [e2, sub_zero, ← e1, hLD]
  have if₂ : ((fderiv ℝ f u).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)).IsInvertible := by
    rw [hid]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℂ, rfl⟩
  have hψ := cdf.contDiffAt_implicitFunction pn if₂
  have hev := cdf.eventually_apply_eq_iff_implicitFunction pn if₂
  -- the curve `t ↦ (t, ρ t)` tends to `u`
  have hcont : Tendsto (fun t => ((t, ρ t) : ℝ × ℂ)) (𝓝 t₀) (𝓝 u) :=
    (continuousAt_id.prodMk (hρ.continuousAt hSn))
  have hev2 := hcont.eventually hev
  have hfu : f u = 0 := by
    simp only [hf, hu, heq t₀ ht₀, sub_self, map_zero]
  have heqψ : ∀ᶠ t in 𝓝 t₀, cdf.implicitFunction pn if₂ t = ρ t := by
    filter_upwards [hev2, hSn] with t ht htS
    have : f (t, ρ t) = f u := by
      rw [hfu]
      simp only [hf, heq t htS, sub_self, map_zero]
    exact ht.1 this
  exact hψ.congr_of_eventuallyEq (heqψ.mono fun t ht => ht.symm)

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {l : ℕ} (hl : 1 ≤ l) {S : Set ℝ} (hS : IsOpen S)
    {F : ℝ × ℂ → E} {g : ℝ → E} {ρ : ℝ → ℂ}
    (hF : ContDiffOn ℝ l F (S ×ˢ Set.univ)) (hg : ContDiffOn ℝ l g S) (hρ : ContinuousOn ρ S)
    (heq : ∀ t ∈ S, F (t, ρ t) = g t)
    (hinj : ∀ t ∈ S, Function.Injective (fderiv ℝ (fun w => F (t, w)) (ρ t))) :
    ContDiffOn ℝ l ρ S :=
  contDiffOn_of_apply_eq_of_injective_fderiv_aux hl hS hF hg hρ heq hinj
