-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tendsto_eq_of_tendsto_of_injective_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T10:43:14.375176+00:00
-- url     : https://prove2.me/submissions/f7453e7e-6ef2-450e-8c69-86b7024f569c

import Mathlib

open Filter Topology

namespace FiniteEnergyPlane

/-- If `f : E → F` (equal finite dimensions) is `C¹` on an open set `U` with injective derivative
at every point of `U`, then every sequence converging to `f p`, `p ∈ U`, eventually has preimages
in `U` that converge to `p`. -/
theorem exists_tendsto_eq_of_tendsto_of_injective_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (f : E → F) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hd : ∀ p ∈ U, Function.Injective (fderiv ℝ f p))
    (p : E) (hp : p ∈ U) (y : ℕ → F) (hy : Tendsto y atTop (𝓝 (f p))) :
    ∃ x : ℕ → E, Tendsto x atTop (𝓝 p) ∧ ∀ᶠ k in atTop, x k ∈ U ∧ f (x k) = y k := by
  have hs : HasStrictFDerivAt f (fderiv ℝ f p) p :=
    (hf.contDiffAt (hU.mem_nhds hp)).hasStrictFDerivAt (by norm_num)
  let e : E ≃L[ℝ] F :=
    (LinearMap.linearEquivOfInjective (fderiv ℝ f p : E →ₗ[ℝ] F) (hd p hp) hdim).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] F) = fderiv ℝ f p := by
    ext v
    rfl
  have hs' : HasStrictFDerivAt f (e : E →L[ℝ] F) p := he ▸ hs
  set g := hs'.localInverse f e p
  have hgc : ContinuousAt g (f p) := hs'.localInverse_continuousAt
  have hgp : g (f p) = p := hs'.localInverse_apply_image
  have hgt : Tendsto g (𝓝 (f p)) (𝓝 p) := by
    have := hgc.tendsto
    rwa [hgp] at this
  refine ⟨fun k => g (y k), hgt.comp hy, ?_⟩
  have h1 : ∀ᶠ k in atTop, g (y k) ∈ U := (hgt.comp hy) (hU.mem_nhds hp)
  have h2 : ∀ᶠ k in atTop, f (g (y k)) = y k := hy hs'.eventually_right_inverse
  filter_upwards [h1, h2] with k hk1 hk2
  exact ⟨hk1, hk2⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (f : E → F) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hd : ∀ p ∈ U, Function.Injective (fderiv ℝ f p))
    (p : E) (hp : p ∈ U) (y : ℕ → F) (hy : Tendsto y atTop (𝓝 (f p))) :
    ∃ x : ℕ → E, Tendsto x atTop (𝓝 p) ∧ ∀ᶠ k in atTop, x k ∈ U ∧ f (x k) = y k :=
  FiniteEnergyPlane.exists_tendsto_eq_of_tendsto_of_injective_fderiv hdim f U hU hf hd p hp y hy
