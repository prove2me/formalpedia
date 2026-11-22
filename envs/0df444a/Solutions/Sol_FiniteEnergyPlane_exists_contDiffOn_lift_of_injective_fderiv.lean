-- Prove2me | solution 1 for FiniteEnergyPlane.exists_contDiffOn_lift_of_injective_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-22T19:33:03.364401+00:00
-- url     : https://prove2.me/submissions/c9ce9f2d-2283-4b47-9be1-09399785737e

import Mathlib



/-! Lifting a `C^n` curve through a map with injective derivative (equal finite dimensions). -/

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

theorem exists_contDiffOn_lift_of_injective_fderiv_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ E = Module.finrank ℝ F) {n : ℕ}
    (hn : 1 ≤ n) {O : Set E} (hO : IsOpen O) {f : E → F} (hf : ContDiffOn ℝ n f O) {a : E}
    (ha : a ∈ O) (hinj : Function.Injective (fderiv ℝ f a)) {g : ℝ → F} {t₀ δ : ℝ} (hδ : 0 < δ)
    (hg : ContDiffOn ℝ n g (ball t₀ δ)) (hga : g t₀ = f a) :
    ∃ ε > 0, ∃ c : ℝ → E, ContDiffOn ℝ n c (ball t₀ ε) ∧ c t₀ = a ∧
      ∀ t ∈ ball t₀ ε, c t ∈ O ∧ f (c t) = g t := by
  have hfa : ContDiffAt ℝ n f a := hf.contDiffAt (hO.mem_nhds ha)
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  let e₀ : E ≃ₗ[ℝ] F :=
    LinearMap.linearEquivOfInjective (fderiv ℝ f a : E →ₗ[ℝ] F) hinj hdim
  let e : E ≃L[ℝ] F := e₀.toContinuousLinearEquiv
  have he : (e : E →L[ℝ] F) = fderiv ℝ f a := by ext v; rfl
  have hfd : HasFDerivAt f (e : E →L[ℝ] F) a := by
    rw [he]; exact (hfa.differentiableAt hn0).hasFDerivAt
  set G := hfa.localInverse hfd hn0 with hG
  have hGc : ContDiffAt ℝ n G (f a) := hfa.to_localInverse hfd hn0
  have hGa : G (f a) = a := hfa.localInverse_apply_image hfd hn0
  have hright : ∀ᶠ x in 𝓝 (f a), f (G x) = x :=
    (hfa.hasStrictFDerivAt' hfd hn0).eventually_right_inverse
  have hGO : ∀ᶠ x in 𝓝 (f a), G x ∈ O := by
    have hm : G (f a) ∈ O := by rw [hGa]; exact ha
    exact hGc.continuousAt.preimage_mem_nhds (hO.mem_nhds hm)
  have hGev : ∀ᶠ x in 𝓝 (f a), ContDiffAt ℝ n G x :=
    hGc.eventually (by exact_mod_cast WithTop.natCast_ne_top n)
  have hP : ∀ᶠ x in 𝓝 (f a), ContDiffAt ℝ n G x ∧ f (G x) = x ∧ G x ∈ O :=
    hGev.and (hright.and hGO)
  have hgt : ContinuousAt g t₀ := (hg.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hδ))).continuousAt
  have hQ : ∀ᶠ t in 𝓝 t₀, (ContDiffAt ℝ n G (g t) ∧ f (G (g t)) = g t ∧ G (g t) ∈ O) ∧
      t ∈ ball t₀ δ := by
    refine (hgt.eventually (hga ▸ hP)).and (isOpen_ball.mem_nhds (mem_ball_self hδ))
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.1 hQ
  refine ⟨ε, hε, G ∘ g, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨⟨h1, -, -⟩, h2⟩ := hεP t ht
    exact (h1.comp t (hg.contDiffAt (isOpen_ball.mem_nhds h2))).contDiffWithinAt
  · simp only [Function.comp_apply, hga, hGa]
  · intro t ht
    obtain ⟨⟨-, h2, h3⟩, -⟩ := hεP t ht
    exact ⟨h3, h2⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ E = Module.finrank ℝ F) {n : ℕ}
    (hn : 1 ≤ n) {O : Set E} (hO : IsOpen O) {f : E → F} (hf : ContDiffOn ℝ n f O) {a : E}
    (ha : a ∈ O) (hinj : Function.Injective (fderiv ℝ f a)) {g : ℝ → F} {t₀ δ : ℝ} (hδ : 0 < δ)
    (hg : ContDiffOn ℝ n g (ball t₀ δ)) (hga : g t₀ = f a) :
    ∃ ε > 0, ∃ c : ℝ → E, ContDiffOn ℝ n c (ball t₀ ε) ∧ c t₀ = a ∧
      ∀ t ∈ ball t₀ ε, c t ∈ O ∧ f (c t) = g t :=
  FiniteEnergyPlane.exists_contDiffOn_lift_of_injective_fderiv_aux hdim hn hO hf ha hinj hδ hg hga
