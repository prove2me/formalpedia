-- Prove2me | solution 1 for ConjugateConvex.Involution.conjFun_lsc_and_closed_relative
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:23:15.943017+00:00
-- url     : https://prove2.me/submissions/358b6948-23a6-4d16-8b6e-be1c5a461c5a

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun
open Filter Topology

open ConjugateConvex.Involution in
theorem cc174_key {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (ξ0 : Fin n → ℝ) (y : ℝ) (x : Fin n → ℝ) (hx : x ∈ G) (hy : y < x ⬝ᵥ ξ0 - f x) :
    ∀ᶠ ξ in 𝓝[conjDomain G f] ξ0, y < conjFun G f ξ := by
  have hc : Continuous (fun ξ : Fin n → ℝ => x ⬝ᵥ ξ - f x) := by fun_prop
  have h1 : ∀ᶠ ξ in 𝓝 ξ0, y < x ⬝ᵥ ξ - f x :=
    hc.continuousAt.eventually (lt_mem_nhds hy)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with ξ h2 h3
  exact lt_of_lt_of_le h2 (le_csSup h3 ⟨x, hx, rfl⟩)

open Filter Topology ConjugateConvex.Involution in
theorem solution {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    LowerSemicontinuousOn (conjFun G f) (conjDomain G f) ∧
      ∀ ξ ∈ closure (conjDomain G f) \ conjDomain G f,
        Tendsto (conjFun G f) (𝓝[conjDomain G f] ξ) atTop := by
  constructor
  · intro ξ0 _ y hy
    rcases G.eq_empty_or_nonempty with hG | hG
    · have h0 : ∀ ξ, conjFun G f ξ = 0 := by
        intro ξ; simp [conjFun, hG]
      exact Eventually.of_forall fun ξ => by rw [h0] at hy ⊢; exact hy
    · obtain ⟨s, ⟨x, hx, rfl⟩, hs⟩ :=
        exists_lt_of_lt_csSup (hG.image (fun x => x ⬝ᵥ ξ0 - f x)) hy
      exact cc174_key G f ξ0 y x hx hs
  · rintro ξ0 ⟨_, hξ0⟩
    rw [tendsto_atTop]
    intro b
    have hnb : ¬ BddAbove ((fun x => x ⬝ᵥ ξ0 - f x) '' G) := hξ0
    rw [not_bddAbove_iff] at hnb
    obtain ⟨s, ⟨x, hx, rfl⟩, hs⟩ := hnb b
    filter_upwards [cc174_key G f ξ0 b x hx hs] with ξ h
    exact h.le
