-- Prove2me | solution 1 for CircuitComplexity.CompleteBasis.of_simulation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:56.29591+00:00
-- url     : https://prove2.me/submissions/5e684ce8-9367-42d3-9db1-b2ee30127008

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
namespace CompleteBasis
theorem _root_.solution (B₁ B₂ : Basis) [CompleteBasis B₁]
    (sim : ∀ {N M G} [NeZero N] [NeZero M] (c : Circuit B₁ N M G),
      ∃ G', ∃ c' : Circuit B₂ N M G', c'.eval = c.eval)
    : CompleteBasis B₂ where
  complete f := by
    obtain ⟨G, c, hc⟩ := CompleteBasis.complete (B := B₁) f
    obtain ⟨G', c', hc'⟩ := sim c
    exact ⟨G', c', hc'.trans hc⟩
end CompleteBasis
end CircuitComplexity
