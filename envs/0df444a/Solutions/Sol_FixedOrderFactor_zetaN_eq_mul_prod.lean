-- Prove2me | solution 1 for FixedOrderFactor.zetaN_eq_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:35.775507+00:00
-- url     : https://prove2.me/submissions/bc3abb1c-0c41-4c2e-b713-9105f2fa53ca

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_hasProd_zetaN

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    zetaN ∅ s = (∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s)⁻¹) * zetaN N s := by
  set g : Nat.Primes → ℝ := fun q => (1 - (1 / (q : ℝ)) ^ s)⁻¹
  have hall : HasProd g (zetaN ∅ s) := by
    have h := hasProd_zetaN ∅ hs
    have hsupp : Function.mulSupport g ⊆ {q | q ∉ (∅ : Finset Nat.Primes)} := by
      intro q _; simp
    exact (hasProd_subtype_iff_of_mulSupport_subset hsupp).mp h
  have hN : HasProd (g ∘ (↑) : (↑(N : Set Nat.Primes) : Type) → ℝ) (∏ q ∈ N, g q) := by
    have := hasProd_fintype (g ∘ ((↑) : (↑(N : Set Nat.Primes) : Type) → Nat.Primes))
    convert this using 1
    exact (Finset.prod_coe_sort N g).symm.trans (by rfl)
  have hc : HasProd (g ∘ (↑) : (↑((N : Set Nat.Primes)ᶜ) : Type) → ℝ) (zetaN N s) :=
    hasProd_zetaN N hs
  exact hall.unique (hN.mul_isCompl isCompl_compl hc)
end FixedOrderFactor
