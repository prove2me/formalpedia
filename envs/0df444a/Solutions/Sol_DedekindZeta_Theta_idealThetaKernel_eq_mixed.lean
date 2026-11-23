-- Prove2me | solution 1 for DedekindZeta.Theta.idealThetaKernel_eq_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:51:28.389873+00:00
-- url     : https://prove2.me/submissions/a9c9f420-855f-4084-9dd5-569bf3b00914

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (𝔞 : Ideal (𝓞 K))
    (x : mixedEmbedding.mixedSpace K) :
    idealThetaKernel K 𝔞 x = mixedThetaKernel K (𝔞 : FractionalIdeal (𝓞 K)⁰ K) x := by
  -- The integral-closure embedding `𝓞 K ↪ K` restricts to a bijection between
  -- the nonzero elements of `𝔞` and the nonzero elements of the coerced
  -- fractional ideal: surjectivity is `FractionalIdeal.mem_coeIdeal`
  -- (every element of `↑𝔞` is `algebraMap` of an element of `𝔞`), and
  -- injectivity is `RingOfIntegers.coe_injective`.
  set I : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hI
  -- For every element `b` of the coerced ideal there is an integral preimage in `𝔞`.
  have key : ∀ b : K, b ∈ (I : Submodule (𝓞 K) K) → ∃ a : 𝓞 K, a ∈ 𝔞 ∧ (a : K) = b := by
    intro b hb
    rw [FractionalIdeal.mem_coe, hI, FractionalIdeal.mem_coeIdeal] at hb
    obtain ⟨a, ha, hab⟩ := hb
    exact ⟨a, ha, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hab⟩
  have hmem : ∀ a : 𝓞 K, a ∈ 𝔞 → (a : K) ∈ (I : Submodule (𝓞 K) K) := by
    intro a ha
    rw [FractionalIdeal.mem_coe, hI, RingOfIntegers.coe_eq_algebraMap]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ ha
  let e : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} ≃
      {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} :=
  { toFun := fun a => ⟨(a.1 : K), hmem a.1 a.2.1, RingOfIntegers.coe_ne_zero_iff.mpr a.2.2⟩
    invFun := fun b => ⟨(key b.1 b.2.1).choose, (key b.1 b.2.1).choose_spec.1, by
      intro h0
      apply b.2.2
      rw [← (key b.1 b.2.1).choose_spec.2, h0]; simp⟩
    left_inv := fun a => by
      apply Subtype.ext
      apply RingOfIntegers.coe_injective
      simpa using (key (a.1 : K) (hmem a.1 a.2.1)).choose_spec.2
    right_inv := fun b => by
      apply Subtype.ext
      simpa using (key b.1 b.2.1).choose_spec.2 }
  rw [idealThetaKernel, mixedThetaKernel, ← Equiv.tsum_eq e]
  rfl
end DedekindZeta.Theta
