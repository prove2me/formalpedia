-- Prove2me | solution 1 for FixedNumerator.mem_normBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:04.495175+00:00
-- url     : https://prove2.me/submissions/f22b8303-d511-4763-9366-7e39bb2b5412

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
public import Theorems.Thm_FixedNumerator_int_neg_le_mul_self
public import Theorems.Thm_FixedNumerator_norm_eq_sq

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {X : ℕ} {c : GaussianInt} : c ∈ normBall X ↔ c.norm ≤ X := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(c.re, c.im), ?_, rfl⟩, h⟩
    have hn := norm_eq_sq c
    have h1 := int_neg_le_mul_self c.re
    have h2 := int_neg_le_mul_self c.im
    have h3 := mul_self_nonneg c.re
    have h4 := mul_self_nonneg c.im
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
end FixedNumerator
