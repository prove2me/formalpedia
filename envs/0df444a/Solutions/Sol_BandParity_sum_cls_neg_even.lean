-- Prove2me | solution 1 for BandParity.sum_cls_neg_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:38.978593+00:00
-- url     : https://prove2.me/submissions/cff5956b-88fc-428f-a704-6bbddd1cb280

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_char_neg
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
omit hχ
namespace BandParity
theorem _root_.solution (hodd : χ (-1) = -1) (g : ZMod p → ℤ) (hg : ∀ x ≠ 0, g (-x) = g x)
    {z : GaussianInt} (hz : z ≠ 0) :
    ∑ x ∈ cls χ (-z), g x = ∑ x ∈ cls χ z, g x := by
  simp only [cls, Finset.sum_filter]
  refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun x => ?_
  simp only [Equiv.neg_apply, char_neg hodd]
  by_cases hx : x = 0
  · subst hx
    have h1 : ¬ (χ 0 = -z) := by rw [MulChar.map_zero]; exact fun h => hz (neg_eq_zero.1 h.symm)
    simp [MulChar.map_zero, hz, hz.symm]
  · rw [hg x hx]
    by_cases h : χ x = -z
    · simp [h]
    · have : ¬ -χ x = z := fun h' => h (by rw [← h', neg_neg])
      simp [h, this]
end BandParity
