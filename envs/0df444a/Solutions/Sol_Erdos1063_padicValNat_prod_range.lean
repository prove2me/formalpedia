-- Prove2me | solution 1 for Erdos1063.padicValNat_prod_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:36:11.478617+00:00
-- url     : https://prove2.me/submissions/30606f69-3c03-4d79-884c-84afcbebfba9

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {p : ℕ} [Fact p.Prime] (f : ℕ → ℕ) (m : ℕ)
    (hf : ∀ i < m, f i ≠ 0) :
    padicValNat p (∏ i ∈ Finset.range m, f i) = ∑ i ∈ Finset.range m, padicValNat p (f i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      padicValNat.mul (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (by simp at hi; omega))
        (hf m (by omega)),
      ih (fun i hi => hf i (by omega))]
end Erdos1063
