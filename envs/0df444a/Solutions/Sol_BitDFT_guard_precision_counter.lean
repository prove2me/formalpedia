-- Prove2me | solution 1 for BitDFT.guard_precision_counter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:53:30.984596+00:00
-- url     : https://prove2.me/submissions/f373dae4-e0cd-459f-bf82-72eb5355f4f0

import Theorems.Thm_BitDFT_binary_counter_add
import Definitions.Def_BitDFT_Numerics

namespace BitDFT.BinaryCounter
open IntMul

private theorem val_append_bit (w : List Bool) (b : Bool) :
    IntMul.val (w++[b]) = 2*IntMul.val w+b.toNat := by
  simp [IntMul.val,List.foldl_append]

private theorem value_reverse (w : List Bool) : value w.reverse = IntMul.val w := by
  suffices h : ∀ a : List Bool, value a = IntMul.val a.reverse by
    simpa using h w.reverse
  intro a
  induction a with
  | nil => rfl
  | cons b a ih =>
    rw [List.reverse_cons,val_append_bit]
    simp only [value,ih]
    omega

end BitDFT.BinaryCounter
open BitDFT BitDFT.BinaryCounter IntMul

/-- The counter implements the arithmetic of the Fourier guard precision once the
    parsed precision bits and unary logarithmic increment have been prepared. -/
theorem solution (base : machine.Cfg) (n b : ℕ) (w : List Bool)
    (hb : 1 ≤ b) (hv : IntMul.val w = b) (hw : w.length ≤ b) :
    ∃ t v, t ≤ 5*guardPrecision n b ∧ BinaryCounter.value v = guardPrecision n b ∧
      machine.step^[t] (frame base .tick w.reverse (3*IntMul.lg n+5) 1) =
        frame base .halt v 0 1 := by
  obtain ⟨t,v,ht,hv',hr⟩ := BitDFT.binary_counter_add base w.reverse (3*IntMul.lg n+5)
  refine ⟨t,v,?_,?_,hr⟩
  · simp only [List.length_reverse] at ht
    unfold guardPrecision
    omega
  · rw [value_reverse,hv] at hv'
    simpa [guardPrecision,Nat.add_assoc] using hv'
