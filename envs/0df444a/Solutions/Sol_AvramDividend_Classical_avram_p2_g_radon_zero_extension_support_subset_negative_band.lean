-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_g_radon_zero_extension_support_subset_negative_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:16:53.692619+00:00
-- url     : https://prove2.me/submissions/c86a2e29-20f5-45b3-97a5-2fa921b19260

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology

/-- A negative-mark test vanishing near zero has a zero extension whose
    functional support lies in the corresponding separated band. -/
theorem solution
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ)
    (ε : ℝ)
    (hf : ∀ x : {x : ℝ // x < 0}, -ε < (x : ℝ) → f x = 0) :
    Function.support
      (Function.extend (Subtype.val : {x : ℝ // x < 0} → ℝ)
        (fun x => f x) 0) ⊆ Iic (-ε) := by
  intro x hx
  by_contra hnot
  have hxgt : -ε < x := lt_of_not_ge hnot
  by_cases hxneg : x < 0
  · have hext :
        Function.extend (Subtype.val : {x : ℝ // x < 0} → ℝ)
          (fun y => f y) 0 x = f ⟨x, hxneg⟩ :=
      Function.extend_val_apply (p := fun z : ℝ => z < 0) (b := x) hxneg
    have hz : f ⟨x, hxneg⟩ = 0 := hf ⟨x, hxneg⟩ hxgt
    exact hx (hext.trans hz)
  · have hext :
        Function.extend (Subtype.val : {x : ℝ // x < 0} → ℝ)
          (fun y => f y) 0 x = 0 :=
      Function.extend_val_apply' (p := fun z : ℝ => z < 0) (b := x) hxneg
    exact hx hext
