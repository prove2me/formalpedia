-- Prove2me | solution 1 for Bl.general_b_fact_left_bis.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:14:54.832283+00:00
-- url     : https://prove2.me/submissions/aa3b9581-cd09-4918-a44a-1d6d556eff9b

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftBis_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_left_bis
namespace Bl.general_b_fact_left_bis
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {N : Nat}
  (L'' : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin N → E)),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L'')) Top.top.{0} →
    ∀ (v : Fin N → E),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} L'' (HSMul.hSMul.{0, 0, 0} d v)) := by
  intro E _ _ N L'' hspan v
  have hv : v ∈ Submodule.span E (L'' : Set (Fin N → E)) := by
    rw [hspan]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L''.zero_mem⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨d1, hd1, h1⟩ := ihx
    obtain ⟨d2, hd2, h2⟩ := ihy
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    have e1 : (d1 * d2) • x = d2 • (d1 • x) := by rw [mul_comm, mul_smul]
    have e2 : (d1 * d2) • y = d1 • (d2 • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L''.add_mem (L''.smul_mem d2 h1) (L''.smul_mem d1 h2)
  | smul a x _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a
    refine ⟨(c : NumberField.RingOfIntegers E) * d, mul_ne_zero (nonZeroDivisors.ne_zero c.2) hd, ?_⟩
    have key : ((c : NumberField.RingOfIntegers E) * d) • (a • x) = b • (d • x) := by
      rw [← algebraMap_smul E ((c : NumberField.RingOfIntegers E) * d), ← algebraMap_smul E b,
        ← algebraMap_smul E d, smul_smul, smul_smul]
      congr 1
      simp only at hbc
      rw [map_mul, ← hbc]
      ring
    rw [key]
    exact L''.smul_mem b h
end Bl.general_b_fact_left_bis
