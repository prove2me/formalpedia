-- Prove2me | solution 1 for Bl.general_b_fact_third_ter.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:44.421537+00:00
-- url     : https://prove2.me/submissions/4703453b-c49f-4f8c-933c-768179c688c6

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdTer_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_ter
namespace Bl.general_b_fact_third_ter
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] [StarRing.{0} E] {W : Type} [inst_3 : AddCommGroup.{0} W]
  [inst_4 : Module.{0, 0} E W] [inst_5 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) W]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E W]
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) W),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) Top.top.{0} →
    ∀ (y : W),
      Exists.{1} fun (ν : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} ν 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} ν y)) := by
  intro E _ _ _ W _ _ _ _ L hL y
  have hy : y ∈ Submodule.span E (L : Set W) := by rw [hL]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x z _ _ ihx ihz =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨b, hb, hbz⟩ := ihz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hax
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul c x _ ihx =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    have hs0 : (s : NumberField.RingOfIntegers E) ≠ 0 := nonZeroDivisors.ne_zero s.2
    refine ⟨(s : NumberField.RingOfIntegers E) * a, mul_ne_zero hs0 ha, ?_⟩
    have key : ((s : NumberField.RingOfIntegers E) * a) • (c • x) = n • (a • x) := by
      rw [mul_comm, mul_smul, ← smul_assoc (s : NumberField.RingOfIntegers E) c x, Algebra.smul_def,
        mul_comm, smul_comm a (c * algebraMap _ E (s : NumberField.RingOfIntegers E)) x]
      simp only at hs
      rw [hs, algebraMap_smul]
    rw [key]
    exact L.smul_mem n hax
end Bl.general_b_fact_third_ter
