-- Prove2me | solution 1 for Bl.general_b_fact_right_alt_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:54.225092+00:00
-- url     : https://prove2.me/submissions/2ef82150-f257-42c2-aa32-0f01c9282b5b

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightAltForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_alt_form
namespace Bl.general_b_fact_right_alt_form
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} E V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V] (A : Set.{0} V) (y : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} E A) y →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
      And (Ne.{1} d 0)
        (Membership.mem.{0, 0} (Submodule.span.{0, 0} (NumberField.RingOfIntegers.{0} E) A) (HSMul.hSMul.{0, 0, 0} d y)) := by
  intro E _ _ V _ _ _ _ A y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x z _ _ hx hz =>
    obtain ⟨d1, hd1, h1⟩ := hx
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    have e1 : (d1 * d2) • x = d2 • (d1 • x) := by rw [mul_comm, mul_smul]
    have e2 : (d1 * d2) • z = d1 • (d2 • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    have hb : (b : NumberField.RingOfIntegers E) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : NumberField.RingOfIntegers E) * d, mul_ne_zero hb hd, ?_⟩
    have key : ((b : NumberField.RingOfIntegers E) * d) • (c • x) = a • (d • x) := by
      rw [← algebraMap_smul E ((b : NumberField.RingOfIntegers E) * d), ← algebraMap_smul E a,
        ← algebraMap_smul E d, smul_smul, smul_smul, map_mul]
      congr 1
      simp only at hab
      rw [← hab]
      ring
    rw [key]
    exact Submodule.smul_mem _ _ h
end Bl.general_b_fact_right_alt_form
