-- Prove2me | solution 1 for Bl.general_b_fact_alt_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:27.559015+00:00
-- url     : https://prove2.me/submissions/cd2b6878-0a54-4fe3-974b-59d75eeaad3a

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactAltForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open Bl Bl.general_b_fact_alt_form
namespace Bl.general_b_fact_alt_form
theorem _root_.solution :
  ∀ {R : Type u_1} {F : Type u_2} {X : Type u_3} [inst : CommRing.{u_1} R] [IsDomain.{u_1} R] [inst_2 : Field.{u_2} F]
  [inst_3 : Algebra.{u_1, u_2} R F] [IsFractionRing.{u_1, u_2} R F] [inst_5 : AddCommGroup.{u_3} X]
  [inst_6 : Module.{u_2, u_3} F X] [inst_7 : Module.{u_1, u_3} R X] [IsScalarTower.{u_1, u_2, u_3} R F X]
  (S : Submodule.{u_1, u_3} R X) {x : X},
  Membership.mem.{u_3, u_3} (Submodule.span.{u_2, u_3} F (SetLike.coe.{u_3, u_3} S)) x →
    Exists.{u_1 + 1} fun (d : R) ↦
      And (Ne.{u_1 + 1} d 0) (Membership.mem.{u_3, u_3} S (HSMul.hSMul.{u_1, u_3, u_3} d x))  := by
  intro R F X _ _ _ _ _ _ _ _ _ S x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact S.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    have e : (d1 * d2) • (y + z) = d2 • (d1 • y) + d1 • (d2 • z) := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm d2 d1]
    rw [e]
    exact S.add_mem (S.smul_mem d2 h1) (S.smul_mem d1 h2)
  | smul a y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨n, ⟨m, hm⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) a
    refine ⟨m * d, mul_ne_zero (nonZeroDivisors.ne_zero hm) hd, ?_⟩
    have e1 : m • (IsLocalization.mk' F n (⟨m, hm⟩ : nonZeroDivisors R) • y) = n • y := by
      rw [← smul_assoc, Algebra.smul_def, IsLocalization.mk'_spec' F n ⟨m, hm⟩, algebraMap_smul]
    have e : (m * d) • (IsLocalization.mk' F n (⟨m, hm⟩ : nonZeroDivisors R) • y) = n • (d • y) := by
      rw [mul_comm m d, mul_smul, e1, ← mul_smul, ← mul_smul, mul_comm d n]
    rw [e]
    exact S.smul_mem n h
end Bl.general_b_fact_alt_form
