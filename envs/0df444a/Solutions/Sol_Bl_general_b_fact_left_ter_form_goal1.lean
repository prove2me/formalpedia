-- Prove2me | solution 1 for Bl.general_b_fact_left_ter_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:37.689944+00:00
-- url     : https://prove2.me/submissions/249503f5-6075-4da2-b647-b6cbc7888733

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftTerForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_left_ter_form
namespace Bl.general_b_fact_left_ter_form
theorem _root_.solution :
  ∀ {R K V : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] [inst_2 : Field.{0} K] [inst_3 : Algebra.{0, 0} R K]
  [IsFractionRing.{0, 0} R K] [inst_5 : AddCommGroup.{0} V] [inst_6 : Module.{0, 0} R V] [inst_7 : Module.{0, 0} K V]
  [IsScalarTower.{0, 0, 0} R K V] (M : Submodule.{0, 0} R V) (y : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} M)) y →
    Exists.{1} fun (s : R) ↦ And (Ne.{1} s 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} s y)) := by
  intro R K V _ _ _ _ _ _ _ _ _ M y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    have e2 : (s * t) • z = s • (t • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact M.add_mem (M.smul_mem t hsx) (M.smul_mem s htz)
  | smul k x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b * s, mul_ne_zero hb0 hs, ?_⟩
    have key : algebraMap R K (b * s) * (algebraMap R K a / algebraMap R K b)
        = algebraMap R K a * algebraMap R K s := by
      rw [map_mul]; field_simp
    have e : (b * s) • ((algebraMap R K a / algebraMap R K b) • x) = a • (s • x) := by
      rw [← algebraMap_smul K (b * s), smul_smul, key, mul_smul, algebraMap_smul K, algebraMap_smul K]
    rw [e]
    exact M.smul_mem a hsx
end Bl.general_b_fact_left_ter_form
