-- Prove2me | solution 1 for Bl.SecondBlockLemmaK.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:01.480952+00:00
-- url     : https://prove2.me/submissions/4e2a91d0-2583-4b74-8e90-0132f542e971

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasJ_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.SecondBlockLemmaK
namespace Bl.SecondBlockLemmaK
theorem _root_.solution :
  ∀ {R F X : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] [inst_2 : Field.{0} F] [inst_3 : Algebra.{0, 0} R F]
  [IsFractionRing.{0, 0} R F] [inst_5 : AddCommGroup.{0} X] [inst_6 : Module.{0, 0} F X] [inst_7 : Module.{0, 0} R X]
  [IsScalarTower.{0, 0, 0} R F X] (S : Submodule.{0, 0} R X) {x : X},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} F (SetLike.coe.{0, 0} S)) x →
    Exists.{1} fun (d : R) ↦ And (Ne.{1} d 0) (Membership.mem.{0, 0} S (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro R F X _ _ _ _ _ _ _ _ _ S x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact S.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine S.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact S.smul_mem b hay
    · rw [mul_smul]
      exact S.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨d, hd, hdy⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbF : algebraMap R F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨d * b, mul_ne_zero hd hb0, ?_⟩
    have key : (d * b) • ((algebraMap R F a / algebraMap R F b) • y) = a • (d • y) := by
      rw [← algebraMap_smul F (d * b), ← algebraMap_smul F a, ← algebraMap_smul F d, smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact S.smul_mem a hdy
end Bl.SecondBlockLemmaK
