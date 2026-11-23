-- Prove2me | solution 1 for Bl.SecondBlockLemmaP.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:40.899079+00:00
-- url     : https://prove2.me/submissions/92c3f0f4-2983-4cc9-b708-7a9a5d05d002

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasO_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.SecondBlockLemmaP
namespace Bl.SecondBlockLemmaP
theorem _root_.solution :
  ∀ (O K V : Type) [inst : CommRing.{0} O] [IsDomain.{0} O] [inst_2 : Field.{0} K] [inst_3 : Algebra.{0, 0} O K]
  [IsFractionRing.{0, 0} O K] [inst_5 : AddCommGroup.{0} V] [inst_6 : Module.{0, 0} K V] [inst_7 : Module.{0, 0} O V]
  [IsScalarTower.{0, 0, 0} O K V] (M : Submodule.{0, 0} O V) (v : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} M)) v →
    Exists.{1} fun (c : O) ↦ And (Ne.{1} c 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} c v)) := by
  intro O K V _ _ _ _ _ _ _ _ _ M v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, hc1, h1⟩ := hx
    obtain ⟨c2, hc2, h2⟩ := hy
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    have e : (c1 * c2) • (x + y) = c2 • (c1 • x) + c1 • (c2 • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm c2 c1]
    rw [e]
    exact M.add_mem (M.smul_mem c2 h1) (M.smul_mem c1 h2)
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) a
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap O K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    refine ⟨d * c, mul_ne_zero hd0 hc, ?_⟩
    have hq : algebraMap O K d * (algebraMap O K n / algebraMap O K d) = algebraMap O K n := by
      field_simp
    have e : (d * c) • ((algebraMap O K n / algebraMap O K d) • x) = n • (c • x) := by
      rw [mul_smul, smul_comm c, ← algebraMap_smul K d, smul_smul, hq, algebraMap_smul]
    rw [e]
    exact M.smul_mem n h
end Bl.SecondBlockLemmaP
