-- Prove2me | solution 1 for Bl.SecondBlockLemmaA.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:57.841211+00:00
-- url     : https://prove2.me/submissions/2f71e436-161f-4b85-8e24-9d2040637381

import Mathlib
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.SecondBlockLemmaA
namespace Bl.SecondBlockLemmaA
theorem _root_.solution :
  ∀ {O : Type u_1} [inst : CommRing.{u_1} O] [inst_1 : IsDomain.{u_1} O] [inst_2 : IsDiscreteValuationRing.{u_1} O]
  {ι : Type u_2} (s : Finset.{u_2} ι) (a : ι → O),
  Eq.{1}
    (DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O)
      (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ a i))
    (Finset.sum.{u_2, 0} s fun (i : ι) ↦
      DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O) (a i)) := by
  intro O _ _ _ ι s a
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, AddValuation.map_mul, ih]
end Bl.SecondBlockLemmaA
