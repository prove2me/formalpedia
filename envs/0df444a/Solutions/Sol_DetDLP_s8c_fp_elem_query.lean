-- Prove2me | solution 1 for DetDLP.s8c_fp_elem_query
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T09:45:59.298799+00:00
-- url     : https://prove2.me/submissions/b1c164d0-3270-4fba-a13a-83d12af6f97c

import Definitions.Def_DetDLP_S8C3_PortEval

set_option autoImplicit false
namespace DetDLP.S8C3
open M89S1 S8C S8J S8G.FpMoment
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Reduction to the physical incidence layout and its local evaluator. -/
theorem ofLayout {p T : ℕ} [Fact p.Prime] (S : FpSeed p (blockCount (bitLen p)))
    (i : Fin (blockCount (bitLen p))) (η : W) (hT : T ≤ p) (hη : η.length ≤ bitLen p)
    (A : w3_FactorLayout) (test : w3_factorTest A) (hg : Function.Surjective A.gate)
    (witness : {y : Fin A.nb → Bool // Accept A test y} ≃ ↥(elemSet S i T η))
    (edges : 2*A.ne < scale (blockCount (bitLen p)) (bitLen p))
    (degree : ∀ v, (w3_factorGraph A).deg v ≤ max 12 (Nat.ceil (136*((bitLen p:ℝ)+2)^((3:ℝ)/4))))
    (makeEq : MakePacket.make (word T S i η) = encodeBTNInstance (word T S i η) (w3_factorGraph A).subdivision (scale (blockCount (bitLen p)) (bitLen p)) (scale (blockCount (bitLen p)) (bitLen p)) 1)
    (eval : ∀ v a, PortEval.port (encodePortQuery (word T S i η) v.val (List.ofFn a)) = encodeNatListBin [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a then 1 else 0]) :
    Realizes MakePacket.make PortEval.port 200000 (word T S i η) (bitLen p)
      (elemCount (fpFactorBlock T S i) elemWord η) := by
  let b := bitLen p
  let m := blockCount b
  let s := scale m b
  let w := word T S i η
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hscale : b+2 ≤ s := Nat.le_mul_of_pos_left _ (by dsimp [m] at hm; dsimp [m]; positivity)
  have hs : 2 ≤ s := by omega
  have he : 2*A.ne < s := edges
  have dims := w3_incDims A hg
  have qs := w3_incQueryBounds A hg s (by omega) he.le w
  have wb := wordBudget S i η hT hη
  rw [← elemSet_card]
  refine wireRealizes _ _ 200000 s b w _ _ ((w3_factorEquiv A test).trans witness) hs (by omega) edges ?_ ?_ wb.1 wb.2 makeEq ?_
  · change A.ng+A.nb+A.ne ≤ s^200000
    calc _ ≤ s^2 := by nlinarith [dims.1,dims.2]
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  · apply (max_le (Finset.sup_le (fun v _ => degree v)) (le_trans (by decide : 2 ≤ 12) (le_max_left _ _))).trans
    exact degreeBudget hm
  · intro v a
    refine ⟨(Nat.le_of_succ_le (qs.2 v a)).trans ?_,?_⟩
    · exact (Nat.pow_le_pow_right (by omega) (by decide : 5 ≤ 200000)).trans
        (Nat.le_mul_of_pos_left _ (by decide))
    · exact eval v a

end DetDLP.S8C3

open DetDLP DetDLP.S8C3 in
theorem solution : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [3] := by
  intro _
  apply tagIntro MakePacket.make PortEval.port 200000 MakePacket.make_poly PortEval.port_poly
  intro p _ T S i η hT hη
  exact ofLayout S i η hT hη _ _ (Semantics.gate_surj p T ((S i).1.val+1) (S i).2.val η) (Semantics.points hT S i η)
    (Semantics.edgeBudget p T _ _ η hη) (Semantics.degree p T _ _ η) (MakePacket.make_word p T S i η) (PortEval.port_word T S i η)
