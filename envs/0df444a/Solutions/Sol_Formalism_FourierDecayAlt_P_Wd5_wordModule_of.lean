-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd5.wordModule_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:59.856522+00:00
-- url     : https://prove2.me/submissions/62525d78-5d62-49b9-814c-18f6fa91463b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd5
open Matrix Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P.Wd5
theorem _root_.solution (hS : StartModule) (hP : LetterPlus) (hM : LetterMinus) (hF : WordFree) :
    WordModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q w hQ hw
  induction w with
  | nil =>
    have hset : {Y : K | Reg ([] : List (Letter K S)) Y} = Set.univ := by
      ext Y
      simp [Reg]
    rw [hset]
    exact hS K A S QQ q hQ
  | cons l w ih =>
    obtain ⟨hnd, hreal, hpw⟩ := hw
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    have hMod := ih ⟨hnd.2, fun l' hl' => hreal l' (List.mem_cons_of_mem _ hl'), hpw.2⟩
    obtain ⟨hFR, hFT⟩ := hF K A S QQ w l.intersection_update_fsHerm_neg_one hnd.1
    have hmem : l.pt ∈ {Y : K | Reg w Y} := fun l' hl' => hpw.1 l' hl'
    have hstar : star l.pt = l.pt := hreal l (by simp)
    cases hpl : l.plus
    · have key := hM K A S _ _ _ _ l.intersection_update_fsHerm_neg_one l.pt hMod hFR hFT hmem hstar
      convert key using 1
      all_goals first
        | (simp [RRw, hpl]; done)
        | (ext Y; simp [Reg, RegL, TTw, qw, hpl, and_comm]; done)
        | (funext Y; simp [TTw, qw, hpl])
    · have key := hP K A S _ _ _ _ l.intersection_update_fsHerm_neg_one l.pt hMod hFR hFT hmem hstar
      convert key using 1
      all_goals first
        | (simp [RRw, hpl]; done)
        | (ext Y; simp [Reg, RegL, TTw, qw, hpl, and_comm]; done)
        | (funext Y; simp [TTw, qw, hpl])
end Formalism.FourierDecayAlt.P.Wd5
