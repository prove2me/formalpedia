-- Prove2me | solution 1 for Formalism.NG.genfin_det_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:39.212135+00:00
-- url     : https://prove2.me/submissions/cde5db8a-eda6-4dc9-8026-022ade504655

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution {ι K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial ι K)) (h : ∀ i j, (A i j).totalDegree ≤ 1) :
    A.det.totalDegree ≤ Fintype.card n := by
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
  have hprod : (∏ i, A (σ i) i).totalDegree ≤ Fintype.card n := by
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    calc ∑ i, (A (σ i) i).totalDegree ≤ ∑ _i : n, 1 := Finset.sum_le_sum fun i _ => h _ _
      _ = Fintype.card n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
    exact hprod
  · rw [hs, Units.neg_smul, one_smul, MvPolynomial.totalDegree_neg]
    exact hprod
end Formalism.NG
