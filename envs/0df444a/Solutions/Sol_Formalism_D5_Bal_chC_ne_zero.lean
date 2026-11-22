-- Prove2me | solution 1 for Formalism.D5.Bal.chC_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:01.624166+00:00
-- url     : https://prove2.me/submissions/f0854385-cc36-4cdc-a5a1-3923cd58571f

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
namespace Bal
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private lemma cconj_fst_fst_eq_one : (cconj : E0 × H).1.1 = 1 := rfl
end
end Bal
end Formalism.D5
end
end

set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5.Bal
theorem _root_.solution (Hs : CycHost H) : Hs.chC ≠ 0 := by
  intro h
  have h1 : Hs.chC cconj = 1 := by rw [h, AddChar.zero_apply]
  have hne : ¬ (1 : ZMod 2) = 0 := by decide
  rw [Hs.7, cconj_fst_fst_eq_one, sgn2, if_neg hne] at h1
  norm_num at h1
end Formalism.D5.Bal
