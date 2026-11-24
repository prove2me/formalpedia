-- Prove2me | solution 1 for Formalism.REAL.arr_operators_gl_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:03.117962+00:00
-- url     : https://prove2.me/submissions/1e1e382e-8c08-4b69-86b2-e5697c6d0ad7

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_factorAction_commutator
import Theorems.Thm_Formalism_REAL_factorAction_commute_of_ne
import Theorems.Thm_Formalism_REAL_factorAction_commute_pointwiseAction
import Theorems.Thm_Formalism_REAL_pointwise_operator_gl_relation
import Theorems.Thm_Formalism_REAL_commutator_of_sums_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    GlRel (arrE E j) := by
  intro a b c d
  simp only [arrE]
  rw [commutator_of_sums_split Finset.univ (fun i => factorAction i a b) (fun i => factorAction i c d) (ptE E a b) (ptE E c d)
    (fun i _ i' _ h => factorAction_commute_of_ne i i' h a b c d) (fun i _ => factorAction_commute_pointwiseAction E i a b c d)
    (fun i _ => (factorAction_commute_pointwiseAction E i c d a b).symm)]
  simp only [factorAction_commutator, pointwise_operator_gl_relation E hE]
  split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel
end Formalism.REAL
