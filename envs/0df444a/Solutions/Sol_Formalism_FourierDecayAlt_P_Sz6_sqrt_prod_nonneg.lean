-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz6.sqrt_prod_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:31.861803+00:00
-- url     : https://prove2.me/submissions/e9ecafb0-2fdd-4d9b-a425-5f1ed69364de

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
open Formalism.FourierDecayAlt.P.Sz6
namespace Formalism.FourierDecayAlt.P.Sz6
theorem _root_.solution {α : Type} (s : Finset α) (f : α → ℝ) (h : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, Real.sqrt_mul (h a (mem_insert_self a s)),
      ih (fun i hi => h i (mem_insert_of_mem hi))]
end Formalism.FourierDecayAlt.P.Sz6
