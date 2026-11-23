-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.idl_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:48.188745+00:00
-- url     : https://prove2.me/submissions/01ee96eb-6cfb-4150-abd4-f93971122783

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (hg : 0 < g) :
    S6.idl E g 0 (-(ν + 1)) = S6.dualIdl E g ν * FractionalIdeal.spanSingleton _ (g : E) := by
  have hg' : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  unfold S6.dualIdl S6.idl
  rw [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
  congr 2
  rw [zpow_zero, zpow_neg_one, inv_mul_cancel₀ hg']
end Formalism.FourierDecayAlt.P.Jx3
