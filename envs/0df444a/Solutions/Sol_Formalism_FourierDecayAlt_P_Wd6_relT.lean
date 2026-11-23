-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.relT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:00.788084+00:00
-- url     : https://prove2.me/submissions/10f63b68-20d1-487a-891b-4e2a6ed1e2ad

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (p c ci : A) (D Y Y' : K) (h1 : D • (p * c) - D • (c * p) = (Y - Y') • c)
    (h2 : D • (p * ci) - D • (ci * p) = (Y' - Y) • ci) (h3 : c * ci = ci * c) :
    Rel (Tm Y p c ci) (Tm Y' p c ci) D := by
  intro i k r s
  fin_cases i <;> fin_cases k <;> fin_cases r <;> fin_cases s <;>
    simp [Tm, Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_add, h3]
  all_goals first
    | module
    | linear_combination (norm := module) h1
    | linear_combination (norm := module) h2
    | linear_combination (norm := module) (-1 : K) • h1
    | linear_combination (norm := module) (-1 : K) • h2
end Formalism.FourierDecayAlt.P.Wd6
