-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Misc.tpolyProd_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:06.526423+00:00
-- url     : https://prove2.me/submissions/2de14a8f-53b5-4310-9afa-508aea7a5f4c

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferProductMonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Misc
open Formalism.FourierDecayAlt.I Finset Polynomial
namespace Formalism.FourierDecayAlt.P.Misc
theorem _root_.solution {A : Type} [Ring A] (n : ℕ) (p c ci : ℕ → A) :
    TpolyProd (n + 1) p c ci = Tpoly (p (n + 1)) (c (n + 1)) (ci (n + 1)) * TpolyProd n p c ci := by
  rw [TpolyProd, TpolyProd, List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  simp [List.prod_cons]
end Formalism.FourierDecayAlt.P.Misc
