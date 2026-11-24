-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:14.491822+00:00
-- url     : https://prove2.me/submissions/6ad3be0d-5aa6-474a-9ffe-803d19c01f22

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.OperatorRepresentations
theorem _root_.solution : ∀ (t : ℕ) (X : Fin t → Module.End ℂ (SV k r i D E)) (T : Fin t → (Mx k r → E) → Mx k r → E),
    (∀ l, Rep (X l) (T l)) → Rep (List.ofFn X).prod (fun f => (List.ofFn T).foldr (fun T h => T h) f)
  | 0, _, _, _ => by
    simpa only [List.ofFn_zero, List.prod_nil, List.foldr_nil] using rep_one
  | t + 1, X, T, h => by
    have := (h 0).mul (solution t (fun l => X l.succ) (fun l => T l.succ) fun l => h l.succ)
    simpa only [List.ofFn_succ, List.prod_cons, List.foldr_cons] using this
end Formalism.FourierDecayAlt.P.OperatorRepresentations
