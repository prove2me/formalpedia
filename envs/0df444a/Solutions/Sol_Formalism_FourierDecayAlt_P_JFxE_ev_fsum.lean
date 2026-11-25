-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ev_fsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:32.756446+00:00
-- url     : https://prove2.me/submissions/4728b46f-bf34-4fbf-8836-e7cbe2247a78

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {ι : Type*} (s : Finset ι) (F : ι → AA k r E) (f : Mat k r → E) (x : Mat k r) :
    ev Eop (∑ i ∈ s, F i) f x = ∑ i ∈ s, ev Eop (F i) f x := by
  first
    | (simp [ev, LinearMap.sum_apply, Finset.sum_apply]; done)
    | (simp only [ev, LinearMap.coeFn_sum, Finset.sum_apply])
end Formalism.FourierDecayAlt.P.JFxE
