-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.isPF_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:15:44.447974+00:00
-- url     : https://prove2.me/submissions/05c5ae82-43ee-482f-b200-17170c77ff62

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_UpperTheory_Reformulated_B_IsPFSum_isPF_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {ι : Type} (s : Finset ι) {f : ι → ℂ → A} (hf : ∀ i ∈ s, IsPF (f i)) :
    IsPF fun Y => ∑ i ∈ s, f i Y :=
  _root_.UpperTheory.Reformulated.B.IsPFSum.isPF_sum s hf
end Formalism.FourierDecayAlt.P.NFx2
