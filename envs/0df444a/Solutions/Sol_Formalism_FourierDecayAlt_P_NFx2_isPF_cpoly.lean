-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.isPF_cpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:19:16.599867+00:00
-- url     : https://prove2.me/submissions/d4f1aee4-d94d-43fd-87a8-328f84aa77f2

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

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
theorem _root_.solution (Q : ℂ[X]) (a : A) : IsPF fun Y => Q.eval Y • a := by
  refine ⟨Q.map (algebraMap ℂ A) * C a, fun Y => ?_⟩
  rw [ev, eval₂_mul_noncomm, eval₂_map, eval₂_C]
  · simp only [RingHom.id_comp, Algebra.smul_def]
    congr 1
    rw [← Polynomial.eval₂_at_apply]
  · intro k; exact (Algebra.commutes Y _).symm
end Formalism.FourierDecayAlt.P.NFx2
