-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.real_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:40.04529+00:00
-- url     : https://prove2.me/submissions/846eb7e8-8942-44b0-bf0f-7102850b06b2

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_mono


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
theorem _root_.solution : {Y : ℂ | star Y = Y}.Infinite := by
  have : Set.range (fun x : ℝ => (x : ℂ)) ⊆ {Y : ℂ | star Y = Y} := by
    rintro _ ⟨x, rfl⟩; simp [Complex.conj_ofReal]
  exact (Set.infinite_range_of_injective Complex.ofReal_injective).mono this
end Formalism.FourierDecayAlt.P.NFx2
