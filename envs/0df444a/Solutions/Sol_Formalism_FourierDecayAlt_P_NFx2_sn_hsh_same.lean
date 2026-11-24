-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_hsh_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:24:26.9594+00:00
-- url     : https://prove2.me/submissions/875d48b8-6e4b-4b01-a2af-54050f978c3e

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (j : ℕ) (ρ : M.Ty P) (Y : ℂ) : sn_hsh P j j ρ Y = M.xEx P {j} ρ Y := by
  unfold M.xEx sn_hsh
  refine Finset.prod_congr rfl fun i hi => ?_
  have : i ≠ j := fun e => (Finset.mem_sdiff.1 hi).2 (by simp [e])
  simp [this]
end Formalism.FourierDecayAlt.P.NFx2
