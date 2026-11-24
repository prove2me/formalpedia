-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_xEx_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:39:28.571799+00:00
-- url     : https://prove2.me/submissions/a509aa7b-14e4-41e4-921e-df2b0555bbfe

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_rho

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
theorem _root_.solution {j : ℕ} {ρ ρ' : M.Ty P} (h : M.Up P j ρ ρ') (l : ℕ) (Y : ℂ) :
    M.xEx P {l} ρ' Y = sn_hsh P l j ρ Y := by
  unfold M.xEx sn_hsh
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [up_rho P h i (Finset.mem_sdiff.1 hi).1]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.NFx2
