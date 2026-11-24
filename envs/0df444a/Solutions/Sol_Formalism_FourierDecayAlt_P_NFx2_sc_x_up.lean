-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_x_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:41:45.230594+00:00
-- url     : https://prove2.me/submissions/3232350b-eff0-4eee-ad65-ff4582c14260

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {τ σ : M.Ty P} (hu : M.Up P l τ σ) (Y : ℂ) :
    M.xC P σ Y = (Y + (M.rho P τ l : ℂ) + 1) * M.xEx P {l} τ Y := by
  unfold M.xC M.xEx
  rw [← Finset.mul_prod_erase _ _ hl, Finset.sdiff_singleton_eq_erase]
  congr 1
  · rw [up_rho P hu l hl, if_pos rfl]; push_cast; ring
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [up_rho P hu i (Finset.mem_of_mem_erase hi), if_neg (Finset.ne_of_mem_erase hi), add_zero]
end Formalism.FourierDecayAlt.P.NFx2
