-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_x_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:39:29.275696+00:00
-- url     : https://prove2.me/submissions/3e29efeb-ceab-4364-9388-d8b4786547bc

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
theorem _root_.solution {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (h : M.Up P j ρ ρ') (Y : ℂ) :
    M.xC P ρ' Y = (Y + M.rho P ρ j + 1) * M.xEx P {j} ρ Y := by
  unfold M.xC M.xEx
  rw [Finset.prod_eq_mul_prod_sdiff_singleton j _ (fun h => absurd hj h)]
  congr 1
  · rw [up_rho P h j hj]; simp; ring
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_sdiff.1 hi
    rw [up_rho P h i hi'.1]
    have : i ≠ j := fun e => hi'.2 (by simp [e])
    simp [this]
end Formalism.FourierDecayAlt.P.NFx2
