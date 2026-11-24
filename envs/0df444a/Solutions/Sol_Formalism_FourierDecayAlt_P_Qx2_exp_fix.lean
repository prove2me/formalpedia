-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.exp_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:59:53.030215+00:00
-- url     : https://prove2.me/submissions/8fcb02ec-4dc7-404c-bfab-4b90effb90c7

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution {X : Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (hX : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  have hd : ∀ t₀ : ℝ, HasDerivAt (fun t : ℝ => evalV v (1 * NormedSpace.exp ((t : ℂ) • X))) 0 t₀ := by
    intro t₀
    have h := (evalV v).hasFDerivAt.comp_hasDerivAt t₀ (B5.curve_hasDerivAt (1 : Mx k r) X t₀)
    have e : evalV v (1 * NormedSpace.exp ((t₀ : ℂ) • X) * X) = 0 := by
      show (1 * NormedSpace.exp ((t₀ : ℂ) • X) * X) *ᵥ v = 0
      rw [← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero]
    exact h.congr_deriv e
  have hc := is_const_of_deriv_eq_zero (fun t₀ => (hd t₀).differentiableAt) (fun t₀ => (hd t₀).deriv) t 0
  have hc' : (1 * NormedSpace.exp ((t : ℂ) • X)) *ᵥ v = (1 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *ᵥ v := hc
  simpa [NormedSpace.exp_zero] using hc'
end Formalism.FourierDecayAlt.P.Qx2
