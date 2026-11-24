-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.dx_repF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:58.040561+00:00
-- url     : https://prove2.me/submissions/5a94ad77-a0e0-415b-b215-4840f8b85450

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_dx_false
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {X : Mat k r} (hX : inLie k r X) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) : Dx (false, X) φ g = F' (g * X) := by
  rw [← dx_false]
  have hc := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hF0 : HasFDerivAt F F' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hF
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (F' (g * X)) 0 :=
    hF0.comp_hasDerivAt (0 : ℝ) hc
  have hU0 : U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hU.mem_nhds hgU
  have hev : (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      fun t => F (g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with t ht
    exact hff _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hg hX t)
  exact (hcomp.congr_of_eventuallyEq hev).deriv
end Formalism.FourierDecayAlt.P.JFxE
