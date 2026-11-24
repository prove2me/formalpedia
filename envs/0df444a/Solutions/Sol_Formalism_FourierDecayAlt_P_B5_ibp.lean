-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.ibp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:18.11685+00:00
-- url     : https://prove2.me/submissions/467b2f6e-2491-484d-82c5-83cfc2b9a9ca

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_exp_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_rdV_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_curve
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_intZero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {X : Mat k r} (hX : inLie k r X) {f1 f2 : Mat k r → (Wq →L[ℂ] Wp)}
    (h1 : CkOn 1 (GV k r) f1) (h2 : CkOn 1 (GV k r) f2)
    (i0 : Integrable (fun g : Mt k r => hsInner (f1 (Matrix.of g)) (f2 (Matrix.of g))) D.μG)
    (i1 : Integrable (fun g : Mt k r => hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g))) D.μG)
    (i2 : Integrable (fun g : Mt k r => hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g))) D.μG) :
    (∫ g : Mt k r, hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g)) ∂D.μG) =
      -∫ g : Mt k r, hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g)) ∂D.μG := by
  haveI := haar_sigmaFinite D.haarG
  set h : Mat k r → ℂ := fun g => hsInner (f1 g) (f2 g) with hh
  have hR : ∀ g ∈ GV k r, RdV X h g = hsInner (RdV X f1 g) (f2 g) + hsInner (f1 g) (RdV X f2 g) := by
    intro g hg
    have H := hs_hasDerivAt (rdV_hasDerivAt h1 hg hX) (rdV_hasDerivAt h2 hg hX)
    simp only [curve_zero] at H
    exact H.deriv
  have hae : ∀ᵐ g ∂D.μG, RdV X h (Matrix.of g) =
      hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g)) +
        hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g)) := by
    filter_upwards [haar_ae D.haarG] with g hg
    exact hR _ hg
  have hinv : ∀ t : ℝ, D.μG.map (rmulF (NormedSpace.exp ((t : ℂ) • X))) = D.μG :=
    fun t => D.haarG.right _ (exp_mem hX t)
  have hcd : ∀ᵐ g ∂D.μG, ContDiff ℝ 1 fun t : ℝ => h (Matrix.of g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [haar_ae D.haarG] with g hg
    exact hs_contDiff (ckOn_curve h1 hg hX) (ckOn_curve h2 hg hX)
  have hI : Integrable (fun g : Mt k r => RdV X h (Matrix.of g)) D.μG := by
    refine (i1.add i2).congr ?_
    filter_upwards [hae] with g hg
    rw [hg]
    rfl
  have hz := Formalism.FourierDecayAlt.P.B1.intZero _ D.μG X h hinv hcd i0 hI
  have hsplit : (∫ g : Mt k r, RdV X h (Matrix.of g) ∂D.μG) =
      (∫ g : Mt k r, hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g)) ∂D.μG) +
        ∫ g : Mt k r, hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g)) ∂D.μG := by
    rw [integral_congr_ae hae, integral_add i1 i2]
  rw [hz] at hsplit
  linear_combination (-1 : ℂ) * hsplit
end Formalism.FourierDecayAlt.P.B5
