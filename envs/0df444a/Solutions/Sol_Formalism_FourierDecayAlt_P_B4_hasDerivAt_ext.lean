-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.hasDerivAt_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:39:35.332955+00:00
-- url     : https://prove2.me/submissions/724fea63-2f46-41bd-a3bb-15d8e77de627

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {f f' : Mat k r → E} {U : Set (Mat k r)} {g X : Mat k r} (b : Bool)
    (hU : IsOpen U) (hg : g ∈ U) (hgG : g ∈ GV k r) (hd : DifferentiableAt ℝ f' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) (hX : inLie k r X) :
    HasDerivAt (fun t : ℝ => f (cv b X t g)) (fderiv ℝ f' g (vf b X g)) 0 := by
  have hc := cv_hasDerivAt b X g
  have h0 : cv b X 0 g = g := cv_zero b X g
  have hd' : HasFDerivAt f' (fderiv ℝ f' g) (cv b X 0 g) := by
    rw [h0]
    exact hd.hasFDerivAt
  have hcomp := hd'.comp_hasDerivAt 0 hc
  apply hcomp.congr_of_eventuallyEq
  have hcont : ContinuousAt (fun t => cv b X t g) 0 := hc.continuousAt
  have hUn : U ∈ nhds ((fun t => cv b X t g) 0) := by
    show U ∈ nhds (cv b X 0 g)
    rw [h0]
    exact hU.mem_nhds hg
  have hU' : ∀ᶠ t in nhds (0 : ℝ), cv b X t g ∈ U := hcont.preimage_mem_nhds hUn
  filter_upwards [hU'] with t ht
  exact hff _ ht (cv_mem hX hgG t)
end Formalism.FourierDecayAlt.P.B4
