-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.family_operators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:09.939995+00:00
-- url     : https://prove2.me/submissions/a9e81c2c-a397-4881-b0b7-c39c065a2515

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_fam_differentiableAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_opL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_opL_equiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_slice

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.FamOps := by
  intro Wp Wq _ _ _ _ k r z z' π π' i Dc Φ _ _ hopen hΦ a j
  obtain ⟨hS, hFF⟩ := hΦ
  have hS' := Qx3.sf_opL (fun x hx => hx.1) a j hS
  refine ⟨hS', fun c hc => ?_⟩
  have hnear : ∀ g ∈ Dc c, ∀ᶠ c' in nhds c, c' ∈ OmX r ∧ g ∈ Dc c' := by
    intro g hg
    have hcont : Continuous fun c' : Fin r → ℂ => ((c', g) : Qx3.XX k r) := continuous_id.prodMk continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (hopen.mem_nhds (show ((c, g) : Qx3.XX k r) ∈ _ from ⟨hc, hg⟩))
  have hdiff : ∀ g ∈ Glev k r i ∩ Dc c, DifferentiableAt ℝ (fun c' => Φ c' g) c := fun g hg =>
    Qx3.fam_differentiableAt hS (x := (c, g)) ⟨hc, hg.2⟩ hg.1
  refine ⟨Qx3.sf_slice hS' hc, ?_, ?_, ?_⟩
  · intro g hg n hn
    have := Qx3.opL_equiv a j (f := fun c' => Φ c' g) (f' := fun c' => Φ c' (n * g))
      (psi k r z cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (c := c)
      (by
        filter_upwards [hnear g hg.2] with c' hc'
        exact (hFF c' hc'.1).2.1 g ⟨hg.1, hc'.2⟩ n hn) (hdiff g hg)
    exact this
  · intro g hg n hn
    have := Qx3.opL_equiv a j (f := fun c' => Φ c' g) (f' := fun c' => Φ c' (g * n))
      (psi k r z' cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (c := c)
      (by
        filter_upwards [hnear g hg.2] with c' hc'
        exact (hFF c' hc'.1).2.2.1 g ⟨hg.1, hc'.2⟩ n hn) (hdiff g hg)
    exact this
  · intro g hg h hh h' hh'
    have := Qx3.opL_equiv a j (f := fun c' => Φ c' g) (f' := fun c' => Φ c' (h * g * h'))
      ((ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (π' h')))
      (c := c)
      (by
        filter_upwards [hnear g hg.2] with c' hc'
        exact (hFF c' hc'.1).2.2.2 g ⟨hg.1, hc'.2⟩ h hh h' hh') (hdiff g hg)
    exact this
end Formalism.FourierDecayAlt.P
