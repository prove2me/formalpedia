-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.curve_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:13:40.31982+00:00
-- url     : https://prove2.me/submissions/063ed8fd-afdf-4757-8ed9-3465d685e69c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_isOpen_OmPlus
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_cv_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {g : Mat k r} (hg : g ∈ Om k r D.z D.z') (b : Bool) {X : Mat k r}
    (hX : inLie k r X) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, cv b X t g ∈ Om k r D.z D.z' := by
  have hopen : IsOpen ((fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') :=
    (isOpen_OmPlus _ _).preimage (cv_continuous b X g)
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := by
    show cv b X 0 g ∈ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'
    rw [cv_zero]; exact hg.2
  obtain ⟨ε1, hε1, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  have hg' : g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := hg
  refine ⟨ε1 / 2, by linarith, fun t ht => (⟨cv_mem hX hg'.1 t, hball ?_⟩ : cv b X t g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')⟩
  rw [Metric.mem_closedBall] at ht
  rw [Metric.mem_ball]
  linarith
end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
