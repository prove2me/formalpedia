-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.needs.vecV_cutF_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:45:25.573491+00:00
-- url     : https://prove2.me/submissions/11e140f2-fa27-4c1c-9c43-68f5dfdf03c6

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_orbJ_cutF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JCx1.needs
theorem _root_.solution (hGS : D.PtGSpec) (Bs : RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ)
    (m₀ : Mat k r) (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (f : Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), D.vecV Bs ν' m₀ (D.cutF Bs χ f ε) p = D.vecV Bs ν' m₀ f p := by
  unfold D.vecV
  split_ifs with h h'
  · have hG : 0 < Gf k r Bs.z Bs.z' h'.choose := by
      rw [← hGS k r Bs.z Bs.z' p h'.choose h.1 h'.choose_spec.2.1]
      exact h.2
    filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
    rw [orbJ_cutF, hχ.2.2 _ ((one_le_div hε.1).2 hε.2.le)]
    simp
  · simp
  · simp
end Formalism.FourierDecayAlt.P.JCx1.needs
