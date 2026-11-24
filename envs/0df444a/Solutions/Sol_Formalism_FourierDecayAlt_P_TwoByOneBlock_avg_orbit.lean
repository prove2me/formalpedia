-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.avg_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:38.881783+00:00
-- url     : https://prove2.me/submissions/a757327b-ddc6-4a05-a1ce-59a96a338c32

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_act_meas_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_act_lmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_GV_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)}
    (hW : IsHaarOn (UWset k r z) μW) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F)
    {h₁ : Mat k r} (hh₁ : h₁ ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    ∫⁻ h, F (act h v) ∂μW = ∫⁻ h, F (act h (h₁ *ᵥ v)) ∂μW := by
  have hunit := GV_unit hh₁.1
  have hF2 : Measurable (fun y : Mt k r => F (act y (h₁ *ᵥ v))) :=
    hF.comp (act_meas_left _)
  have hlc : Continuous (lmulM h₁ : Mt k r → Mt k r) := by
    unfold lmulM
    exact (continuous_const (y := h₁)).matrix_mul (continuous_id (X := Mat k r))
  have hlm : Measurable (lmulM h₁ : Mt k r → Mt k r) := hlc.measurable
  conv_rhs => rw [← hW.left h₁ hh₁]
  rw [lintegral_map hF2 hlm]
  refine lintegral_congr fun h => ?_
  rw [act_lmul hunit]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
