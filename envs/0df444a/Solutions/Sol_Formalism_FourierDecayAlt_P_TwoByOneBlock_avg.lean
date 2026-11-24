-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:58:50.157496+00:00
-- url     : https://prove2.me/submissions/33477993-3247-4e67-a99f-d64b5fd74367

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mulVec_meas
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock_act_meas__8cead913ce31
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__V_inv_a557543499cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWset_inv_mem_UWb

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW : Measure (Mt k r)} [SFinite μW]
    (hW : IsHaarOn (UWset k r z) μW) (T' : ℝ) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, ∫⁻ h, F (act h v) ∂μW ∂σV k r T' = μW Set.univ * ∫⁻ v, F v ∂σV k r T' := by
  have hFa : Measurable (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => F (act p.2 p.1)) :=
    hF.comp act_meas'
  rw [lintegral_lintegral_swap hFa.aemeasurable]
  have hae : ∀ᵐ h : Mt k r ∂μW, h ∈ (UWset k r z : Set (Mt k r)) := by
    rw [ae_iff]; exact hW.conc
  have : ∀ᵐ h : Mt k r ∂μW, ∫⁻ v, F (act h v) ∂σV k r T' = ∫⁻ v, F v ∂σV k r T' := by
    filter_upwards [hae] with h hh
    have hi := σV_inv T' (UWset_inv_mem_UWb hz (h := Matrix.of h) hh)
    calc ∫⁻ v, F (act h v) ∂σV k r T'
        = ∫⁻ v, F v ∂((σV k r T').map (fun v => ((Matrix.of h : Mat k r)⁻¹ : Mat k r) *ᵥ v)) :=
          (lintegral_map hF (mulVec_meas _)).symm
      _ = _ := by rw [hi]
  rw [lintegral_congr_ae this, lintegral_const, mul_comm]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
