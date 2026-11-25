-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.hypInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:13:43.95302+00:00
-- url     : https://prove2.me/submissions/27f12f3b-9b23-4ebb-bdff-69644e704ab6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__V_inv_a557543499cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key


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
theorem _root_.solution : HypInv := by
  intro k r z z' μsec μW hk hz hz' hT hT' hsec hW m hm
  have hdef : hypMeas k r z z' μsec μW =
      (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW).map
        (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z')) := rfl
  rw [hdef]
  by_cases hf : AEMeasurable (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z'))
      (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW)
  swap
  · rw [Measure.map_of_not_aemeasurable hf, Measure.map_zero]
  have : IsFiniteMeasureOnCompacts μW := ⟨fun K hK => hW.finite_compact K hK⟩
  have : SigmaFinite μW := inferInstance
  obtain ⟨c, hc0, hc1, hkey⟩ := key hk hz hz' hT hT' hsec hW hf
  have hν : (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW).map
        (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z')) = c⁻¹ • ((μW Set.univ) • σV k r (Tz k r z')) := by
    rw [← hkey, smul_smul, ENNReal.inv_mul_cancel hc0 hc1, one_smul]
  rw [hν, Measure.map_smul, Measure.map_smul, σV_inv _ hm]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
