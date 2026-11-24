-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Mv_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:14.846523+00:00
-- url     : https://prove2.me/submissions/93ef6c26-9634-429e-bcda-503299c7bbda

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kg_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kset_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution : Mv P Q 1 < ∞ := by
  have e : Mv P Q 1 = ∫⁻ p, Kf P Q 1 (gramF p.1, p.2)
      ∂((volume : Measure (Q → Q → ℂ)).prod (volume : Measure (Q → P → ℂ))) := by
    rw [lintegral_prod _ (Kg_meas 1).aemeasurable]; rfl
  rw [e]
  have hle : ∀ p : (Q → Q → ℂ) × (Q → P → ℂ), Kf P Q 1 (gramF p.1, p.2) ≤
      (Metric.closedBall (0 : (Q → Q → ℂ) × (Q → P → ℂ)) 1).indicator 1 p := by
    intro p
    by_cases h : (gramF p.1, p.2) ∈ Kset P Q 1
    · have : p ∈ Metric.closedBall (0 : (Q → Q → ℂ) × (Q → P → ℂ)) 1 := by
        rw [mem_closedBall_zero_iff]; exact Kset_bound h
      rw [Set.indicator_of_mem this]
      exact le_of_eq (Set.indicator_of_mem h _)
    · have : Kf P Q 1 (gramF p.1, p.2) = 0 := Set.indicator_of_notMem h _
      rw [this]; exact zero_le
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_indicator_one Metric.isClosed_closedBall.measurableSet]
  exact (isCompact_closedBall _ _).measure_lt_top
end Formalism.FourierDecayAlt.P.HermitianFormFactor
