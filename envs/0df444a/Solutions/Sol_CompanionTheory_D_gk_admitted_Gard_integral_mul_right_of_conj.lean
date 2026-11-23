-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.integral_mul_right_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:45.97808+00:00
-- url     : https://prove2.me/submissions/35e87dc7-7466-450a-a82a-f30bcf465e51

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w)
    (h1 : w 1 ≠ 0) (k : G) (hk : ∀ x, w (k⁻¹ * x * k) = w x) (F : G → H) :
    ∫ x, F (x * k) ∂μ = ∫ x, F x ∂μ := by
  have hm := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
  have hemb : MeasurableEmbedding fun x : G => x * k := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hpos := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1
  have e1 : ∫ x, w (x * k) ∂μ = ∫ x, w x ∂μ := by
    rw [← integral_mul_left_eq_self (fun x => w (x * k)) k⁻¹]
    simp only [hk]
  rw [← hemb.integral_map, hm, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at e1
  have e2 : Measure.modularCharacterFun k = 1 := by
    have : ((Measure.modularCharacterFun k : NNReal) : ℝ) = 1 := by
      apply mul_right_cancel₀ hpos.ne'
      rw [e1, one_mul]
    exact_mod_cast this
  rw [← hemb.integral_map, hm, e2, one_smul]
end CompanionTheory.D.gk.admitted.Gard
