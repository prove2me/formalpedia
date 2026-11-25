-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.big_cell_orbit_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:44.743368+00:00
-- url     : https://prove2.me/submissions/e4e925ba-8923-4867-b726-ed1622c05026

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurableSet_Qset
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_gqDom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxA3
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.JFxA3
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : GqOm := by
  intro k r Wp Wq _ _ _ _ D
  have hnull : (volume : Measure ((Fin r → ℂ) × ℂ))
      (Set.univ ×ˢ {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    have h0 : (volume : Measure ℂ)
        {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'} = 0 := by
      apply measure_mono_null (t := Metric.sphere (0 : ℂ)
        (Real.sqrt (Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z')))
      · intro w hw
        simp only [Set.mem_setOf_eq] at hw
        simp only [Metric.mem_sphere, dist_zero_right]
        rw [← hw, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      · exact Measure.addHaar_sphere _ _ _
    rw [h0, mul_zero]
  rw [ae_restrict_iff' (Formalism.FourierDecayAlt.P.B7.measurableSet_Qset D)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq hqQ
  apply Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D
  simp only [B.Qset, Set.mem_setOf_eq] at hqQ
  unfold Formalism.QuantumDeterminants.bcWeight at hqQ
  split_ifs at hqQ with hle
  · refine ⟨?_, ?_⟩
    · intro a ha
      have hp : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r b - 2))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        rw [ha, norm_zero]
        apply zero_pow
        have := a.isLt
        unfold Formalism.QuantumDeterminants.Mdim
        omega
      rw [hp, zero_mul] at hqQ
      exact lt_irrefl _ hqQ
    · refine lt_of_le_of_ne hle ?_
      intro heq
      exact hq ⟨Set.mem_univ _, heq.symm⟩
  · exact absurd hqQ (lt_irrefl _)
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.JFxA3
