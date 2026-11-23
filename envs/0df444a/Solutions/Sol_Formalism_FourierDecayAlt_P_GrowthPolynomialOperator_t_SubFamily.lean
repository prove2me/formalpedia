-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_SubFamily
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:59.329863+00:00
-- url     : https://prove2.me/submissions/7a03f2e1-1500-4297-9e17-cbedc3945fc2

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_summable_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : SubFamily := by
  intro τ Rw I H H₁ _ _ _ _ _ X hA Q Q' hQ
  have hA' : Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1 := hA
  have hs := summable_abs X hA
  have hG := hA'.2.2.le
  have hb : ∀ p, ‖Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖ ≤
      Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p := by
    intro p
    by_cases hp : p ∈ Q
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.norm_eq_abs]
      first
          | exact Complex.abs_re_le_norm _
          | exact Complex.abs_re_le_abs _
          | exact RCLike.abs_re_le_norm _
    · first
        | rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
        | rw [Set.indicator_of_not_mem hp, Set.indicator_of_not_mem hp]
      simp
  have hsr : Summable (fun p : τ × τ =>
      ‖Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hb (hs.indicator Q)
  constructor
  · show X.Gam1 * _ ≤ X.Gam1 * _
    refine mul_le_mul_of_nonneg_left ?_ hG
    have hle : ∀ p, Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p ≤
        Q'.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p :=
      fun p => Set.indicator_le_indicator_of_subset hQ (fun _ => norm_nonneg _) p
    first
      | exact Summable.tsum_le_tsum hle (hs.indicator Q) (hs.indicator Q')
      | exact tsum_le_tsum hle (hs.indicator Q) (hs.indicator Q')
  · show |X.Gam1 * _| ≤ X.Gam1 * _
    rw [abs_mul, abs_of_pos hA'.2.2]
    refine mul_le_mul_of_nonneg_left ?_ hG
    calc |∑' p, Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p|
        = ‖∑' p, Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' p, ‖Q.indicator (fun p : τ × τ => (inner ℂ (X.vec p.1) (X.vec p.2)).re) p‖ :=
          norm_tsum_le_tsum_norm hsr
      _ ≤ ∑' p, Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p := by
          first
            | exact Summable.tsum_le_tsum hb hsr (hs.indicator Q)
            | exact tsum_le_tsum hb hsr (hs.indicator Q)
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
