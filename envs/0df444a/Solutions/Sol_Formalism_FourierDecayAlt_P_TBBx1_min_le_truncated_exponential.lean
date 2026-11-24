-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.min_le_truncated_exponential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:59:45.507989+00:00
-- url     : https://prove2.me/submissions/f0e6402e-ebe7-479e-b641-e10ad81c1824

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution {Λ x : ℝ} (hΛ : 0 ≤ Λ) (hΛx : Λ ≤ x) {K : ℕ} (hK : 3 ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    mn Λ K t ≤ Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff 3 x t := by
  unfold mn Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff
  split_ifs with h0
  · exact le_rfl
  · rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have ha : 0 ≤ Λ / t := div_nonneg hΛ ht
    have hab : Λ / t ≤ x / t := div_le_div_of_nonneg_right hΛx ht
    calc min 1 ((Λ / t) ^ K) ≤ min 1 ((Λ / t) ^ 3) := by
          rcases le_or_gt (Λ / t) 1 with h1 | h1
          · exact min_le_min le_rfl (pow_le_pow_of_le_one ha h1 hK)
          · rw [min_eq_left (one_le_pow₀ h1.le), min_eq_left (one_le_pow₀ h1.le)]
      _ ≤ min 1 ((x / t) ^ 3) := min_le_min le_rfl (pow_le_pow_left₀ ha hab 3)
end Formalism.FourierDecayAlt.P.TBBx1
