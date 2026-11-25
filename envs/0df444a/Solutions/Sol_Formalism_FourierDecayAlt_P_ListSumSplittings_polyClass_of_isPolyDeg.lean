-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_of_isPolyDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:33:59.699159+00:00
-- url     : https://prove2.me/submissions/a5d2971a-8754-441a-9eca-b838f10590c1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_cmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution {D : ℕ} {P : Mat k r → ℂ} (hP : C2.IsPolyDeg D P) : PolyClass D P := by
  obtain ⟨q, hq, hPq⟩ := hP
  have e : P = fun g => ∑ d ∈ q.support, q.coeff d * ∏ v, (varL v g) ^ d v := by
    funext g
    rw [hPq g, MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    cases v <;> rfl
  rw [e]
  refine polyClass_sum _ _ _ fun d hd => ?_
  have hdeg : ∑ v, d v * 1 ≤ D := by
    have h1 := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
    simpa using h1.trans hq
  refine polyClass_mono hdeg (polyClass_cmul _ ?_)
  exact polyClass_prod Finset.univ (fun v => d v * 1) (fun v g => (varL v g) ^ d v)
    fun v _ => polyClass_pow (polyClass_lin (varL v)) (d v)
end Formalism.FourierDecayAlt.P.ListSumSplittings
