-- Prove2me | solution 1 for Formalism.L2.Th1.C.CompactOperatorsAlt.int_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:35:27.247541+00:00
-- url     : https://prove2.me/submissions/f0cc6a13-ceff-4e98-b8cf-bbdf66c2acb2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_below_mul
import Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_below_subst
import Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_below_shift
import Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_coeff_of_sq
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_of_mul_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.CompactOperatorsAlt
variable {K : Type} [Field K] {R : Subring K}
namespace Formalism.L2.Th1.C.CompactOperatorsAlt
theorem _root_.solution {A V g : PowerSeries K} {al : K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hA : IntPS R A) (hV : IsOneUnit R V) (hal : al ∈ R) (hg0 : constantCoeff g = 1)
    (hEq : A.subst (C al * X * g) = g * g * V) : IntPS R g := by
  have hne : constantCoeff V ≠ 0 := by rw [hV.1]; exact one_ne_zero
  have hinv : V * V⁻¹ = 1 := PowerSeries.mul_inv_cancel V hne
  have hW : IntPS R V⁻¹ := USideA.intPS_of_mul_eq_one hV.2 hV.1 hinv
  have hgg : g * g = A.subst (C al * X * g) * V⁻¹ := by
    rw [hEq, mul_assoc, hinv, mul_one]
  have ha0 : constantCoeff (C al * X * g) = 0 := by simp
  have key : ∀ n, ∀ m < n, coeff m g ∈ R := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
      · exact ih m h
      · subst h
        refine coeff_of_sq h2 h20 hg0 ih ?_
        rw [hgg]
        exact below_mul (below_subst hA ha0 (below_shift hal ih)) (fun k _ => hW k) m
          (Nat.lt_succ_self m)
  exact fun n => key (n + 1) n (Nat.lt_succ_self n)
end Formalism.L2.Th1.C.CompactOperatorsAlt
