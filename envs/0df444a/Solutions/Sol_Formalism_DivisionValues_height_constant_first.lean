-- Prove2me | solution 1 for Formalism.DivisionValues.height_constant_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:32.318953+00:00
-- url     : https://prove2.me/submissions/b460c648-6a1c-4495-9e85-4db28bca3252

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_dual_eq
import Theorems.Thm_Formalism_DivisionValues_successive_minimum_log
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_dual_expand
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_map_expand
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_nonneg
import Theorems.Thm_Formalism_DivisionValues_composition_norm_at_place
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_place_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open OperatorNormFrames
namespace Formalism.DivisionValues
theorem _root_.solution : HeightBoundConstant := by
  unfold HeightBoundConstant
  intro K _ _ _ n D m c Xc hXc Kj H X0 h0 P hP XQ hQ XE hE ι hι Ix J _ _ _ Qp hsup κ lam lamL
    hκ hlamL hle hspec Pt B hB hB0 pU kU hpU hkU
  have hcomp := composition_norm_at_place K m c Xc hXc Kj
  have hk : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤ ∏ j, kU j v := fun v =>
    (hcomp.1 v).trans (Finset.prod_le_prod (fun j _ => opNormAt_nonneg _ _ _ _ _ _)
      (fun j _ => hkU j v))
  have hBpos : ∀ v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B := by
    intro v
    rw [opNormAt_dual_eq (Xc 0) XE hE B v, norm_pos_iff]
    intro h0'
    apply hB0
    have hM := Matrix.toEuclideanLin.map_eq_zero_iff.mp
      (LinearMap.toContinuousLinearMap.map_eq_zero_iff.mp h0')
    have hTu : IsUnit ((XE v)ᵀ).det := by
      rw [Matrix.det_transpose]
      exact hE v
    have hP0 : pmat v B = 0 := by
      have := congrArg (fun M => ((XE v)ᵀ)⁻¹ * M * (Xc 0 v)⁻¹) hM
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hTu,
        Matrix.mul_nonsing_inv _ (hXc 0 v), Matrix.mul_one, Matrix.mul_zero,
        Matrix.zero_mul] at this
      exact this
    have hentry : ∀ i k, B (Pi.single i 1) (Pi.single k 1) = 0 := by
      intro i k
      have := congrFun (congrFun hP0 k) i
      simpa [pmat] using this
    refine LinearMap.ext fun φ => LinearMap.ext fun e' => ?_
    have hd : ∀ i, B (Pi.single i 1) e' = 0 := by
      intro i
      rw [dual_expand (B (Pi.single i 1)) e']
      simp [hentry]
    rw [map_expand B φ e']
    simp [hd]
  have hlogv : ∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2) ≤
      Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) -
        minOver (fun p => ∑ j, Real.log (lamL j p v)) := by
    intro v
    have S1 : 0 < κ v * minOver (fun p => ∏ j, lamL j p v) :=
      (successive_minimum_log Ix J (κ v) (fun j p => lamL j p v) (hκ v) fun j p => hlamL j p v).1
    have S2 : ∀ p, κ v * minOver (fun p => ∏ j, lamL j p v) ≤ κ v * ∏ j, lamL j p v :=
      (successive_minimum_log Ix J (κ v) (fun j p => lamL j p v) (hκ v) fun j p => hlamL j p v).2.1
    have S4 : Real.log (κ v * minOver (fun p => ∏ j, lamL j p v)) =
        Real.log (κ v) + minOver (fun p => ∑ j, Real.log (lamL j p v)) :=
      (successive_minimum_log Ix J (κ v) (fun j p => lamL j p v) (hκ v) fun j p => hlamL j p v).2.2.2
    have hs : ∀ p, κ v * minOver (fun p => ∏ j, lamL j p v) ≤ κ v * ∏ j, lam j p v := fun p =>
      (S2 p).trans (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun j _ => (hlamL j p v).le) (fun j _ => hle j p v)) (hκ v).le)
    have hpl := place_bound (Xc 0) (hXc 0) (Xc (Fin.last m)) (hXc (Fin.last m))
      (chainMat Kj (Fin.last m)) H X0 h0 P hP XQ hQ XE hE ι hι Qp hsup v
      (fun p => κ v * ∏ j, lam j p v) (κ v * minOver (fun p => ∏ j, lamL j p v)) S1 hs
      (fun p x hx y => hspec v p x hx y) Pt B hB (pU v) (∏ j, kU j v) (hpU v) (hk v)
    have hpos := hBpos v
    have hpUnn : 0 ≤ pU v := (opNormAt_nonneg _ _ _ _ _ _).trans (hpU v)
    have hkUnn : ∀ j, 0 ≤ kU j v := fun j => (opNormAt_nonneg _ _ _ _ _ _).trans (hkU j v)
    have hsq : 0 < Real.sqrt (κ v * minOver (fun p => ∏ j, lamL j p v)) := Real.sqrt_pos.2 S1
    have hnum : 0 < pU v * ∏ j, kU j v :=
      (div_pos_iff_of_pos_right hsq).mp (hpos.trans_le hpl)
    have hprod : 0 < ∏ j, kU j v := by
      first
        | exact pos_of_mul_pos_right hnum hpUnn
        | nlinarith [Finset.prod_nonneg fun j (_ : j ∈ Finset.univ) => hkUnn j]
    have hpUpos : 0 < pU v := by
      rcases lt_or_eq_of_le hpUnn with h | h
      · exact h
      · rw [← h, zero_mul] at hnum
        exact absurd hnum (lt_irrefl _)
    have hkUpos : ∀ j, 0 < kU j v := by
      intro j
      rcases lt_or_eq_of_le (hkUnn j) with h | h
      · exact h
      · have : ∏ j, kU j v = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h.symm
        rw [this] at hprod
        exact absurd hprod (lt_irrefl _)
    have hlogprod : ∑ j, Real.log (kU j v ^ 2) = Real.log (∏ j, kU j v ^ 2) := by
      symm
      first
        | exact Real.log_prod fun j _ => (pow_pos (hkUpos j) 2).ne'
        | exact Real.log_prod _ _ fun j _ => (pow_pos (hkUpos j) 2).ne'
    calc Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2)
        ≤ Real.log (pU v ^ 2 * (∏ j, kU j v ^ 2) / (κ v * minOver (fun p => ∏ j, lamL j p v))) := by
          apply Real.log_le_log (pow_pos hpos 2)
          have e : pU v ^ 2 * (∏ j, kU j v ^ 2) / (κ v * minOver (fun p => ∏ j, lamL j p v)) =
              (pU v * (∏ j, kU j v) / Real.sqrt (κ v * minOver (fun p => ∏ j, lamL j p v))) ^ 2 := by
            rw [div_pow, mul_pow, Real.sq_sqrt S1.le, Finset.prod_pow]
          rw [e]
          have := hpos.le
          gcongr
      _ = Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) -
            Real.log (κ v * minOver (fun p => ∏ j, lamL j p v)) := by
          rw [Real.log_div (mul_pos (pow_pos hpUpos 2)
              (Finset.prod_pos fun j _ => pow_pos (hkUpos j) 2)).ne' S1.ne',
            Real.log_mul (pow_pos hpUpos 2).ne' (Finset.prod_pos fun j _ => pow_pos (hkUpos j) 2).ne',
            ← hlogprod]
      _ = Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) -
            minOver (fun p => ∑ j, Real.log (lamL j p v)) := by
          rw [S4]
          ring
  refine ⟨hlogv, ?_⟩
  unfold Formalism.HN.htMap meanLog
  calc (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
        (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2)
      ≤ (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, (Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) -
          Real.log (κ v) - minOver (fun p => ∑ j, Real.log (lamL j p v))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hlogv v) (by positivity)
    _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        ring
end Formalism.DivisionValues
