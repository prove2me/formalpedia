-- Prove2me | solution 1 for ContinuousMapCalculus.volterra_residual_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:22:38.274977+00:00
-- url     : https://prove2.me/submissions/5cb76547-c6ea-4107-b29a-ca3713e2a03a

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Ring.Units
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ContinuousMapCalculus

universe u v w
variable {K : Type v} {E : Type u} {F : Type w} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous field of linear operators acts pointwise on continuous maps. -/
noncomputable def pointwiseOperator (A : C(K,E →L[ℝ] F)) : C(K,E) →L[ℝ] C(K,F) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun k => A k (v k), A.continuous.clm_apply v.continuous⟩
      map_add' := fun v w => by ext k; simp
      map_smul' := fun c v => by ext k; simp }
    ‖A‖ (by
      intro v
      change ‖(⟨fun k => A k (v k), A.continuous.clm_apply v.continuous⟩ : C(K,F))‖ ≤ ‖A‖ * ‖v‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg v))).mpr
      intro k
      exact (A k).le_opNorm (v k) |>.trans
        (mul_le_mul (A.norm_coe_le_norm k) (v.norm_coe_le_norm k)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem pointwiseOperator_apply (A : C(K,E →L[ℝ] F)) (v : C(K,E)) (k : K) :
    pointwiseOperator A v k = A k (v k) := rfl

theorem norm_pointwiseOperator_le (A : C(K,E →L[ℝ] F)) :
    ‖pointwiseOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg v))).mpr
  intro k
  exact (A k).le_opNorm (v k) |>.trans
    (mul_le_mul (A.norm_coe_le_norm k) (v.norm_coe_le_norm k)
      (norm_nonneg _) (norm_nonneg _))

/-- Lifting an operator field is itself a bounded linear operation. -/
noncomputable def pointwiseOperatorCLM :
    C(K,E →L[ℝ] F) →L[ℝ] (C(K,E) →L[ℝ] C(K,F)) :=
  LinearMap.mkContinuous
    { toFun := fun (A : C(K,E →L[ℝ] F)) => pointwiseOperator A
      map_add' := fun A B => by ext v k; simp
      map_smul' := fun c A => by ext v k; simp }
    1 (by intro A; simpa using norm_pointwiseOperator_le A)


end ContinuousMapCalculus


open Set MeasureTheory
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ContinuousMapCalculus

abbrev UnitInterval := Icc (0 : ℝ) 1

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

noncomputable def extendUnitInterval (f : C(UnitInterval,V)) : C(ℝ,V) :=
  f.comp ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩

@[simp] theorem extendUnitInterval_apply (f : C(UnitInterval,V)) (t : UnitInterval) :
    extendUnitInterval f t = f t := by
  simp [extendUnitInterval, projIcc, t.property.1, t.property.2]

/-- Variable-upper-endpoint integration, as a curve on the unit interval. -/
noncomputable def primitive (f : C(UnitInterval,V)) : C(UnitInterval,V) :=
  ⟨fun t => ∫ s in 0..(t:ℝ), extendUnitInterval f s,
    ((intervalIntegral.differentiable_integral_of_continuous
      (extendUnitInterval f).continuous).continuous.comp continuous_subtype_val)⟩

theorem norm_primitive_le (f : C(UnitInterval,V)) : ‖primitive f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  change ‖∫ s in 0..(t:ℝ), extendUnitInterval f s‖ ≤ ‖f‖
  calc
    _ ≤ ‖f‖ * |(t:ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s _ => f.norm_coe_le_norm _)
    _ ≤ ‖f‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg _) t.property.2

/-- Integration from zero has operator norm at most one in the supremum norm. -/
noncomputable def primitiveCLM : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V) :=
  LinearMap.mkContinuous
    { toFun := fun (f : C(UnitInterval,V)) => primitive f
      map_add' := fun f g => by
        ext t
        exact intervalIntegral.integral_add
          ((extendUnitInterval f).continuous.intervalIntegrable 0 t)
          ((extendUnitInterval g).continuous.intervalIntegrable 0 t)
      map_smul' := fun c f => by
        ext t
        exact intervalIntegral.integral_smul c _ }
    1 (by intro f; simpa using norm_primitive_le f)

theorem norm_primitiveCLM_le : ‖(primitiveCLM : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖primitive f‖ ≤ 1 * ‖f‖
  simpa using norm_primitive_le f

end ContinuousMapCalculus

namespace ContinuousMapCalculus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

noncomputable def weightOperator (c : ℝ) : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V) :=
  LinearMap.mkContinuous
    { toFun := fun (f : C(UnitInterval,V)) =>
        ⟨fun s => Real.exp (c * s) • f s,
          (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul f.continuous⟩
      map_add' := fun f g => by ext s; exact smul_add _ _ _
      map_smul' := fun a f => by ext s; exact smul_comm _ _ _ }
    (Real.exp |c|) (by
      intro f
      change ‖(⟨fun s => Real.exp (c * s) • f s, _⟩ : C(UnitInterval,V))‖ ≤ Real.exp |c| * ‖f‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le (norm_nonneg f))).mpr
      intro s
      change ‖Real.exp (c * s) • f s‖ ≤ Real.exp |c| * ‖f‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul _ (f.norm_coe_le_norm s) (norm_nonneg _) (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      calc
        c * (s:ℝ) ≤ |c| * (s:ℝ) := mul_le_mul_of_nonneg_right (le_abs_self c) s.property.1
        _ ≤ |c| := mul_le_of_le_one_right (abs_nonneg _) s.property.2)

@[simp] theorem weightOperator_apply (c : ℝ) (f : C(UnitInterval,V)) (s : UnitInterval) :
    weightOperator c f s = Real.exp (c * s) • f s := rfl

theorem weightOperator_mul_neg (c : ℝ) :
    weightOperator c * weightOperator (-c) =
      ContinuousLinearMap.id ℝ C(UnitInterval,V) := by
  ext f s
  simp only [ContinuousLinearMap.mul_apply, weightOperator_apply, smul_smul,
    ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, one_smul,
    ContinuousLinearMap.id_apply]

noncomputable def weightUnit (c : ℝ) : (C(UnitInterval,V) →L[ℝ] C(UnitInterval,V))ˣ where
  val := weightOperator c
  inv := weightOperator (-c)
  val_inv := weightOperator_mul_neg c
  inv_val := by
    change weightOperator (-c) * weightOperator c = ContinuousLinearMap.id ℝ C(UnitInterval,V)
    simpa only [neg_neg] using weightOperator_mul_neg (V := V) (-c)

/-- A Volterra operator conjugated by an exponential weight. -/
noncomputable def weightedVolterra (A : C(UnitInterval,V →L[ℝ] V)) (c : ℝ) :
    C(UnitInterval,V) →L[ℝ] C(UnitInterval,V) :=
  (weightOperator (-c)).comp
    (primitiveCLM.comp ((pointwiseOperator A).comp (weightOperator c)))

theorem weightedVolterra_norm_le (A : C(UnitInterval,V →L[ℝ] V))
    (c : ℝ) (hc : 0 < c) : ‖weightedVolterra A c‖ ≤ ‖A‖ / c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg A) hc.le)
  intro f
  apply (ContinuousMap.norm_le _
    (mul_nonneg (div_nonneg (norm_nonneg A) hc.le) (norm_nonneg f))).mpr
  intro t
  change ‖Real.exp ((-c) * t) •
      ∫ s in 0..(t:ℝ), extendUnitInterval (pointwiseOperator A (weightOperator c f)) s‖ ≤
    (‖A‖ / c) * ‖f‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hi : ‖∫ s in 0..(t:ℝ),
      extendUnitInterval (pointwiseOperator A (weightOperator c f)) s‖ ≤
      ∫ s in 0..(t:ℝ), ‖A‖ * ‖f‖ * Real.exp (c * s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
    · apply Filter.Eventually.of_forall
      intro s hs
      have hsI : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le, hs.2.trans t.property.2⟩
      rw [show extendUnitInterval (pointwiseOperator A (weightOperator c f)) s =
          A ⟨s,hsI⟩ (Real.exp (c*s) • f ⟨s,hsI⟩) from extendUnitInterval_apply _ ⟨s,hsI⟩]
      calc
        _ ≤ ‖A ⟨s,hsI⟩‖ * ‖Real.exp (c*s) • f ⟨s,hsI⟩‖ :=
          (A ⟨s,hsI⟩).le_opNorm _
        _ ≤ ‖A‖ * (Real.exp (c*s) * ‖f‖) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul (A.norm_coe_le_norm _) (mul_le_mul_of_nonneg_left
            (f.norm_coe_le_norm _) (Real.exp_pos _).le) (by positivity) (norm_nonneg A)
        _ = _ := by ring
    · exact (continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have he : (∫ s in 0..(t:ℝ), ‖A‖ * ‖f‖ * Real.exp (c*s)) =
      ‖A‖ * ‖f‖ * (c⁻¹ * (Real.exp (c*t) - 1)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hc.ne',
      integral_exp]
    simp
  calc
    _ ≤ Real.exp ((-c)*t) * (∫ s in 0..(t:ℝ), ‖A‖ * ‖f‖ * Real.exp (c*s)) :=
      mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
    _ = (‖A‖ / c) * ‖f‖ * (1 - Real.exp ((-c)*t)) := by
      rw [he]
      have hexp : Real.exp ((-c)*(t:ℝ)) * Real.exp (c*t) = 1 := by
        rw [← Real.exp_add]; simp
      simp only [div_eq_mul_inv]
      calc
        _ = ‖A‖ * c⁻¹ * ‖f‖ *
            (Real.exp ((-c)*t) * Real.exp (c*t) - Real.exp ((-c)*t)) := by ring
        _ = _ := by rw [hexp]
    _ ≤ (‖A‖ / c) * ‖f‖ := by
      apply mul_le_of_le_one_right (by positivity)
      linarith [Real.exp_pos ((-c)*(t:ℝ))]

theorem invertible_volterra_operator (A : C(UnitInterval,V →L[ℝ] V)) :
    (ContinuousLinearMap.id ℝ C(UnitInterval,V) -
      primitiveCLM.comp (pointwiseOperator A)).IsInvertible := by
  let c : ℝ := ‖A‖ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let B := weightedVolterra A c
  have hB : ‖B‖ < 1 := by
    refine (weightedVolterra_norm_le A c hc).trans_lt ?_
    apply (div_lt_one hc).mpr
    dsimp [c]
    linarith
  let w := weightUnit (V := V) c
  let u := w * Units.oneSub B hB * w⁻¹
  refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
  change (u : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V)) = _
  let L := primitiveCLM.comp (pointwiseOperator A)
  have hb : B = (w⁻¹ : (C(UnitInterval,V) →L[ℝ] C(UnitInterval,V))ˣ) * L * w := by
    ext f s
    rfl
  change (w : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V)) *
    (Units.oneSub B hB : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V)) *
    (w⁻¹ : (C(UnitInterval,V) →L[ℝ] C(UnitInterval,V))ˣ) = 1 - L
  rw [Units.val_oneSub, hb]
  have hwinv : (w : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V)) * ↑w⁻¹ = 1 := by
    exact w.val_inv
  rw [mul_sub, sub_mul, mul_one, ← mul_assoc, ← mul_assoc, hwinv, one_mul,
    mul_assoc, hwinv, mul_one]

end ContinuousMapCalculus

open ContinuousMapCalculus

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : C(Icc (0 : ℝ) 1,V →L[ℝ] V))
    (L : C(Icc (0 : ℝ) 1,V) →L[ℝ] C(Icc (0 : ℝ) 1,V))
    (hL : ∀ γ s, L γ s = ∫ r in 0..(s:ℝ),
      A (projIcc 0 1 zero_le_one r) (γ (projIcc 0 1 zero_le_one r))) :
    (ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) 1,V) - L).IsInvertible := by
  have he : L = primitiveCLM.comp (pointwiseOperator A) := by
    ext γ s
    exact hL γ s
  rw [he]
  exact ContinuousMapCalculus.invertible_volterra_operator A
