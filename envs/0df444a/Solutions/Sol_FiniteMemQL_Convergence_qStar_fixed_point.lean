-- Prove2me | solution 1 for FiniteMemQL.Convergence.qStar_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T03:53:35.678475+00:00
-- url     : https://prove2.me/submissions/fa21d8e8-eb84-46f3-87c1-1ca029444c2c

import Mathlib
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace Aux_FMQ_fp

open FiniteMemQL.Convergence
open scoped ENNReal

lemma inf_diff {U : Type*} [Fintype U] [Nonempty U] (f g : U → ℝ) (d : ℝ)
    (h : ∀ v, |f v - g v| ≤ d) : |(⨅ v, f v) - ⨅ v, g v| ≤ d := by
  rw [abs_le]
  constructor
  · have : (⨅ v, g v) - d ≤ ⨅ v, f v := le_ciInf fun v => by
      linarith [ciInf_le (Finite.bddBelow_range g) v, (abs_le.mp (h v)).1]
    linarith
  · have : (⨅ v, f v) - d ≤ ⨅ v, g v := le_ciInf fun v => by
      linarith [ciInf_le (Finite.bddBelow_range f) v, (abs_le.mp (h v)).2]
    linarith

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

lemma normalize_univ_le (μ : Measure X) : FiniteMemQL.Convergence.normalize μ Set.univ ≤ 1 := by
  unfold FiniteMemQL.Convergence.normalize
  rw [Measure.smul_apply, smul_eq_mul]
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · rw [h0, mul_zero]; exact zero_le_one
  rcases eq_or_ne (μ Set.univ) ⊤ with ht | ht
  · rw [ht]; simp
  · rw [ENNReal.inv_mul_cancel h0 ht]

lemma predict_univ (M : POMDP X Y U) (μ : Measure X) (u : U) :
    predict M μ u Set.univ = μ Set.univ := by
  unfold predict
  have hm : Measurable (fun x => M.T (x, u)) :=
    M.T.measurable.comp (measurable_id.prodMk measurable_const)
  rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
  simp

lemma sum_correct [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U) (ν : Measure X) :
    ∑ y : Y, correct M ν y Set.univ = ν Set.univ := by
  unfold correct
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← lintegral_finset_sum _ (fun y _ => M.O.measurable_coe (measurableSet_singleton y))]
  have : ∀ x, ∑ y : Y, M.O x {y} = 1 := by
    intro x
    rw [sum_measure_singleton]
    simp
  simp only [this, lintegral_const, one_mul]

end Aux_FMQ_fp

open FiniteMemQL.Convergence Aux_FMQ_fp in
theorem solution {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    {N : ℕ} (πs : Measure X) [IsProbabilityMeasure πs] :
    ∀ (I : Window Y U N) (u : U), qStar M πs I u =
      Cstar M πs I u + M.β * ∑ y : Y, Pstar M πs I u y * ⨅ v : U, qStar M πs (shift I u y) v := by
  have hβ0 := M.β_pos
  have hβ1 := M.β_lt_one
  have hP0 : ∀ (I : Window Y U N) u y, 0 ≤ Pstar M πs I u y := fun _ _ _ => ENNReal.toReal_nonneg
  have hP1 : ∀ (I : Window Y U N) u, ∑ y : Y, Pstar M πs I u y ≤ 1 := by
    intro I u
    set ν := predict M (post M πs I) u with hν
    have hνle : ν Set.univ ≤ 1 := by
      rw [hν, predict_univ]; exact normalize_univ_le _
    have hfin : ∀ y, correct M ν y Set.univ ≠ ⊤ := by
      intro y
      have : correct M ν y Set.univ ≤ ν Set.univ := by
        rw [← sum_correct M ν]
        exact Finset.single_le_sum (f := fun y => correct M ν y Set.univ) (fun _ _ => zero_le) (Finset.mem_univ y)
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans this hνle)
    have : ∑ y : Y, Pstar M πs I u y = (∑ y : Y, correct M ν y Set.univ).toReal := by
      rw [ENNReal.toReal_sum (fun y _ => hfin y)]
      rfl
    rw [this, sum_correct]
    calc (ν Set.univ).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hνle
      _ = 1 := ENNReal.toReal_one
  set T : (Window Y U N → U → ℝ) → (Window Y U N → U → ℝ) := qBellman M πs with hT
  have hlip : ∀ Q Q', dist (T Q) (T Q') ≤ M.β * dist Q Q' := by
    intro Q Q'
    have hd0 : 0 ≤ dist Q Q' := dist_nonneg
    have hentry : ∀ J v, |Q J v - Q' J v| ≤ dist Q Q' := fun J v => by
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist (Q J) (Q' J) v).trans (dist_le_pi_dist Q Q' J)
    rw [dist_pi_le_iff (mul_nonneg hβ0.le hd0)]
    intro I
    rw [dist_pi_le_iff (mul_nonneg hβ0.le hd0)]
    intro u
    rw [Real.dist_eq]
    simp only [hT, qBellman]
    have e : (Cstar M πs I u + M.β * ∑ y : Y, Pstar M πs I u y * ⨅ v, Q (shift I u y) v) -
        (Cstar M πs I u + M.β * ∑ y : Y, Pstar M πs I u y * ⨅ v, Q' (shift I u y) v) =
        M.β * ∑ y : Y, Pstar M πs I u y * ((⨅ v, Q (shift I u y) v) - ⨅ v, Q' (shift I u y) v) := by
      rw [add_sub_add_left_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [e, abs_mul, abs_of_pos hβ0]
    apply mul_le_mul_of_nonneg_left _ hβ0.le
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ y : Y, |Pstar M πs I u y * ((⨅ v, Q (shift I u y) v) - ⨅ v, Q' (shift I u y) v)|
        ≤ ∑ y : Y, Pstar M πs I u y * dist Q Q' := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (hP0 I u y)]
          exact mul_le_mul_of_nonneg_left (inf_diff _ _ _ fun v => hentry _ v) (hP0 I u y)
      _ = (∑ y : Y, Pstar M πs I u y) * dist Q Q' := by rw [Finset.sum_mul]
      _ ≤ 1 * dist Q Q' := mul_le_mul_of_nonneg_right (hP1 I u) hd0
      _ = dist Q Q' := one_mul _
  have hK : ContractingWith (Real.toNNReal M.β) T := by
    refine ⟨by rw [Real.toNNReal_lt_one]; exact hβ1, LipschitzWith.of_dist_le_mul fun Q Q' => ?_⟩
    rw [Real.coe_toNNReal _ hβ0.le]
    exact hlip Q Q'
  set Qs := ContractingWith.fixedPoint T hK with hQs
  have htend := hK.tendsto_iterate_fixedPoint 0
  have hq : ∀ I u, qStar M πs I u = Qs I u := by
    intro I u
    unfold qStar
    apply Filter.Tendsto.limUnder_eq
    exact ((continuous_apply u).tendsto _).comp (((continuous_apply I).tendsto _).comp htend)
  have hfix : T Qs = Qs := hK.fixedPoint_isFixedPt
  intro I u
  rw [hq I u]
  have := congrFun (congrFun hfix I) u
  rw [← this]
  simp only [hT, qBellman]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  exact iInf_congr fun v => (hq _ v).symm
