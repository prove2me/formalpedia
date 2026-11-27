-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:34.427708+00:00
-- url     : https://prove2.me/submissions/854e60c8-35e4-44bc-ab69-f5f0f753e937

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol

open CrossLearnCB
open CrossLearnCB.UCB1CL
open CrossLearnCB.UCB1CL.Supplement

/-- Theorem 8, p. 42 (per-instance form): for every algorithm `A` and every instance `S` with
stochastic rewards and contexts there is an instance with adversarial (possibly randomized,
oblivious) rewards and the same context distribution on which `A`'s expected regret against
`π_Adv` is at least its expected regret on `S` against `π_Stoc` minus `√(T log(KT))`. -/
theorem solution {K C : ℕ} [NeZero K] (T : ℕ) (G : Fin K → Fin C → Fin C → Prop)
    (hG : HasSelfLoops G) (A : Policy K C) (hA : A.IsValid) (hAm : A.IsMeasurable)
    (S : StochInstance K C) :
    ∃ V : AdvInstance K C T, V.D = S.D ∧
      stochRegret T G S A - Real.sqrt (T * Real.log (K * T)) ≤ advRegret G V A := by
        classical
        have : ∀ t, MeasureTheory.IsProbabilityMeasure (S.roundLaw t) := S.round_prob
        have hP : MeasureTheory.IsProbabilityMeasure (S.tableLaw T) := by
          unfold StochInstance.tableLaw; infer_instance
        have hcoord : ∀ (t : Fin T) (i : Fin K) (c : Fin C),
            Measurable (fun r : Fin T → Fin K → Fin C → ℝ => r t i c) := by
          intro t i c; fun_prop
        have hmap : ∀ (t : Fin T) (i : Fin K) (c : Fin C),
            MeasureTheory.Measure.map (fun r : Fin T → Fin K → Fin C → ℝ => r t i c) (S.tableLaw T)
              = S.F i c := by
          intro t i c
          have hpe := MeasureTheory.measurePreserving_eval (fun t : Fin T => S.roundLaw t) t
          unfold StochInstance.tableLaw
          calc MeasureTheory.Measure.map (fun r : Fin T → Fin K → Fin C → ℝ => r t i c)
                (MeasureTheory.Measure.pi fun t : Fin T => S.roundLaw t)
              = MeasureTheory.Measure.map (fun x : Fin K → Fin C → ℝ => x i c)
                (MeasureTheory.Measure.map (Function.eval t)
                  (MeasureTheory.Measure.pi fun t : Fin T => S.roundLaw t)) := by
                rw [MeasureTheory.Measure.map_map (by fun_prop) hpe.measurable]; rfl
            _ = MeasureTheory.Measure.map (fun x : Fin K → Fin C → ℝ => x i c) (S.roundLaw t) := by
                rw [hpe.map_eq]
            _ = S.F i c := S.round_marginal t i c
        have hsupp : ∀ᵐ r ∂(S.tableLaw T), ∀ t i c, r t i c ∈ Set.Icc (0 : ℝ) 1 := by
          rw [MeasureTheory.ae_all_iff]; intro t
          rw [MeasureTheory.ae_all_iff]; intro i
          rw [MeasureTheory.ae_all_iff]; intro c
          have h0 := S.F_supp i c
          rw [← hmap t i c, MeasureTheory.Measure.map_apply (hcoord t i c)
            measurableSet_Icc.compl] at h0
          exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h0 |>.mono (fun r hr => by
            simpa using hr)
        have hint : ∀ (t : Fin T) (i : Fin K) (c : Fin C),
            MeasureTheory.Integrable (fun r : Fin T → Fin K → Fin C → ℝ => r t i c) (S.tableLaw T) := by
          intro t i c
          refine MeasureTheory.Integrable.of_bound (hcoord t i c).aestronglyMeasurable 1 ?_
          filter_upwards [hsupp] with r hr
          have := hr t i c
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
        have hmean : ∀ (t : Fin T) (i : Fin K) (c : Fin C),
            ∫ r, r t i c ∂(S.tableLaw T) = S.mean i c := by
          intro t i c
          unfold StochInstance.mean
          rw [← hmap t i c]
          exact (MeasureTheory.integral_map (f := fun x : ℝ => x) (hcoord t i c).aemeasurable
            measurable_id.aestronglyMeasurable).symm
        -- D and A bounds
        have hD1 : ∀ c, S.D c ≤ 1 := by
          intro c; rw [← S.D_dist.2]
          exact Finset.single_le_sum (fun c _ => S.D_dist.1 c) (Finset.mem_univ c)
        have hA1 : ∀ t h c i, A t h c i ≤ 1 := by
          intro t h c i; rw [← hA.2 t h c]
          exact Finset.single_le_sum (fun i _ => hA.1 t h c i) (Finset.mem_univ i)
        have hhist : ∀ (τ : Fin T → Fin C × Fin K) (t : Fin T),
            Measurable (fun r : Fin T → Fin K → Fin C → ℝ => hist G r τ t) := by
          intro τ t
          unfold hist feedback
          refine measurable_pi_lambda _ (fun s => ?_)
          refine Measurable.prodMk measurable_const (Measurable.prodMk measurable_const ?_)
          refine measurable_pi_lambda _ (fun c' => ?_)
          by_cases hc : G (τ (Fin.castLE t.2.le s)).2 (τ (Fin.castLE t.2.le s)).1 c'
          · simp only [hc, if_true]; fun_prop
          · simp only [hc, if_false]; exact measurable_const
        have htrajm : ∀ τ, Measurable (fun r : Fin T → Fin K → Fin C → ℝ => trajProb G S.D A r τ) := by
          intro τ
          unfold trajProb
          refine Finset.measurable_prod _ (fun t _ => ?_)
          exact measurable_const.mul ((hAm t (τ t).1 (τ t).2).comp (hhist τ t))
        have htrajb : ∀ (τ : Fin T → Fin C × Fin K) (r : Fin T → Fin K → Fin C → ℝ),
            ‖trajProb G S.D A r τ‖ ≤ 1 := by
          intro τ r
          unfold trajProb
          rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun t _ =>
            mul_nonneg (S.D_dist.1 _) (hA.1 _ _ _ _)))]
          exact Finset.prod_le_one (fun t _ => mul_nonneg (S.D_dist.1 _) (hA.1 _ _ _ _))
            (fun t _ => mul_le_one₀ (hD1 _) (hA.1 _ _ _ _) (hA1 _ _ _ _))
        have hAint : MeasureTheory.Integrable (fun r => algReward G S.D A r) (S.tableLaw T) := by
          unfold algReward expect
          refine MeasureTheory.integrable_finsetSum _ (fun τ _ => ?_)
          refine MeasureTheory.Integrable.bdd_mul (c := 1) ?_ (htrajm τ).aestronglyMeasurable
            (Filter.Eventually.of_forall (htrajb τ))
          exact MeasureTheory.integrable_finsetSum _ (fun t _ => hint _ _ _)
        have hsupm : ∀ c, Measurable (fun r : Fin T → Fin K → Fin C → ℝ =>
            Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ t, r t i c)) := by
          intro c
          have := Finset.measurable_sup' (δ := Fin T → Fin K → Fin C → ℝ)
            (Finset.univ_nonempty (α := Fin K))
            (f := fun i (r : Fin T → Fin K → Fin C → ℝ) => ∑ t, r t i c)
            (fun i _ => Finset.measurable_sum _ (fun t _ => hcoord t i c))
          convert this using 1
          ext r; simp [Finset.sup'_apply]
        have hsupi : ∀ c, MeasureTheory.Integrable (fun r : Fin T → Fin K → Fin C → ℝ =>
            Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ t, r t i c)) (S.tableLaw T) := by
          intro c
          refine MeasureTheory.Integrable.of_bound (hsupm c).aestronglyMeasurable (T : ℝ) ?_
          filter_upwards [hsupp] with r hr
          rw [Real.norm_eq_abs, abs_le]
          obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin K))
            (fun i => ∑ t, r t i c)
          rw [hj]
          have h1 : ∑ t, r t j c ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum (fun t _ => (hr t j c).2)
          have h2 : ∑ _t : Fin T, (0 : ℝ) ≤ ∑ t, r t j c := Finset.sum_le_sum (fun t _ => (hr t j c).1)
          simp at h1 h2
          constructor <;> linarith
        have hBint : MeasureTheory.Integrable (fun r => exAnteBenchmark S.D r) (S.tableLaw T) := by
          unfold exAnteBenchmark
          exact MeasureTheory.integrable_finsetSum _ (fun c _ => (hsupi c).const_mul _)
        refine ⟨⟨S.D, S.tableLaw T, S.D_dist, hP, hsupp⟩, rfl, ?_⟩
        unfold advRegret exAnteRegret stochRegret
        simp only
        rw [MeasureTheory.integral_sub hBint hAint]
        have key : (T : ℝ) * ∑ c, S.D c * Finset.univ.sup' Finset.univ_nonempty (fun i => S.mean i c)
            ≤ ∫ r, exAnteBenchmark S.D r ∂(S.tableLaw T) := by
          unfold exAnteBenchmark
          rw [MeasureTheory.integral_finsetSum _ (fun c _ => (hsupi c).const_mul _), Finset.mul_sum]
          refine Finset.sum_le_sum (fun c _ => ?_)
          rw [MeasureTheory.integral_const_mul]
          obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin K))
            (fun i => S.mean i c)
          rw [hj]
          have e : (T : ℝ) * S.mean j c = ∫ r, ∑ t, r t j c ∂(S.tableLaw T) := by
            rw [MeasureTheory.integral_finsetSum _ (fun t _ => hint t j c)]
            simp [hmean]
          have hle : ∫ r, ∑ t, r t j c ∂(S.tableLaw T) ≤ ∫ r, Finset.univ.sup' Finset.univ_nonempty
              (fun i => ∑ t, r t i c) ∂(S.tableLaw T) :=
            MeasureTheory.integral_mono (MeasureTheory.integrable_finsetSum _ (fun t _ => hint t j c))
              (hsupi c) (fun r => Finset.le_sup' (fun i => ∑ t, r t i c) (Finset.mem_univ j))
          calc (T : ℝ) * (S.D c * S.mean j c) = S.D c * ((T : ℝ) * S.mean j c) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (e ▸ hle) (S.D_dist.1 c)
        have hsq := Real.sqrt_nonneg ((T : ℝ) * Real.log (K * T))
        linarith
