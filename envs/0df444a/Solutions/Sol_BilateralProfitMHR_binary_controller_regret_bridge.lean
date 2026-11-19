-- Prove2me | solution 1 for BilateralProfitMHR.binary_controller_regret_bridge
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T12:25:32.386055+00:00
-- url     : https://prove2.me/submissions/ba7eb882-8200-4d9c-9546-82484d6e825b

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model
import Definitions.Def_BilateralProfitMHR_BinaryControl

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BilateralProfitMHR
open BilateralProfit
private lemma ptrade_nonneg (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : 0 ≤ Ptrade D a :=
  ENNReal.toReal_nonneg

private lemma ptrade_le_one (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D] (a : ℝ × ℝ) :
    Ptrade D a ≤ 1 := by
  unfold Ptrade
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr prob_le_one

private lemma ptrade_measurable (D : Measure (ℝ × ℝ)) [SFinite D] : Measurable (Ptrade D) := by
  classical
  have hset : MeasurableSet {z : (ℝ × ℝ) × (ℝ × ℝ) | Trades z.2 z.1} :=
    (measurableSet_le measurable_snd.fst measurable_fst.fst).inter
      (measurableSet_le measurable_fst.snd measurable_snd.snd)
  have hf : Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      if Trades z.2 z.1 then (1 : ℝ≥0∞) else 0) := Measurable.ite hset measurable_const measurable_const
  have hm := (Measurable.lintegral_prod_right (ν := D)
    (f := fun a v : ℝ × ℝ => if Trades v a then (1 : ℝ≥0∞) else 0) hf).ennreal_toReal
  have he : (fun a : ℝ × ℝ => (∫⁻ v, if Trades v a then (1 : ℝ≥0∞) else 0 ∂D).toReal) = Ptrade D := by
    funext a
    unfold Ptrade
    congr 1
    have hs : MeasurableSet {v | Trades v a} :=
      (measurableSet_le measurable_fst measurable_const).inter
        (measurableSet_le measurable_const measurable_snd)
    convert! lintegral_indicator_one (μ := D) hs using 1
    simp only [Set.indicator, Pi.one_apply, mem_setOf_eq]
  rw [he] at hm
  exact hm

private lemma mu_nonneg {D : Measure (ℝ × ℝ)} {a : ℝ × ℝ} (ha : a.1 ≤ a.2) :
    0 ≤ muP D a := mul_nonneg (sub_nonneg.mpr ha) (ptrade_nonneg D a)

private lemma mu_le_ptrade {D : Measure (ℝ × ℝ)} {a : ℝ × ℝ} (ha : a ∈ unitSq) :
    muP D a ≤ Ptrade D a := by
  unfold muP
  apply mul_le_of_le_one_left (ptrade_nonneg D a)
  rcases ha with ⟨ha, hb⟩
  linarith [ha.1, hb.2]

private lemma mu_le_one {D : Measure (ℝ × ℝ)} [IsProbabilityMeasure D] {a : ℝ × ℝ}
    (ha : a ∈ unitSq) : muP D a ≤ 1 :=
  (mu_le_ptrade ha).trans (ptrade_le_one D a)

private lemma abs_mu_le_one {D : Measure (ℝ × ℝ)} [IsProbabilityMeasure D] {a : ℝ × ℝ}
    (ha : a ∈ unitSq) : |muP D a| ≤ 1 := by
  apply abs_le.mpr
  refine ⟨?_, mu_le_ptrade ha |>.trans (ptrade_le_one D a)⟩
  have hg : -1 ≤ a.2 - a.1 := by linarith [ha.1.2,ha.2.1]
  have hp := ptrade_nonneg D a
  have hP := ptrade_le_one D a
  have hm := mul_le_mul_of_nonneg_right hg hp
  unfold muP
  nlinarith


end BilateralProfitMHR

namespace BilateralProfitMHR
open BilateralProfit
variable {Ω S : Type} [MeasurableSpace Ω]
@[simp] private theorem binaryRunState_snoc (step : Ω → S → Bool → S) (sinit : Ω → S)
    (t : ℕ) (h : Fin t → Bool) (b : Bool) (ω : Ω) :
    binaryRunState step sinit (t+1) (Fin.snoc h b) ω = step ω (binaryRunState step sinit t h ω) b := by
  simp [binaryRunState]

private theorem controllerPolicy_oneBit (T : ℕ) (act : Ω → S → ℝ × ℝ) (step : Ω → S → Bool → S)
    (sinit : Ω → S) (hlegal : ∀ ω s, act ω s ∈ unitSq)
    (hmeas : ∀ t (h : Fin t → Bool), Measurable fun ω => act ω (binaryRunState step sinit t h ω)) :
    (controllerPolicy T act step sinit hlegal hmeas).OneBit := by
  intro t ω h h' he
  change act ω (binaryRunState step sinit t (fun i => (h i).1 && (h i).2) ω) =
    act ω (binaryRunState step sinit t (fun i => (h' i).1 && (h' i).2) ω)
  congr 2
  funext i
  exact he i

private def valuationBit (v a : ℝ × ℝ) : Bool := decide (Trades v a)

@[simp] private theorem feedback_product_eq_valuationBit (v a : ℝ × ℝ) :
    ((feedback v a).1 && (feedback v a).2) = valuationBit v a := by
  by_cases hs : v.1 ≤ a.1 <;> by_cases hb : a.2 ≤ v.2 <;> simp [feedback, valuationBit, Trades, hs, hb]

private def listControlState (act : S → ℝ × ℝ) (step : S → Bool → S) (s : S)
    (vs : List (ℝ × ℝ)) : S := vs.foldl (fun s v => step s (valuationBit v (act s))) s

private def listControlCost (g : (ℝ × ℝ) → ℝ≥0∞) (act : S → ℝ × ℝ) (step : S → Bool → S) :
    S → List (ℝ × ℝ) → ℝ≥0∞
  | _, [] => 0
  | s, v::vs => g (act s) + listControlCost g act step (step s (valuationBit v (act s))) vs

@[simp] private theorem listControlState_nil (act : S → ℝ × ℝ) (step : S → Bool → S) (s : S) :
    listControlState act step s [] = s := rfl

@[simp] private theorem listControlState_concat (act : S → ℝ × ℝ) (step : S → Bool → S)
    (s : S) (vs : List (ℝ × ℝ)) (v : ℝ × ℝ) :
    listControlState act step s (vs.concat v) =
      step (listControlState act step s vs) (valuationBit v (act (listControlState act step s vs))) := by
  simp [listControlState, List.concat_eq_append]

private theorem listControlCost_concat (g : (ℝ × ℝ) → ℝ≥0∞) (act : S → ℝ × ℝ)
    (step : S → Bool → S) (s : S) (vs : List (ℝ × ℝ)) (v : ℝ × ℝ) :
    listControlCost g act step s (vs.concat v) =
      listControlCost g act step s vs + g (act (listControlState act step s vs)) := by
  induction vs generalizing s with
  | nil => simp [listControlCost, listControlState]
  | cons w ws ih => simp only [List.concat_cons, listControlCost, ih, listControlState, List.foldl_cons]; ac_rfl

private lemma measurableSet_trades (a : ℝ × ℝ) : MeasurableSet {v | Trades v a} :=
  (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_const measurable_snd)

private lemma lintegral_valuationBit (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    (a : ℝ × ℝ) (A B : ℝ≥0∞) :
    (∫⁻ v, if valuationBit v a then A else B ∂D) =
      ENNReal.ofReal (Ptrade D a) * A + ENNReal.ofReal (1 - Ptrade D a) * B := by
  classical
  have he : ENNReal.ofReal (Ptrade D a) = D {v | Trades v a} :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hc : ENNReal.ofReal (1 - Ptrade D a) = D {v | Trades v a}ᶜ := by
    rw [Ptrade, ← ENNReal.toReal_one, ← ENNReal.toReal_sub_of_le prob_le_one (by simp),
      ENNReal.ofReal_toReal (by finiteness), measure_compl (measurableSet_trades a) (measure_ne_top _ _)]
    simp
  rw [he,hc]
  have hf : (fun v => if valuationBit v a then A else B) =
      {v | Trades v a}.piecewise (fun _ => A) (fun _ => B) := by
    funext v
    simp [valuationBit, Set.piecewise]
  rw [hf, lintegral_piecewise (measurableSet_trades a)]
  simp [mul_comm]

private lemma measurable_listControlCost (g : (ℝ × ℝ) → ℝ≥0∞) (act : S → ℝ × ℝ)
    (step : S → Bool → S) (n : ℕ) (s : S) :
    Measurable fun v : Fin n → ℝ × ℝ => listControlCost g act step s (List.ofFn v) := by
  induction n generalizing s with
  | zero => simp only [List.ofFn_zero, listControlCost]; exact measurable_const
  | succ n ih =>
    simp only [List.ofFn_succ, listControlCost]
    have htail : Measurable (fun v : Fin (n+1) → ℝ × ℝ => Fin.tail v) := by fun_prop
    have hset : MeasurableSet {v : Fin (n+1) → ℝ × ℝ | Trades (v 0) (act s)} :=
      (measurableSet_trades (act s)).preimage (measurable_pi_apply 0)
    have hfun : (fun v : Fin (n+1) → ℝ × ℝ =>
      listControlCost g act step (step s (valuationBit (v 0) (act s))) (List.ofFn (Fin.tail v))) =
      (fun v => if Trades (v 0) (act s) then
        listControlCost g act step (step s true) (List.ofFn (Fin.tail v)) else
        listControlCost g act step (step s false) (List.ofFn (Fin.tail v))) := by
      funext v; by_cases hv : Trades (v 0) (act s) <;> simp [valuationBit,hv]
    change Measurable (fun v : Fin (n+1) → ℝ × ℝ => g (act s) +
      listControlCost g act step (step s (valuationBit (v 0) (act s))) (List.ofFn (Fin.tail v)))
    simp_rw [congrFun hfun]
    exact measurable_const.add (Measurable.ite hset ((ih _).comp htail) ((ih _).comp htail))

private lemma lintegral_listControlCost (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    (g : (ℝ × ℝ) → ℝ≥0∞) (act : S → ℝ × ℝ) (step : S → Bool → S) (n : ℕ) (s : S) :
    (∫⁻ v, listControlCost g act step s (List.ofFn v) ∂(Measure.pi fun _ : Fin n => D)) =
      binaryValue (Ptrade D) g act step n s := by
  induction n generalizing s with
  | zero => simp [List.ofFn_zero,listControlCost,binaryValue]
  | succ n ih =>
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => D) 0).symm
    have he : (fun z : (ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ × ℝ) 0).symm z) =
        (fun z => Fin.cons z.1 z.2) := by
      funext z
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero, Fin.consEquiv]
    change (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ × ℝ) 0).symm) = _ at he
    rw [he] at hmp
    rw [← hmp.lintegral_comp (measurable_listControlCost g act step (n+1) s)]
    rw [lintegral_prod (fun z : (ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      listControlCost g act step s (List.ofFn (Fin.cons z.1 z.2)))
      ((measurable_listControlCost g act step (n+1) s).comp hmp.measurable).aemeasurable]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, listControlCost]
    simp_rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, ih]
    have hi : (fun v : ℝ × ℝ => binaryValue (Ptrade D) g act step n (step s (valuationBit v (act s)))) =
        (fun v => if valuationBit v (act s) then binaryValue (Ptrade D) g act step n (step s true)
          else binaryValue (Ptrade D) g act step n (step s false)) := by
      funext v
      cases valuationBit v (act s) <;> rfl
    simp_rw [congrFun hi]
    rw [lintegral_valuationBit]
    rfl


end BilateralProfitMHR


open MeasureTheory Set
open scoped ENNReal

namespace BilateralProfitMHR
open BilateralProfit

variable {Ω S : Type} [MeasurableSpace Ω]

private def valuationPrefix {T : ℕ} (v : Fin T → ℝ × ℝ) (t : ℕ) (ht : t ≤ T) : Fin t → ℝ × ℝ :=
  fun i => v ⟨i, i.isLt.trans_le ht⟩

private lemma ofFn_valuationPrefix_succ {T t : ℕ} (v : Fin T → ℝ × ℝ) (ht : t+1 ≤ T) :
    List.ofFn (valuationPrefix v (t+1) ht) =
      (List.ofFn (valuationPrefix v t (by omega))).concat (v ⟨t, by omega⟩) := by
  rw [List.ofFn_succ']
  rfl

private lemma listControlCost_ofFn_eq_sum (g : (ℝ × ℝ) → ℝ≥0∞) (act : S → ℝ × ℝ)
    (step : S → Bool → S) (s : S) (n : ℕ) (v : Fin n → ℝ × ℝ) :
    listControlCost g act step s (List.ofFn v) =
      ∑ t : Fin n, g (act (listControlState act step s
        (List.ofFn (valuationPrefix v t t.isLt.le)))) := by
  induction n with
  | zero => simp [listControlCost]
  | succ n ih =>
    rw [List.ofFn_succ', listControlCost_concat, ih, Fin.sum_univ_castSucc]
    congr 1

private lemma controllerPolicy_state (T : ℕ) (act : Ω → S → ℝ × ℝ) (step : Ω → S → Bool → S)
    (sinit : Ω → S) (hlegal : ∀ ω s, act ω s ∈ unitSq)
    (hmeas : ∀ t (h : Fin t → Bool), Measurable fun ω => act ω (binaryRunState step sinit t h ω))
    (ω : Ω) (v : Fin T → ℝ × ℝ) (t : ℕ) (ht : t ≤ T) :
    binaryRunState step sinit t
      (fun i => (((controllerPolicy T act step sinit hlegal hmeas).hist ω v t ht) i).1 &&
        (((controllerPolicy T act step sinit hlegal hmeas).hist ω v t ht) i).2) ω =
      listControlState (act ω) (step ω) (sinit ω) (List.ofFn (valuationPrefix v t ht)) := by
  induction t with
  | zero => simp [binaryRunState, listControlState]
  | succ t ih =>
    let π := controllerPolicy T act step sinit hlegal hmeas
    have ht' : t ≤ T := by omega
    have he : (fun i => ((π.hist ω v (t+1) ht) i).1 && ((π.hist ω v (t+1) ht) i).2) =
        Fin.snoc (fun i => ((π.hist ω v t ht') i).1 && ((π.hist ω v t ht') i).2)
          (valuationBit (v ⟨t,ht⟩) (π.price ⟨t,ht⟩ ω (π.hist ω v t ht'))) := by
      rw [Policy.hist]
      exact Fin.comp_snoc (fun z : Bool × Bool => z.1 && z.2) _ _ |>.trans
        (by rw [feedback_product_eq_valuationBit]; rfl)
    change binaryRunState step sinit (t+1) (fun i => ((π.hist ω v (t+1) ht) i).1 &&
      ((π.hist ω v (t+1) ht) i).2) ω = _
    rw [he, binaryRunState_snoc, ofFn_valuationPrefix_succ, listControlState_concat]
    change step ω (binaryRunState step sinit t _ ω)
        (valuationBit (v ⟨t,ht⟩) (act ω (binaryRunState step sinit t _ ω))) = _
    rw [ih ht']

private lemma controllerPolicy_cost_sum (T : ℕ) (g : (ℝ × ℝ) → ℝ≥0∞)
    (act : Ω → S → ℝ × ℝ) (step : Ω → S → Bool → S) (sinit : Ω → S)
    (hlegal : ∀ ω s, act ω s ∈ unitSq)
    (hmeas : ∀ t (h : Fin t → Bool), Measurable fun ω => act ω (binaryRunState step sinit t h ω))
    (ω : Ω) (v : Fin T → ℝ × ℝ) :
    (∑ t : Fin T, g ((controllerPolicy T act step sinit hlegal hmeas).runPrice ω v t)) =
      listControlCost g (act ω) (step ω) (sinit ω) (List.ofFn v) := by
  rw [listControlCost_ofFn_eq_sum]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  change act ω (binaryRunState step sinit t _ ω) = _
  rw [controllerPolicy_state T act step sinit hlegal hmeas ω v t t.isLt.le]

end BilateralProfitMHR


open MeasureTheory Set
open scoped ENNReal

namespace BilateralProfitMHR
open BilateralProfit

private lemma feedback_measurable_comp {A : Type} [MeasurableSpace A] {v a : A → ℝ × ℝ}
    (hv : Measurable v) (ha : Measurable a) : Measurable fun x => feedback (v x) (a x) := by
  apply Measurable.prodMk
  · apply measurable_to_bool
    convert measurableSet_le hv.fst ha.fst using 1
    ext x
    simp [feedback]
  · apply measurable_to_bool
    convert measurableSet_le ha.snd hv.snd using 1
    ext x
    simp [feedback]

private lemma profit_measurable_comp {A : Type} [MeasurableSpace A] {v a : A → ℝ × ℝ}
    (hv : Measurable v) (ha : Measurable a) : Measurable fun x => profit (v x) (a x) := by
  unfold profit tradeBit
  exact (ha.snd.sub ha.fst).mul (Measurable.ite
    ((measurableSet_le hv.fst ha.fst).inter (measurableSet_le ha.snd hv.snd)) measurable_const measurable_const)

private lemma mu_measurable (D : Measure (ℝ × ℝ)) [SFinite D] : Measurable (muP D) :=
  (measurable_snd.sub measurable_fst).mul (ptrade_measurable D)

variable {Ω : Type} [MeasurableSpace Ω] {T : ℕ}

private lemma Policy.measurable_price_joint (π : Policy T Ω) (t : Fin T) :
    Measurable (fun z : Ω × (Fin t → Bool × Bool) => π.price t z.1 z.2) :=
  measurable_from_prod_countable_left (fun h => π.price_measurable t h)

private lemma Policy.measurable_hist (π : Policy T Ω) (t : ℕ) (ht : t ≤ T) :
    Measurable fun z : Ω × (Fin T → ℝ × ℝ) => π.hist z.1 z.2 t ht := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have ht' : t ≤ T := by omega
    have hhist := ih ht'
    have hprice := (π.measurable_price_joint ⟨t,ht⟩).comp (measurable_fst.prodMk hhist)
    have hval := (measurable_pi_apply (⟨t,ht⟩ : Fin T)).comp
      (measurable_snd : Measurable fun z : Ω × (Fin T → ℝ × ℝ) => z.2)
    have hfb := feedback_measurable_comp hval hprice
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Policy.hist, Fin.snoc_last, Function.comp_def] using hfb
    · simpa only [Policy.hist, Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp hhist

private lemma Policy.measurable_runPrice (π : Policy T Ω) (t : Fin T) :
    Measurable fun z : Ω × (Fin T → ℝ × ℝ) => π.runPrice z.1 z.2 t :=
  (π.measurable_price_joint t).comp (measurable_fst.prodMk (π.measurable_hist t t.isLt.le))

private lemma Policy.hist_congr_before (π : Policy T Ω) (ω : Ω) (v v' : Fin T → ℝ × ℝ)
    (t : ℕ) (ht : t ≤ T)
    (hv : ∀ i : Fin T, (i : ℕ) < t → v i = v' i) : π.hist ω v t ht = π.hist ω v' t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ht' : t ≤ T := by omega
    have hh := ih ht' (fun i hi => hv i (by omega))
    simp only [Policy.hist]
    rw [hh, hv ⟨t,ht⟩ (by simp)]

private lemma Policy.runPrice_congr_before (π : Policy T Ω) (ω : Ω) (v v' : Fin T → ℝ × ℝ)
    (t : Fin T) (hv : ∀ i : Fin T, (i : ℕ) < t → v i = v' i) :
    π.runPrice ω v t = π.runPrice ω v' t := by
  unfold Policy.runPrice
  rw [π.hist_congr_before ω v v' t t.isLt.le hv]

private lemma abs_profit_le_one {v a : ℝ × ℝ} (ha : a ∈ unitSq) : |profit v a| ≤ 1 := by
  have hgap : |a.2 - a.1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [ha.1.1,ha.1.2,ha.2.1,ha.2.2]
  unfold profit tradeBit
  split_ifs <;> simpa using hgap

private lemma Policy.integrable_roundProfit (π : Policy T Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D] (t : Fin T) :
    Integrable (fun z => profit (z.2 t) (π.runPrice z.1 z.2 t)) (runLaw T P D) := by
  letI : IsProbabilityMeasure (runLaw T P D) := by unfold runLaw; infer_instance
  have hm := profit_measurable_comp ((measurable_pi_apply t).comp
    (measurable_snd : Measurable fun z : Ω × (Fin T → ℝ × ℝ) => z.2)) (π.measurable_runPrice t)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with z
  exact abs_profit_le_one (π.price_mem _ _ _)

private lemma Policy.integrable_roundMu (π : Policy T Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D] (t : Fin T) :
    Integrable (fun z => muP D (π.runPrice z.1 z.2 t)) (runLaw T P D) := by
  letI : IsProbabilityMeasure (runLaw T P D) := by unfold runLaw; infer_instance
  have hm := (mu_measurable D).comp (π.measurable_runPrice t)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with z
  exact abs_mu_le_one (π.price_mem _ _ _)

end BilateralProfitMHR


open MeasureTheory Set
open scoped ENNReal

namespace BilateralProfitMHR
open BilateralProfit

private lemma fixedProfit_eq_muP (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : fixedProfit D a = muP D a := by
  unfold fixedProfit profit muP
  rw [integral_const_mul]
  congr 1
  have he : (fun v => tradeBit v a) = {v | Trades v a}.indicator (fun _ => (1:ℝ)) := by
    funext v
    simp only [tradeBit, Set.indicator, mem_setOf_eq]
  rw [he, integral_indicator (measurableSet_trades a), integral_const]
  simp [Ptrade, Measure.real, Measure.restrict_apply, measurableSet_trades]

variable {Ω : Type} [MeasurableSpace Ω] {T : ℕ}

private lemma Policy.integrable_roundProfit_seed (π : Policy T Ω) (D : Measure (ℝ × ℝ))
    [IsProbabilityMeasure D] (ω : Ω) (t : Fin T) :
    Integrable (fun v => profit (v t) (π.runPrice ω v t)) (Measure.pi fun _ : Fin T => D) := by
  have hm := profit_measurable_comp (measurable_pi_apply t)
    ((π.measurable_runPrice t).comp ((measurable_const : Measurable (fun _ : Fin T → ℝ × ℝ => ω)).prodMk measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with v
  exact abs_profit_le_one (π.price_mem _ _ _)

private lemma Policy.integrable_roundMu_seed (π : Policy T Ω) (D : Measure (ℝ × ℝ))
    [IsProbabilityMeasure D] (ω : Ω) (t : Fin T) :
    Integrable (fun v => muP D (π.runPrice ω v t)) (Measure.pi fun _ : Fin T => D) := by
  have hm := (mu_measurable D).comp
    ((π.measurable_runPrice t).comp ((measurable_const : Measurable (fun _ : Fin T → ℝ × ℝ => ω)).prodMk measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with v
  exact abs_mu_le_one (π.price_mem _ _ _)

private lemma Policy.integral_profit_seed_eq_mu (π : Policy T Ω) (D : Measure (ℝ × ℝ))
    [IsProbabilityMeasure D] (hfixed : ∀ a, (∫ v, profit v a ∂D) = muP D a)
    (ω : Ω) (t : Fin T) :
    (∫ v, profit (v t) (π.runPrice ω v t) ∂(Measure.pi fun _ : Fin T => D)) =
      ∫ v, muP D (π.runPrice ω v t) ∂(Measure.pi fun _ : Fin T => D) := by
  cases T with
  | zero => exact Fin.elim0 t
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ × ℝ) t
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => D) t).symm
    have hF := hmp.integrable_comp_of_integrable (π.integrable_roundProfit_seed D ω t)
    have hG := hmp.integrable_comp_of_integrable (π.integrable_roundMu_seed D ω t)
    rw [← hmp.integral_comp' (fun v => profit (v t) (π.runPrice ω v t)),
      ← hmp.integral_comp' (fun v => muP D (π.runPrice ω v t))]
    rw [integral_prod_symm (fun z : (ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
        profit ((e.symm z) t) (π.runPrice ω (e.symm z) t)) hF,
      integral_prod_symm (fun z : (ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
        muP D (π.runPrice ω (e.symm z) t)) hG]
    apply integral_congr_ae
    filter_upwards with rest
    have he (b : ℝ × ℝ) :
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ × ℝ) t).symm (b,rest) =
          t.insertNth b rest := by
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    have hconst (b : ℝ × ℝ) :
        π.runPrice ω (t.insertNth b rest) t = π.runPrice ω (t.insertNth (0,0) rest) t := by
      apply π.runPrice_congr_before
      intro i hi
      rw [Fin.insertNth_apply_below (show i < t from hi),
        Fin.insertNth_apply_below (show i < t from hi)]
    dsimp only [e]
    simp_rw [he, Fin.insertNth_apply_same, hconst]
    rw [hfixed]
    simp

private lemma Policy.expProfit_eq_integral_mu (π : Policy T Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    (hfixed : ∀ a, (∫ v, profit v a ∂D) = muP D a) (t : Fin T) :
    π.expProfit P D t = ∫ z, muP D (π.runPrice z.1 z.2 t) ∂runLaw T P D := by
  have hF := π.integrable_roundProfit P D t
  have hG := π.integrable_roundMu P D t
  unfold Policy.expProfit runLaw
  rw [integral_prod _ hF, integral_prod _ hG]
  apply integral_congr_ae
  filter_upwards with ω
  exact π.integral_profit_seed_eq_mu D hfixed ω t

private lemma Policy.regret_eq_sum_mu (π : Policy T Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    (hfixed : ∀ a, (∫ v, profit v a ∂D) = muP D a) (a : ℝ × ℝ) :
    π.regret P D a = ∑ t : Fin T, (muP D a -
      ∫ z, muP D (π.runPrice z.1 z.2 t) ∂runLaw T P D) := by
  unfold Policy.regret fixedProfit
  simp_rw [hfixed, π.expProfit_eq_integral_mu P D hfixed]

end BilateralProfitMHR


open MeasureTheory Set
open scoped ENNReal

namespace BilateralProfitMHR
open BilateralProfit

variable {Ω S : Type} [MeasurableSpace Ω]

private lemma controllerPolicy_lintegral_cost (T : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D] (g : (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g)
    (act : Ω → S → ℝ × ℝ) (step : Ω → S → Bool → S) (sinit : Ω → S)
    (hlegal : ∀ ω s, act ω s ∈ unitSq)
    (hmeas : ∀ t (h : Fin t → Bool), Measurable fun ω => act ω (binaryRunState step sinit t h ω)) :
    (∫⁻ z, (∑ t : Fin T, g ((controllerPolicy T act step sinit hlegal hmeas).runPrice z.1 z.2 t))
      ∂runLaw T P D) =
      ∫⁻ ω, binaryValue (Ptrade D) g (act ω) (step ω) T (sinit ω) ∂P := by
  let π := controllerPolicy T act step sinit hlegal hmeas
  have hm : Measurable (fun z : Ω × (Fin T → ℝ × ℝ) => ∑ t : Fin T, g (π.runPrice z.1 z.2 t)) :=
    Finset.measurable_sum _ (fun t ht => hg.comp (π.measurable_runPrice t))
  unfold runLaw
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro ω
  dsimp only [π]
  simp_rw [controllerPolicy_cost_sum]
  exact lintegral_listControlCost D g (act ω) (step ω) T (sinit ω)

private lemma controllerPolicy_regret_le_binaryValue (T : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    (hfixed : ∀ a, (∫ v, profit v a ∂D) = muP D a)
    (act : Ω → S → ℝ × ℝ) (step : Ω → S → Bool → S) (sinit : Ω → S)
    (hlegal : ∀ ω s, act ω s ∈ unitSq)
    (hmeas : ∀ t (h : Fin t → Bool), Measurable fun ω => act ω (binaryRunState step sinit t h ω))
    (C : ℝ) (hC : ∀ ω s, muP D (act ω s) ≤ C) (a : ℝ × ℝ) (ha : muP D a ≤ C) :
    (controllerPolicy T act step sinit hlegal hmeas).regret P D a ≤
      (∫⁻ ω, binaryValue (Ptrade D) (fun x => ENNReal.ofReal (C - muP D x))
        (act ω) (step ω) T (sinit ω) ∂P).toReal := by
  let π := controllerPolicy T act step sinit hlegal hmeas
  letI : IsProbabilityMeasure (runLaw T P D) := by unfold runLaw; infer_instance
  have hnonneg (z : Ω × (Fin T → ℝ × ℝ)) (t : Fin T) :
      0 ≤ C - muP D (π.runPrice z.1 z.2 t) := by
    apply sub_nonneg.mpr
    exact hC z.1 _
  have hint (t : Fin T) : Integrable
      (fun z => C - muP D (π.runPrice z.1 z.2 t)) (runLaw T P D) :=
    (integrable_const C).sub (π.integrable_roundMu P D t)
  have hmeasSum : AEStronglyMeasurable
      (fun z => ∑ t : Fin T, (C - muP D (π.runPrice z.1 z.2 t))) (runLaw T P D) :=
    (integrable_finset_sum _ (fun t ht => hint t)).aestronglyMeasurable
  have hreal : (∫ z, (∑ t : Fin T, (C - muP D (π.runPrice z.1 z.2 t))) ∂runLaw T P D) =
      (∫⁻ z, (∑ t : Fin T, ENNReal.ofReal (C - muP D (π.runPrice z.1 z.2 t))) ∂runLaw T P D).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun z => Finset.sum_nonneg (fun t ht => hnonneg z t)) hmeasSum]
    congr 1
    apply lintegral_congr
    intro z
    exact ENNReal.ofReal_sum_of_nonneg (fun t ht => hnonneg z t)
  have hregret : π.regret P D a ≤
      ∫ z, (∑ t : Fin T, (C - muP D (π.runPrice z.1 z.2 t))) ∂runLaw T P D := by
    rw [π.regret_eq_sum_mu P D hfixed, integral_finset_sum _ (fun t ht => hint t)]
    apply Finset.sum_le_sum
    intro t ht
    rw [integral_sub (integrable_const C) (π.integrable_roundMu P D t)]
    simp only [integral_const, probReal_univ, one_smul]
    linarith
  apply hregret.trans_eq
  rw [hreal]
  congr 1
  exact controllerPolicy_lintegral_cost T P D (fun x => ENNReal.ofReal (C - muP D x))
    ((measurable_const.sub (mu_measurable D)).ennreal_ofReal) act step sinit hlegal hmeas

end BilateralProfitMHR

open BilateralProfitMHR BilateralProfit
theorem solution (T : ℕ) {Ω S : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    (act : Ω → S → ℝ × ℝ) (step : Ω → S → Bool → S) (sinit : Ω → S)
    (hlegal : ∀ ω s, act ω s ∈ unitSq)
    (hmeas : ∀ t (h : Fin t → Bool), Measurable fun ω => act ω (binaryRunState step sinit t h ω)) :
    (controllerPolicy T act step sinit hlegal hmeas).OneBit ∧
    ∀ C : ℝ, (∀ ω s, muP D (act ω s) ≤ C) → ∀ a : ℝ × ℝ, muP D a ≤ C →
      (controllerPolicy T act step sinit hlegal hmeas).regret P D a ≤
        (∫⁻ ω, binaryValue (Ptrade D) (fun x => ENNReal.ofReal (C - muP D x))
          (act ω) (step ω) T (sinit ω) ∂P).toReal := by
  refine ⟨controllerPolicy_oneBit T act step sinit hlegal hmeas, ?_⟩
  intro C hC a ha
  exact controllerPolicy_regret_le_binaryValue T P D (fun a => fixedProfit_eq_muP D a)
    act step sinit hlegal hmeas C hC a ha

