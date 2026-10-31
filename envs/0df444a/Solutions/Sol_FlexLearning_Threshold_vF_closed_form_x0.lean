-- Prove2me | solution 1 for FlexLearning.Threshold.vF_closed_form_x0
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:48:11.008047+00:00
-- url     : https://prove2.me/submissions/dc1525f0-90ed-4e55-bcac-93b1ad413e4c

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model
import Theorems.Thm_FlexLearning_Threshold_lemma_3

open FlexLearning.Threshold MeasureTheory ProbabilityTheory

namespace FlexLAuxP

noncomputable def ps (r : ℝ) : ℝ := (max r 0) ^ 2 / 2
noncomputable def Ps (r : ℝ) : ℝ := (max r 0) ^ 3 / 6

lemma ps_cont : Continuous ps := by
  unfold ps; fun_prop

lemma prior_integral (x U : ℝ) (hU : 0 < U) (f : ℝ → ℝ) :
    ∫ d, f d ∂(prior x U) = U⁻¹ * ∫ d in x..x + U, f d := by
  unfold prior
  rw [integral_smul_measure, intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc]
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal hU.le]

lemma int_min (x U Q : ℝ) (hU : 0 < U) :
    ∫ d in x..x + U, min d Q =
      if Q ≤ x then Q * U
      else if Q ≤ x + U then x * U + (Q - x) * U - (Q - x) ^ 2 / 2
      else x * U + U ^ 2 / 2 := by
  split_ifs with h1 h2
  · rw [intervalIntegral.integral_congr (g := fun _ => Q)]
    · simp; ring
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      simp only
      exact min_eq_right (by linarith [hd.1])
  · have hc : Continuous fun d : ℝ => min d Q := continuous_id.min continuous_const
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := Q)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (g := fun d => d) (a := x) (b := Q),
      intervalIntegral.integral_congr (g := fun _ => Q) (a := Q) (b := x + U)]
    · simp [integral_id]; ring
    · intro d hd
      rw [Set.uIcc_of_le h2] at hd
      exact min_eq_right hd.1
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      exact min_eq_left hd.2
  · rw [intervalIntegral.integral_congr (g := fun d => d)]
    · simp [integral_id]; ring
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      exact min_eq_left (by linarith [hd.2])

lemma int_min' (x U Q : ℝ) (hU : 0 < U) :
    ∫ d in x..x + U, min d Q = x * U + U ^ 2 / 2 - ps (x + U - Q) + ps (x - Q) := by
  rw [int_min x U Q hU]
  unfold ps
  split_ifs with h1 h2
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring

lemma int_ps (α β : ℝ) (h : α ≤ β) : ∫ r in α..β, ps r = Ps β - Ps α := by
  unfold ps Ps
  rcases le_total β 0 with hb | hb
  · rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · rw [max_eq_right hb, max_eq_right (by linarith)]; simp
    · intro r hr
      rw [Set.uIcc_of_le h] at hr
      simp only; rw [max_eq_right (by linarith [hr.2])]; ring
  rcases le_total 0 α with ha | ha
  · rw [intervalIntegral.integral_congr (g := fun r => r ^ 2 / 2)]
    · rw [max_eq_left hb, max_eq_left ha, intervalIntegral.integral_div, integral_pow]; ring
    · intro r hr
      rw [Set.uIcc_of_le h] at hr
      simp only; rw [max_eq_left (by linarith [hr.1])]
  · have hc : Continuous fun r : ℝ => (max r 0) ^ 2 / 2 := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (a := α) (b := 0),
      intervalIntegral.integral_congr (g := fun r => r ^ 2 / 2) (a := 0) (b := β)]
    · rw [max_eq_left hb, max_eq_right ha, intervalIntegral.integral_div, integral_pow]
      simp; ring
    · intro r hr
      rw [Set.uIcc_of_le hb] at hr
      simp only; rw [max_eq_left hr.1]
    · intro r hr
      rw [Set.uIcc_of_le ha] at hr
      simp only; rw [max_eq_right hr.2]; ring

lemma int_ps_shift (α β k : ℝ) (h : α ≤ β) :
    ∫ r in α..β, ps (r + k) = Ps (β + k) - Ps (α + k) := by
  rw [intervalIntegral.integral_comp_add_right ps k, int_ps _ _ (by linarith)]

lemma prior_prob (x U : ℝ) (hU : 0 < U) : IsProbabilityMeasure (prior x U) := by
  constructor
  unfold prior
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, smul_eq_mul]
  have : ENNReal.ofReal (x + U - x) = ENNReal.ofReal U := by congr 1; ring
  rw [this, ENNReal.inv_mul_cancel (by simp [hU]) ENNReal.ofReal_ne_top]

lemma prior2_integrable (x U : ℝ) (hU : 0 < U) (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    Integrable F (prior2 x U) := by
  unfold prior2 prior
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict,
    ← Measure.volume_eq_prod]
  exact ((hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).smul_measure
    (by simp [hU])).smul_measure (by simp [hU])

lemma sales_eq (Q a b : ℝ) (hb : 0 ≤ b) :
    salesF1 Q (a, b) + salesF2 Q (a, b) = min (a + b) Q := by
  unfold salesF1 salesF2
  simp only
  rcases le_total a Q with h | h
  · rw [min_eq_left h]
    rcases le_total b (Q - a) with h' | h'
    · rw [min_eq_left h', min_eq_left (by linarith)]
    · rw [min_eq_right h', min_eq_right (by linarith)]; ring
  · rw [min_eq_right h, sub_self, min_eq_right hb, min_eq_right (by linarith)]; ring

lemma inner_eq (x U Q a : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (p : ℝ) :
    ∫ b, (p * salesF1 Q (a, b) + p * salesF2 Q (a, b)) ∂(prior x U) =
      p * (a + x + U / 2 - (ps (a + (x + U - Q)) - ps (a + (x - Q))) / U) := by
  rw [prior_integral x U hU]
  rw [intervalIntegral.integral_congr (g := fun b => p * a + p * min b (Q - a))]
  · rw [intervalIntegral.integral_add (f := fun _ => p * a) (g := fun b => p * min b (Q - a))
      intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul p (fun b => min b (Q - a)), int_min' x U (Q - a) hU]
    have e1 : x + U - (Q - a) = a + (x + U - Q) := by ring
    have e2 : x - (Q - a) = a + (x - Q) := by ring
    rw [e1, e2]
    simp
    field_simp
    ring
  · intro b hb
    rw [Set.uIcc_of_le (by linarith)] at hb
    simp only
    rw [← mul_add, sales_eq Q a b (by linarith [hb.1])]
    rw [← mul_add]
    congr 1
    rcases le_total (a + b) Q with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
    · rw [min_eq_right h, min_eq_right (by linarith)]; ring

lemma piF_formula (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) :
    piF p x U cF Q = p * (2 * x + U -
      (Ps (2 * x + 2 * U - Q) - 2 * Ps (2 * x + U - Q) + Ps (2 * x - Q)) / U ^ 2) - cF * Q := by
  unfold piF
  have := prior_prob x U hU
  have hF : Continuous fun d : ℝ × ℝ => p * salesF1 Q d + p * salesF2 Q d := by
    unfold salesF1 salesF2; fun_prop
  rw [prior2, integral_prod _ (by simpa [prior2] using prior2_integrable x U hU _ hF)]
  simp_rw [inner_eq x U Q _ hx hU p]
  rw [prior_integral x U hU]
  have hc1 : Continuous fun a : ℝ => ps (a + (x + U - Q)) := ps_cont.comp (by fun_prop)
  have hc2 : Continuous fun a : ℝ => ps (a + (x - Q)) := ps_cont.comp (by fun_prop)
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (f := fun a : ℝ => a + x + U / 2)
      (g := fun a => (ps (a + (x + U - Q)) - ps (a + (x - Q))) / U)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (((hc1.sub hc2).div_const U).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (f := fun a => ps (a + (x + U - Q)))
    (g := fun a => ps (a + (x - Q))) (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), int_ps_shift _ _ _ (by linarith),
    int_ps_shift _ _ _ (by linarith)]
  rw [intervalIntegral.integral_add (f := fun a : ℝ => a + x) (Continuous.intervalIntegrable (by fun_prop) _ _)
    intervalIntegrable_const, intervalIntegral.integral_add (f := fun a : ℝ => a)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    intervalIntegrable_const, integral_id]
  simp
  have e1 : x + U + (x + U - Q) = 2 * x + 2 * U - Q := by ring
  have e2 : x + (x + U - Q) = 2 * x + U - Q := by ring
  have e3 : x + U + (x - Q) = 2 * x + U - Q := by ring
  have e4 : x + (x - Q) = 2 * x - Q := by ring
  rw [e1, e2, e3, e4]
  field_simp
  ring


lemma reg0 (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hQ : Q ≤ 2 * x) :
    piF p x U cF Q = (p - cF) * Q := by
  rw [piF_formula p x U cF Q hx hU]; unfold Ps
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
  field_simp; ring

lemma reg1 (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hQ : 2 * x ≤ Q) (hQ' : Q ≤ 2 * x + U) :
    piF p x U cF Q = p * (Q - (Q - 2 * x) ^ 3 / (6 * U ^ 2)) - cF * Q := by
  rw [piF_formula p x U cF Q hx hU]; unfold Ps
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
  field_simp; ring

lemma reg2 (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hQ : 2 * x + U ≤ Q)
    (hQ' : Q ≤ 2 * x + 2 * U) :
    piF p x U cF Q = p * (2 * x + U - (2 * x + 2 * U - Q) ^ 3 / (6 * U ^ 2)) - cF * Q := by
  rw [piF_formula p x U cF Q hx hU]; unfold Ps
  rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  field_simp; ring

lemma reg3 (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hQ : 2 * x + 2 * U ≤ Q) :
    piF p x U cF Q = p * (2 * x + U) - cF * Q := by
  rw [piF_formula p x U cF Q hx hU]; unfold Ps
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  field_simp; ring

end FlexLAuxP

namespace FlexLAuxW

lemma prior_integral (x U : ℝ) (hU : 0 < U) (f : ℝ → ℝ) :
    ∫ d, f d ∂(prior x U) = U⁻¹ * ∫ d in x..x + U, f d := by
  unfold prior
  rw [integral_smul_measure, intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc]
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal hU.le]

lemma prior_prob (x U : ℝ) (hU : 0 < U) : IsProbabilityMeasure (prior x U) := by
  constructor
  unfold prior
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, smul_eq_mul]
  have : ENNReal.ofReal (x + U - x) = ENNReal.ofReal U := by congr 1; ring
  rw [this, ENNReal.inv_mul_cancel (by simp [hU]) ENNReal.ofReal_ne_top]

lemma prior_integrable (x U : ℝ) (hU : 0 < U) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f (prior x U) := by
  unfold prior
  exact (hf.continuousOn.integrableOn_Icc).smul_measure (by simp [hU])

/-- conditioning the uniform prior on a stock-out at `q`. -/
lemma cond_prior (x U q : ℝ) (hU : 0 < U) (hq : q < x + U) :
    (prior x U)[|Set.Ici q] = prior (max q x) (x + U - max q x) := by
  have hI : Set.Icc x (x + U) ∩ Set.Ici q = Set.Icc (max q x) (x + U) := by
    ext d; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici, max_le_iff]; tauto
  have hpos : 0 < x + U - max q x := by
    rcases le_total q x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hmeas : prior x U (Set.Ici q) = (ENNReal.ofReal U)⁻¹ * ENNReal.ofReal (x + U - max q x) := by
    unfold prior
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ici, Set.inter_comm, hI,
      Real.volume_Icc, smul_eq_mul]
  have hres : (prior x U).restrict (Set.Ici q) =
      (ENNReal.ofReal U)⁻¹ • volume.restrict (Set.Icc (max q x) (x + U)) := by
    unfold prior
    rw [Measure.restrict_smul, Measure.restrict_restrict measurableSet_Ici, Set.inter_comm, hI]
  unfold ProbabilityTheory.cond
  rw [hmeas, hres, smul_smul]
  unfold prior
  rw [show max q x + (x + U - max q x) = x + U by ring]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inr (by simp; constructor <;> linarith)), inv_inv,
    mul_comm (ENNReal.ofReal U), mul_assoc,
    ENNReal.mul_inv_cancel (by simp [hU]) ENNReal.ofReal_ne_top, mul_one]

lemma ig_dirac (p c d : ℝ) (hc : 0 ≤ c) (hcp : c ≤ p) (hd : 0 ≤ d) :
    IsGreatest (nvProfit p c (Measure.dirac d) '' Set.Ici 0) ((p - c) * d) := by
  refine ⟨⟨d, hd, ?_⟩, ?_⟩
  · unfold nvProfit; rw [integral_dirac]; simp; ring
  · rintro _ ⟨Q, hQ, rfl⟩
    unfold nvProfit; rw [integral_dirac]
    rcases le_total d Q with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith

lemma ig_prior (p c a b : ℝ) (hc : 0 ≤ c) (hcp : c < p) (ha : 0 ≤ a) (hb : 0 < b) :
    IsGreatest (nvProfit p c (prior a b) '' Set.Ici 0)
      ((p - c) * a + b / 2 * ((p - c) ^ 2 / p)) := by
  obtain ⟨h0, hv, hm⟩ := FlexLearning.Threshold.lemma_3 p c a b hc hcp ha hb
  refine ⟨⟨_, h0, hv⟩, ?_⟩
  rintro _ ⟨Q, hQ, rfl⟩
  rw [← hv]; exact hm Q hQ

/-- second-period value of a product with prior/posterior `G` (probability, integrable). -/
lemma V2_prod (p c : ℝ) (G1 G2 : Measure ℝ) [IsProbabilityMeasure G1] [IsProbabilityMeasure G2]
    (h1 : ∀ Q : ℝ, Integrable (fun d => min d Q) G1)
    (h2 : ∀ Q : ℝ, Integrable (fun d => min d Q) G2) (M1 M2 : ℝ)
    (hM1 : IsGreatest (nvProfit p c G1 '' Set.Ici 0) M1)
    (hM2 : IsGreatest (nvProfit p c G2 '' Set.Ici 0) M2) :
    V2 p c (G1.prod G2) = M1 + M2 := by
  have key : ∀ Q : ℝ × ℝ,
      ∫ d, (p * min d.1 Q.1 + p * min d.2 Q.2 - c * (Q.1 + Q.2)) ∂(G1.prod G2) =
        nvProfit p c G1 Q.1 + nvProfit p c G2 Q.2 := by
    intro Q
    have i1 := ((h1 Q.1).const_mul p).comp_fst G2
    have i2 := ((h2 Q.2).const_mul p).comp_snd G1
    rw [integral_sub (f := fun d : ℝ × ℝ => p * min d.1 Q.1 + p * min d.2 Q.2) (i1.add i2)
      (integrable_const _), integral_add i1 i2,
      integral_fun_fst (fun d => p * min d Q.1), integral_fun_snd (fun d => p * min d Q.2)]
    unfold nvProfit
    rw [integral_sub ((h1 Q.1).const_mul p) (integrable_const _),
      integral_sub ((h2 Q.2).const_mul p) (integrable_const _)]
    simp; ring
  unfold V2
  apply IsGreatest.csSup_eq
  obtain ⟨⟨Q1, hQ1, e1⟩, b1⟩ := hM1
  obtain ⟨⟨Q2, hQ2, e2⟩, b2⟩ := hM2
  refine ⟨⟨(Q1, Q2), ⟨hQ1, hQ2⟩, ?_⟩, ?_⟩
  · have := key (Q1, Q2); simp only at this ⊢; rw [this, e1, e2]
  · rintro _ ⟨Q, ⟨hq1, hq2⟩, rfl⟩
    simp only; rw [key Q]
    have := b1 ⟨Q.1, hq1, rfl⟩
    have := b2 ⟨Q.2, hq2, rfl⟩
    linarith

/-- value of the stocked-out posterior. -/
noncomputable def Sv (p c x U q : ℝ) : ℝ :=
  (p - c) * max q x + (x + U - max q x) / 2 * ((p - c) ^ 2 / p)

/-- one product's second-period value after observing (censored) sales. -/
noncomputable def Wt (p c x U q d : ℝ) : ℝ := if d < q then (p - c) * d else Sv p c x U q

lemma post_facts (p c x U q d : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U)
    (hd : x ≤ d) (hq : d < q ∨ q < x + U) :
    IsProbabilityMeasure (post x U q d) ∧
    (∀ Q : ℝ, Integrable (fun d => min d Q) (post x U q d)) ∧
    IsGreatest (nvProfit p c (post x U q d) '' Set.Ici 0) (Wt p c x U q d) := by
  unfold post Wt
  split_ifs with h
  · refine ⟨inferInstance, fun Q => integrable_dirac (by simp), ?_⟩
    exact ig_dirac p c d hc hcp.le (by linarith)
  · have hq' : q < x + U := hq.resolve_left h
    rw [cond_prior x U q hU hq']
    have hpos : 0 < x + U - max q x := by
      rcases le_total q x with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    refine ⟨prior_prob _ _ hpos, fun Q => prior_integrable _ _ hpos _ (by fun_prop), ?_⟩
    have := ig_prior p c (max q x) (x + U - max q x) hc hcp (le_max_of_le_right hx) hpos
    unfold Sv; convert this using 2

lemma V2_post (p c x U q1 q2 d1 d2 : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U)
    (hd1 : x ≤ d1) (hq1 : d1 < q1 ∨ q1 < x + U) (hd2 : x ≤ d2) (hq2 : d2 < q2 ∨ q2 < x + U) :
    V2 p c ((post x U q1 d1).prod (post x U q2 d2)) = Wt p c x U q1 d1 + Wt p c x U q2 d2 := by
  obtain ⟨i1, j1, k1⟩ := post_facts p c x U q1 d1 hc hcp hx hU hd1 hq1
  obtain ⟨i2, j2, k2⟩ := post_facts p c x U q2 d2 hc hcp hx hU hd2 hq2
  exact V2_prod p c _ _ j1 j2 _ _ k1 k2


lemma int_min (x U Q : ℝ) (hU : 0 < U) :
    ∫ d in x..x + U, min d Q =
      if Q ≤ x then Q * U
      else if Q ≤ x + U then x * U + (Q - x) * U - (Q - x) ^ 2 / 2
      else x * U + U ^ 2 / 2 := by
  split_ifs with h1 h2
  · rw [intervalIntegral.integral_congr (g := fun _ => Q)]
    · simp; ring
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      simp only
      exact min_eq_right (by linarith [hd.1])
  · have hc : Continuous fun d : ℝ => min d Q := continuous_id.min continuous_const
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := Q)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (g := fun d => d) (a := x) (b := Q),
      intervalIntegral.integral_congr (g := fun _ => Q) (a := Q) (b := x + U)]
    · simp [integral_id]; ring
    · intro d hd
      rw [Set.uIcc_of_le h2] at hd
      exact min_eq_right hd.1
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      exact min_eq_left hd.2
  · rw [intervalIntegral.integral_congr (g := fun d => d)]
    · simp [integral_id]; ring
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      exact min_eq_left (by linarith [hd.2])

lemma nv_formula (p c x U Q : ℝ) (hU : 0 < U) :
    nvProfit p c (prior x U) Q =
      p * U⁻¹ * (if Q ≤ x then Q * U
      else if Q ≤ x + U then x * U + (Q - x) * U - (Q - x) ^ 2 / 2
      else x * U + U ^ 2 / 2) - c * Q := by
  unfold nvProfit
  rw [prior_integral x U hU, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    int_min x U Q hU]
  · split_ifs <;> simp <;> field_simp <;> ring
  · exact ((continuous_id.min continuous_const).const_smul p).intervalIntegrable _ _
  · exact intervalIntegrable_const

/-- explicit (a.e.) version of `Wt`. -/
noncomputable def Wp (p c x U q d : ℝ) : ℝ := if d ≤ q then (p - c) * d else Sv p c x U q

lemma Wp_eq_ind (p c x U q : ℝ) :
    Wp p c x U q = (Set.Iic q).indicator (fun d => (p - c) * d) +
      (Set.Ioi q).indicator (fun _ => Sv p c x U q) := by
  funext d
  by_cases h : d ≤ q
  · simp [Wp, Set.indicator, h, not_lt.mpr h]
  · have h' : q < d := lt_of_not_ge h
    simp [Wp, Set.indicator, h, h']

lemma Wp_integrable (p c x U q : ℝ) (hU : 0 < U) : Integrable (Wp p c x U q) (prior x U) := by
  have := prior_prob x U hU
  rw [Wp_eq_ind]
  exact ((prior_integrable x U hU _ (by fun_prop)).indicator measurableSet_Iic).add
    ((integrable_const _).indicator measurableSet_Ioi)

lemma ioc_congr (F G : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (h : ∀ d, a < d → d ≤ b → F d = G d) :
    (∫ d in a..b, F d) = ∫ d in a..b, G d := by
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall (fun d hd => ?_)
  rw [Set.uIoc_of_le hab] at hd
  exact h d hd.1 hd.2

lemma ioc_ii (F G : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (h : ∀ d, a < d → d ≤ b → F d = G d)
    (hG : Continuous G) : IntervalIntegrable F volume a b := by
  refine (intervalIntegrable_congr (g := F) (f := G) ?_).mp (hG.intervalIntegrable _ _)
  intro d hd
  rw [Set.uIoc_of_le hab] at hd
  exact (h d hd.1 hd.2).symm

/-- expected second-period value of one product. -/
noncomputable def EW (p c x U q : ℝ) : ℝ :=
  if q ≤ x then (p - c) * x + U / 2 * ((p - c) ^ 2 / p)
  else if q ≤ x + U then
    U⁻¹ * ((p - c) * (q ^ 2 - x ^ 2) / 2 + (x + U - q) * ((p - c) * q + (x + U - q) / 2 * ((p - c) ^ 2 / p)))
  else (p - c) * (x + U / 2)

lemma EW_eq (p c x U q : ℝ) (hU : 0 < U) (hp : 0 < p) : ∫ d, Wp p c x U q d ∂(prior x U) = EW p c x U q := by
  rw [prior_integral x U hU]
  unfold EW
  split_ifs with h1 h2
  · rw [ioc_congr _ (fun _ => Sv p c x U q) _ _ (by linarith)]
    · simp [Sv, max_eq_right h1]; field_simp
    · intro d hd _; simp [Wp]; intro h; linarith
  · push Not at h1
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := q)
      (ioc_ii _ (fun d => (p - c) * d) _ _ h1.le (fun d _ hd => by simp [Wp, hd]) (by fun_prop))
      (ioc_ii _ (fun _ => Sv p c x U q) _ _ h2 (fun d hd _ => by simp [Wp]; intro h; linarith)
        (by fun_prop))]
    rw [ioc_congr _ (fun d => (p - c) * d) _ _ h1.le (fun d _ hd => by simp [Wp, hd]),
      ioc_congr _ (fun _ => Sv p c x U q) _ _ h2 (fun d hd _ => by simp [Wp]; intro h; linarith)]
    rw [intervalIntegral.integral_const_mul (p - c) (fun d => d), integral_id]
    simp only [Sv, max_eq_left h1.le, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp
  · push Not at h1 h2
    rw [ioc_congr _ (fun d => (p - c) * d) _ _ (by linarith)
      (fun d _ hd => by simp [Wp]; intro h; linarith)]
    rw [intervalIntegral.integral_const_mul, integral_id]; field_simp; ring

lemma prior2_eq (x U : ℝ) :
    prior2 x U = (ENNReal.ofReal U)⁻¹ • (ENNReal.ofReal U)⁻¹ •
      (volume : Measure (ℝ × ℝ)).restrict (Set.Icc x (x + U) ×ˢ Set.Icc x (x + U)) := by
  unfold prior2 prior
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict,
    ← Measure.volume_eq_prod]

lemma prior2_ae (x U : ℝ) (P : ℝ × ℝ → Prop)
    (h : ∀ᵐ d ∂((volume : Measure (ℝ × ℝ)).restrict (Set.Icc x (x + U) ×ˢ Set.Icc x (x + U))), P d) :
    ∀ᵐ d ∂(prior2 x U), P d := by
  rw [prior2_eq]
  exact Measure.ae_smul_measure (Measure.ae_smul_measure h _) _

lemma ae_fst_ne (a : ℝ) : ∀ᵐ d ∂(volume : Measure (ℝ × ℝ)), d.1 ≠ a := by
  rw [ae_iff]
  have : {d : ℝ × ℝ | ¬ d.1 ≠ a} = {a} ×ˢ Set.univ := by ext d; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp

lemma ae_snd_ne (a : ℝ) : ∀ᵐ d ∂(volume : Measure (ℝ × ℝ)), d.2 ≠ a := by
  rw [ae_iff]
  have : {d : ℝ × ℝ | ¬ d.2 ≠ a} = Set.univ ×ˢ {a} := by ext d; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp

lemma good_ae (x U a b : ℝ) : ∀ᵐ d ∂(prior2 x U),
    d.1 ∈ Set.Icc x (x + U) ∧ d.2 ∈ Set.Icc x (x + U) ∧ d.1 ≠ a ∧ d.2 ≠ b ∧
      d.1 ≠ x + U ∧ d.2 ≠ x + U := by
  apply prior2_ae
  have hm := ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ)))
    (s := Set.Icc x (x + U) ×ˢ Set.Icc x (x + U)) (measurableSet_Icc.prod measurableSet_Icc)
  filter_upwards [hm, ae_restrict_of_ae (ae_fst_ne a), ae_restrict_of_ae (ae_snd_ne b),
    ae_restrict_of_ae (ae_fst_ne (x + U)), ae_restrict_of_ae (ae_snd_ne (x + U))]
    with d h0 h1 h2 h3 h4
  exact ⟨h0.1, h0.2, h1, h2, h3, h4⟩

lemma Wt_eq_Wp (p c x U q d : ℝ) (h : d ≠ q) : Wt p c x U q d = Wp p c x U q d := by
  unfold Wt Wp
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [if_pos h', if_pos h'.le]
  · rw [if_neg (by linarith), if_neg (by linarith)]

lemma piN_split (p c x U : ℝ) (hU : 0 < U) (Q : ℝ × ℝ) :
    piN p c x U Q = nvProfit p c (prior x U) Q.1 + nvProfit p c (prior x U) Q.2 := by
  have := prior_prob x U hU
  have h1 := prior_integrable x U hU (fun d => p * min d Q.1)
    (continuous_const.mul (continuous_id.min continuous_const))
  have h2 := prior_integrable x U hU (fun d => p * min d Q.2)
    (continuous_const.mul (continuous_id.min continuous_const))
  unfold piN nvProfit prior2
  rw [integral_add (h1.comp_fst _) (h2.comp_snd _), integral_fun_fst (fun d => p * min d Q.1),
    integral_fun_snd (fun d => p * min d Q.2), integral_sub h1 (integrable_const _),
    integral_sub h2 (integrable_const _)]
  simp; ring

lemma vN_split (p c x U : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) (Q : ℝ × ℝ) :
    vN p c x U Q = (nvProfit p c (prior x U) Q.1 + EW p c x U Q.1) +
      (nvProfit p c (prior x U) Q.2 + EW p c x U Q.2) := by
  have := prior_prob x U hU
  unfold vN
  rw [piN_split p c x U hU]
  have hae : (fun d : ℝ × ℝ => V2 p c ((post x U Q.1 d.1).prod (post x U Q.2 d.2))) =ᵐ[prior2 x U]
      (fun d => Wp p c x U Q.1 d.1 + Wp p c x U Q.2 d.2) := by
    filter_upwards [good_ae x U Q.1 Q.2] with d ⟨h1, h2, h3, h4, h5, h6⟩
    have hq1 : d.1 < Q.1 ∨ Q.1 < x + U := by
      rcases lt_or_ge Q.1 (x + U) with h | h
      · exact Or.inr h
      · left; exact lt_of_lt_of_le (lt_of_le_of_ne h1.2 h5) h
    have hq2 : d.2 < Q.2 ∨ Q.2 < x + U := by
      rcases lt_or_ge Q.2 (x + U) with h | h
      · exact Or.inr h
      · left; exact lt_of_lt_of_le (lt_of_le_of_ne h2.2 h6) h
    rw [V2_post p c x U _ _ _ _ hc hcp hx hU h1.1 hq1 h2.1 hq2, Wt_eq_Wp _ _ _ _ _ _ h3,
      Wt_eq_Wp _ _ _ _ _ _ h4]
  rw [integral_congr_ae hae]
  unfold prior2
  rw [integral_add ((Wp_integrable p c x U Q.1 hU).comp_fst _)
    ((Wp_integrable p c x U Q.2 hU).comp_snd _), integral_fun_fst (fun d => Wp p c x U Q.1 d),
    integral_fun_snd (fun d => Wp p c x U Q.2 d), EW_eq _ _ _ _ _ hU (by linarith), EW_eq _ _ _ _ _ hU (by linarith)]
  simp; ring


lemma prior_ae (x U : ℝ) (P : ℝ → Prop)
    (h : ∀ᵐ d ∂(volume.restrict (Set.Icc x (x + U))), P d) : ∀ᵐ d ∂(prior x U), P d := by
  unfold prior; exact Measure.ae_smul_measure h _

lemma ae_ne_real (a : ℝ) : ∀ᵐ d ∂(volume : Measure ℝ), d ≠ a := by
  rw [ae_iff]; simp

lemma Wt_ae (p c x U q : ℝ) : Wt p c x U q =ᵐ[prior x U] Wp p c x U q := by
  apply prior_ae
  filter_upwards [ae_restrict_of_ae (ae_ne_real q)] with d hd
  exact Wt_eq_Wp p c x U q d hd

lemma Wt_integrable (p c x U q : ℝ) (hU : 0 < U) : Integrable (Wt p c x U q) (prior x U) :=
  (Wp_integrable p c x U q hU).congr (Wt_ae p c x U q).symm

lemma int_Wt (p c x U q : ℝ) (hU : 0 < U) (hp : 0 < p) :
    ∫ d, Wt p c x U q d ∂(prior x U) = EW p c x U q := by
  rw [integral_congr_ae (Wt_ae p c x U q), EW_eq p c x U q hU hp]

lemma Sv_cont (p c x U : ℝ) : Continuous (Sv p c x U) := by
  unfold Sv; fun_prop

lemma Wt_abs (p c x U q d : ℝ) : |Wt p c x U q d| ≤ |p - c| * |d| + |Sv p c x U q| := by
  unfold Wt
  split_ifs
  · rw [abs_mul]; have := abs_nonneg (Sv p c x U q); linarith
  · have := mul_nonneg (abs_nonneg (p - c)) (abs_nonneg d); linarith

lemma Wt_meas (p c x U : ℝ) (g : ℝ × ℝ → ℝ) (hg : Continuous g) (h : ℝ × ℝ → ℝ) (hh : Continuous h) :
    Measurable (fun d : ℝ × ℝ => Wt p c x U (g d) (h d)) := by
  unfold Wt
  refine Measurable.ite (measurableSet_lt hh.measurable hg.measurable) ?_ ?_
  · exact (continuous_const.mul hh).measurable
  · exact ((Sv_cont p c x U).comp hg).measurable

lemma F_integrable (p c x U QF : ℝ) (hx : 0 ≤ x) (hU : 0 < U) :
    Integrable (fun d : ℝ × ℝ => Wt p c x U QF d.1 + Wt p c x U (QF - min d.1 QF) d.2)
      ((prior x U).prod (prior x U)) := by
  have := prior_prob x U hU
  refine Integrable.add ((Wt_integrable p c x U QF hU).comp_fst _) ?_
  set R := 2 * |QF| + x + U
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    (Sv_cont p c x U).continuousOn
  refine Integrable.mono' (integrable_const (|p - c| * (x + U) + M)) ?_ ?_
  · exact (Wt_meas p c x U (fun d => QF - min d.1 QF) (by fun_prop) (fun d => d.2)
      (by fun_prop)).aestronglyMeasurable
  · have hae := good_ae x U 0 0
    unfold prior2 at hae
    filter_upwards [hae] with d ⟨h1, h2, _⟩
    rw [Real.norm_eq_abs]
    have hq : QF - min d.1 QF ∈ Set.Icc (-R) R := by
      have hm1 : min d.1 QF ≤ QF := min_le_right _ _
      have hm2 : -|QF| ≤ min d.1 QF := le_min (by linarith [abs_nonneg QF, h1.1]) (neg_abs_le QF)
      have hm3 : min d.1 QF ≤ x + U := le_trans (min_le_left _ _) h1.2
      constructor <;> [skip; skip] <;>
        nlinarith [abs_nonneg QF, le_abs_self QF, neg_abs_le QF]
    have hS := hM _ hq
    rw [Real.norm_eq_abs] at hS
    have hd2 : |d.2| ≤ x + U := by rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
    have := Wt_abs p c x U (QF - min d.1 QF) d.2
    have := mul_le_mul_of_nonneg_left hd2 (abs_nonneg (p - c))
    linarith

lemma V2_flex_ae (p c x U QF : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    (fun d : ℝ × ℝ => V2 p c ((post x U QF d.1).prod (post x U (QF - min d.1 QF) d.2)))
      =ᵐ[prior2 x U] (fun d => Wt p c x U QF d.1 + Wt p c x U (QF - min d.1 QF) d.2) := by
  filter_upwards [good_ae x U 0 0] with d ⟨h1, h2, _, _, h5, h6⟩
  have hq1 : d.1 < QF ∨ QF < x + U := by
    rcases lt_or_ge QF (x + U) with h | h
    · exact Or.inr h
    · left; exact lt_of_lt_of_le (lt_of_le_of_ne h1.2 h5) h
  have hq2 : d.2 < QF - min d.1 QF ∨ QF - min d.1 QF < x + U := by
    rcases lt_or_ge (QF - min d.1 QF) (x + U) with h | h
    · exact Or.inr h
    · left; exact lt_of_lt_of_le (lt_of_le_of_ne h2.2 h6) h
  exact V2_post p c x U _ _ _ _ hc hcp hx hU h1.1 hq1 h2.1 hq2

/-- the second-period part of `vF`, reduced to a one-dimensional integral. -/
lemma vF_sec (p c x U QF : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    ∫ d, V2 p c ((post x U QF d.1).prod (post x U (QF - min d.1 QF) d.2)) ∂(prior2 x U) =
      U⁻¹ * ∫ d1 in x..x + U, (Wt p c x U QF d1 + EW p c x U (QF - min d1 QF)) := by
  have := prior_prob x U hU
  rw [integral_congr_ae (V2_flex_ae p c x U QF hc hcp hx hU)]
  unfold prior2
  rw [integral_prod _ (F_integrable p c x U QF hx hU)]
  rw [← prior_integral x U hU]
  congr 1
  funext d1
  simp only
  rw [integral_add (integrable_const _) (Wt_integrable p c x U _ hU),
    int_Wt p c x U _ hU (by linarith)]
  simp


lemma ioo_congr (F G : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (h : ∀ d, a < d → d < b → F d = G d) :
    (∫ d in a..b, F d) = ∫ d in a..b, G d := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_ne_real b] with d hd hmem
  rw [Set.uIoc_of_le hab] at hmem
  exact h d hmem.1 (lt_of_le_of_ne hmem.2 hd)

lemma ioo_ii (F G : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (h : ∀ d, a < d → d < b → F d = G d)
    (hG : Continuous G) : IntervalIntegrable F volume a b := by
  refine (intervalIntegrable_congr_uIoo (f := G) (g := F) ?_).mp (hG.intervalIntegrable _ _)
  intro d hd
  rw [Set.uIoo_of_le hab] at hd
  exact (h d hd.1 hd.2).symm

lemma quad_int (a0 a1 a2 a b : ℝ) :
    ∫ d in a..b, (a0 + a1 * d + a2 * d ^ 2) = a0 * (b - a) + a1 * (b ^ 2 - a ^ 2) / 2 +
      a2 * (b ^ 3 - a ^ 3) / 3 := by
  rw [intervalIntegral.integral_add (f := fun d : ℝ => a0 + a1 * d) (g := fun d => a2 * d ^ 2)
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (f := fun _ : ℝ => a0) (g := fun d => a1 * d) intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
    integral_pow]
  simp; ring

/-- middle branch of `EW`. -/
noncomputable def EWm (p c x U q : ℝ) : ℝ :=
  U⁻¹ * ((p - c) * (q ^ 2 - x ^ 2) / 2 + (x + U - q) * ((p - c) * q + (x + U - q) / 2 * ((p - c) ^ 2 / p)))

lemma EWm_poly (p c x U Q d : ℝ) (hU : 0 < U) (hp : 0 < p) :
    (p - c) * d + EWm p c x U (Q - d) =
      (-(p - c) * (Q ^ 2 * c - 2 * Q * U * c - 2 * Q * c * x + U ^ 2 * c - U ^ 2 * p + 2 * U * c * x
        - 2 * U * p * x + c * x ^ 2) / (2 * U * p)) +
      (-(p - c) * (-Q * c + U * c - U * p + c * x) / (U * p)) * d +
      (-c * (p - c) / (2 * U * p)) * d ^ 2 := by
  unfold EWm; field_simp; ring

lemma EW_mid (p c x U q : ℝ) (h1 : x < q) (h2 : q ≤ x + U) : EW p c x U q = EWm p c x U q := by
  unfold EW EWm; rw [if_neg (by linarith), if_pos h2]

lemma EW_hi (p c x U q : ℝ) (hU : 0 < U) (h : x + U ≤ q) : EW p c x U q = (p - c) * (x + U / 2) := by
  unfold EW
  rw [if_neg (by linarith)]
  split_ifs with h2
  · have : q = x + U := le_antisymm h2 h
    subst this; field_simp; ring
  · rfl

/-- second-period integral, regime `2x+U ≤ QF ≤ 2x+2U`. -/
lemma secG (p c x U QF : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hp : 0 < p) (h1 : 2 * x + U ≤ QF)
    (h2 : QF ≤ 2 * x + 2 * U) :
    U⁻¹ * ∫ d1 in x..x + U, (Wt p c x U QF d1 + EW p c x U (QF - min d1 QF)) =
      U⁻¹ * (((p - c) * ((QF - x - U) ^ 2 - x ^ 2) / 2 + (p - c) * (x + U / 2) * (QF - x - U - x)) +
      ((-(p - c) * (QF ^ 2 * c - 2 * QF * U * c - 2 * QF * c * x + U ^ 2 * c - U ^ 2 * p
        + 2 * U * c * x - 2 * U * p * x + c * x ^ 2) / (2 * U * p)) * (x + U - (QF - x - U)) +
       (-(p - c) * (-QF * c + U * c - U * p + c * x) / (U * p)) * ((x + U) ^ 2 - (QF - x - U) ^ 2) / 2 +
       (-c * (p - c) / (2 * U * p)) * ((x + U) ^ 3 - (QF - x - U) ^ 3) / 3)) := by
  set s0 := QF - x - U
  have hs0 : x ≤ s0 := by simp only [s0]; linarith
  have hs1 : s0 ≤ x + U := by simp only [s0]; linarith
  have hWt : ∀ d, d < x + U → Wt p c x U QF d = (p - c) * d := by
    intro d hd; unfold Wt; rw [if_pos (by linarith)]
  have hmin : ∀ d, d < x + U → min d QF = d := fun d hd => min_eq_left (by linarith)
  have eq1 : ∀ d, x < d → d < s0 →
      Wt p c x U QF d + EW p c x U (QF - min d QF) = (p - c) * d + (p - c) * (x + U / 2) := by
    intro d _ hd
    rw [hWt d (by linarith), hmin d (by linarith), EW_hi p c x U _ hU (by simp only [s0] at hd; linarith)]
  have eq2 : ∀ d, s0 < d → d < x + U →
      Wt p c x U QF d + EW p c x U (QF - min d QF) = (p - c) * d + EWm p c x U (QF - d) := by
    intro d hd hd'
    rw [hWt d hd', hmin d hd', EW_mid p c x U _ (by simp only [s0] at hd; linarith) (by linarith)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s0)
    (ioo_ii _ _ _ _ hs0 eq1 (by fun_prop))
    (ioo_ii _ (fun d => (-(p - c) * (QF ^ 2 * c - 2 * QF * U * c - 2 * QF * c * x + U ^ 2 * c
        - U ^ 2 * p + 2 * U * c * x - 2 * U * p * x + c * x ^ 2) / (2 * U * p)) +
      (-(p - c) * (-QF * c + U * c - U * p + c * x) / (U * p)) * d +
      (-c * (p - c) / (2 * U * p)) * d ^ 2) _ _ hs1
      (fun d hd hd' => by rw [eq2 d hd hd', EWm_poly p c x U QF d hU hp]) (by fun_prop))]
  rw [ioo_congr _ _ _ _ hs0 eq1, ioo_congr _ (fun d => (-(p - c) * (QF ^ 2 * c - 2 * QF * U * c
      - 2 * QF * c * x + U ^ 2 * c - U ^ 2 * p + 2 * U * c * x - 2 * U * p * x + c * x ^ 2)
      / (2 * U * p)) + (-(p - c) * (-QF * c + U * c - U * p + c * x) / (U * p)) * d +
      (-c * (p - c) / (2 * U * p)) * d ^ 2) _ _ hs1
      (fun d hd hd' => by rw [eq2 d hd hd', EWm_poly p c x U QF d hU hp]), quad_int]
  rw [intervalIntegral.integral_add (f := fun d : ℝ => (p - c) * d) (g := fun _ => (p - c) * (x + U / 2))
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [intervalIntegral.integral_const, smul_eq_mul]; ring


lemma vF_G (p c x U cF QF : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U)
    (h1 : 2 * x + U ≤ QF) (h2 : QF ≤ 2 * x + 2 * U) :
    vF p c x U cF QF = 2 * U * (p - cF) - U * c + 4 * p * x - 2 * c * x - 2 * cF * x +
      cF * (2 * x + 2 * U - QF) -
      ((p - c) * (p + c) + c * p) * (2 * x + 2 * U - QF) ^ 3 / (6 * U ^ 2 * p) := by
  have hp : 0 < p := by linarith
  unfold vF
  rw [vF_sec p c x U QF hc hcp hx hU, secG p c x U QF hx hU hp h1 h2,
    FlexLAuxP.reg2 p x U cF QF hx hU h1 h2]
  field_simp
  ring


lemma sec3 (p c x U QF : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (h1 : 2 * x + 2 * U ≤ QF) :
    U⁻¹ * ∫ d1 in x..x + U, (Wt p c x U QF d1 + EW p c x U (QF - min d1 QF)) =
      U⁻¹ * ((p - c) * ((x + U) ^ 2 - x ^ 2) / 2 + (p - c) * (x + U / 2) * U) := by
  have eq1 : ∀ d, x < d → d < x + U →
      Wt p c x U QF d + EW p c x U (QF - min d QF) = (p - c) * d + (p - c) * (x + U / 2) := by
    intro d hd hd'
    have : Wt p c x U QF d = (p - c) * d := by unfold Wt; rw [if_pos (by linarith)]
    rw [this, min_eq_left (by linarith), EW_hi p c x U _ hU (by linarith)]
  rw [ioo_congr _ _ _ _ (by linarith) eq1]
  rw [intervalIntegral.integral_add (f := fun d : ℝ => (p - c) * d) (g := fun _ => (p - c) * (x + U / 2))
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [intervalIntegral.integral_const, smul_eq_mul]; ring

lemma secL (p c U QF : ℝ) (hU : 0 < U) (hp : 0 < p) (h0 : 0 ≤ QF) (h1 : QF ≤ U) :
    U⁻¹ * ∫ d1 in (0:ℝ)..0 + U, (Wt p c 0 U QF d1 + EW p c 0 U (QF - min d1 QF)) =
      U⁻¹ * (((-(p - c) * (QF ^ 2 * c - 2 * QF * U * c - 2 * QF * c * 0 + U ^ 2 * c - U ^ 2 * p
        + 2 * U * c * 0 - 2 * U * p * 0 + c * 0 ^ 2) / (2 * U * p)) * QF +
       (-(p - c) * (-QF * c + U * c - U * p + c * 0) / (U * p)) * QF ^ 2 / 2 +
       (-c * (p - c) / (2 * U * p)) * QF ^ 3 / 3) +
       (Sv p c 0 U QF + U / 2 * ((p - c) ^ 2 / p)) * (U - QF)) := by
  have eq1 : ∀ d, 0 < d → d < QF →
      Wt p c 0 U QF d + EW p c 0 U (QF - min d QF) =
        (-(p - c) * (QF ^ 2 * c - 2 * QF * U * c - 2 * QF * c * 0 + U ^ 2 * c - U ^ 2 * p
        + 2 * U * c * 0 - 2 * U * p * 0 + c * 0 ^ 2) / (2 * U * p)) +
        (-(p - c) * (-QF * c + U * c - U * p + c * 0) / (U * p)) * d +
        (-c * (p - c) / (2 * U * p)) * d ^ 2 := by
    intro d hd hd'
    have : Wt p c 0 U QF d = (p - c) * d := by unfold Wt; rw [if_pos hd']
    rw [this, min_eq_left hd'.le, EW_mid p c 0 U _ (by linarith) (by linarith),
      EWm_poly p c 0 U QF d hU hp]
  have eq2 : ∀ d, QF < d → d < 0 + U →
      Wt p c 0 U QF d + EW p c 0 U (QF - min d QF) = Sv p c 0 U QF + U / 2 * ((p - c) ^ 2 / p) := by
    intro d hd _
    have : Wt p c 0 U QF d = Sv p c 0 U QF := by unfold Wt; rw [if_neg (by linarith)]
    rw [this, min_eq_right hd.le, sub_self]
    unfold EW; rw [if_pos le_rfl]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := QF)
    (ioo_ii _ _ _ _ h0 eq1 (by fun_prop)) (ioo_ii _ _ _ _ (by linarith) eq2 (by fun_prop))]
  rw [ioo_congr _ _ _ _ h0 eq1, ioo_congr _ _ _ _ (by linarith) eq2, quad_int]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma vF_L (p c U cF QF : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hU : 0 < U) (h0 : 0 ≤ QF) (h1 : QF ≤ U) :
    vF p c 0 U cF QF = (p - c) ^ 2 * U / p + QF * (((p - c) * (p + c) + c * p) / p - cF) -
      ((p - c) * (p + c) + c * p) * QF ^ 3 / (6 * U ^ 2 * p) := by
  have hp : 0 < p := by linarith
  unfold vF
  rw [vF_sec p c 0 U QF hc hcp le_rfl hU, secL p c U QF hU hp h0 h1,
    FlexLAuxP.reg1 p 0 U cF QF le_rfl hU (by linarith) (by linarith)]
  unfold Sv
  rw [max_eq_left h0]
  field_simp
  ring

lemma vF_3 (p c x U cF QF : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U)
    (h1 : 2 * x + 2 * U ≤ QF) :
    vF p c x U cF QF = p * (2 * x + U) - cF * QF + (p - c) * (2 * x + U) := by
  unfold vF
  rw [vF_sec p c x U QF hc hcp hx hU, sec3 p c x U QF hx hU h1,
    FlexLAuxP.reg3 p x U cF QF hx hU h1]
  field_simp
  ring

end FlexLAuxW

open FlexLAuxW in
theorem solution (p c U cF Q : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hU : 0 < U) :
    (0 ≤ Q → Q ≤ U → vF p c 0 U cF Q = (p - c) ^ 2 * U / p +
      Q * (((p - c) * (p + c) + c * p) / p - cF) -
      ((p - c) * (p + c) + c * p) * Q ^ 3 / (6 * U ^ 2 * p)) ∧
    (U ≤ Q → Q ≤ 2 * U → vF p c 0 U cF Q = 2 * U * (p - cF) - U * c + cF * (2 * U - Q) -
      ((p - c) * (p + c) + c * p) * (2 * U - Q) ^ 3 / (6 * U ^ 2 * p)) ∧
    (2 * U ≤ Q → vF p c 0 U cF Q = p * U - cF * Q + (p - c) * U) := by
  refine ⟨fun h0 h1 => vF_L p c U cF Q hc hcp hU h0 h1, fun h1 h2 => ?_,
    fun h => ?_⟩
  · rw [vF_G p c 0 U cF Q hc hcp le_rfl hU (by linarith) (by linarith)]; ring
  · rw [vF_3 p c 0 U cF Q hc hcp le_rfl hU (by linarith)]; ring
