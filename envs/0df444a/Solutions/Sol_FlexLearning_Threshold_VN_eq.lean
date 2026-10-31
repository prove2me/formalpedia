-- Prove2me | solution 1 for FlexLearning.Threshold.VN_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:56:10.814454+00:00
-- url     : https://prove2.me/submissions/700d2890-9df8-46d4-8371-7a6254b253ae

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model
import Theorems.Thm_FlexLearning_Threshold_lemma_3

open FlexLearning.Threshold MeasureTheory ProbabilityTheory

namespace FlexLAuxV

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

end FlexLAuxV

open FlexLAuxV

theorem solution (p c x U : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    vN p c x U (x + U * ((p - c) * (p + c) / ((p - c) * (p + c) + c * p)),
        x + U * ((p - c) * (p + c) / ((p - c) * (p + c) + c * p))) = VN p c x U ∧
    VN p c x U =
      4 * x * (p - c) + U * ((p - c) ^ 2 * (3 * c + 2 * p) / ((p - c) * (p + c) + c * p)) := by
  have hp : 0 < p := by linarith
  have hpc : 0 < p - c := by linarith
  set Δ := (p - c) * (p + c) + c * p with hΔ
  have hΔp : 0 < Δ := by rw [hΔ]; have : 0 < (p - c) * (p + c) := by nlinarith
                         nlinarith
  set hs := 2 * x * (p - c) + U * ((p - c) ^ 2 * (3 * c + 2 * p) / Δ) / 2 with hhs
  set Qs := x + U * ((p - c) * (p + c) / Δ) with hQs
  have hr0 : 0 ≤ (p - c) * (p + c) / Δ := by positivity
  have hr1 : (p - c) * (p + c) / Δ ≤ 1 := by
    rw [div_le_one hΔp, hΔ]; nlinarith
  -- value and bound of the one-product two-period objective
  have hval : nvProfit p c (prior x U) Qs + EW p c x U Qs = hs := by
    rw [nv_formula p c x U Qs hU]
    unfold EW
    by_cases h0 : Qs ≤ x
    · have : U * ((p - c) * (p + c) / Δ) = 0 := by
        have : 0 ≤ U * ((p - c) * (p + c) / Δ) := by positivity
        linarith
      have : (p - c) * (p + c) = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · rcases div_eq_zero_iff.1 h with h' | h'
          · exact h'
          · linarith
      nlinarith
    rw [if_neg h0, if_pos (by nlinarith), if_neg h0, if_pos (by nlinarith)]
    rw [hhs, hQs]
    field_simp
    ring
  have hbound : ∀ q, 0 ≤ q → nvProfit p c (prior x U) q + EW p c x U q ≤ hs := by
    intro q hq
    rw [nv_formula p c x U q hU]
    unfold EW
    by_cases h0 : q ≤ x
    · rw [if_pos h0, if_pos h0]
      have key : hs - (p * U⁻¹ * (q * U) - c * q + ((p - c) * x + U / 2 * ((p - c) ^ 2 / p))) =
          (U * (p ^ 2 - c ^ 2)) ^ 2 / (2 * U * p * Δ) + (p - c) * (x - q) := by
        rw [hhs, hΔ]; field_simp; ring
      have : 0 ≤ (U * (p ^ 2 - c ^ 2)) ^ 2 / (2 * U * p * Δ) := by positivity
      have : 0 ≤ (p - c) * (x - q) := mul_nonneg hpc.le (by linarith)
      linarith
    by_cases h1 : q ≤ x + U
    · rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1]
      have key : hs - (p * U⁻¹ * (x * U + (q - x) * U - (q - x) ^ 2 / 2) - c * q +
          U⁻¹ * ((p - c) * (q ^ 2 - x ^ 2) / 2 +
            (x + U - q) * ((p - c) * q + (x + U - q) / 2 * ((p - c) ^ 2 / p)))) =
          (Δ * (q - x) - U * (p ^ 2 - c ^ 2)) ^ 2 / (2 * U * p * Δ) := by
        rw [hhs, hΔ]; field_simp; ring
      have : 0 ≤ (Δ * (q - x) - U * (p ^ 2 - c ^ 2)) ^ 2 / (2 * U * p * Δ) := by positivity
      linarith
    · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]
      push Not at h1
      have key : hs - (p * U⁻¹ * (x * U + U ^ 2 / 2) - c * q + (p - c) * (x + U / 2)) =
          (U * c * p) ^ 2 / (2 * U * p * Δ) + c * (q - x - U) := by
        rw [hhs, hΔ]; field_simp; ring
      have : 0 ≤ (U * c * p) ^ 2 / (2 * U * p * Δ) := by positivity
      have : 0 ≤ c * (q - x - U) := mul_nonneg hc (by linarith)
      linarith
  have hQs0 : 0 ≤ Qs := by positivity
  have hG : IsGreatest (vN p c x U '' {Q : ℝ × ℝ | 0 ≤ Q.1 ∧ 0 ≤ Q.2}) (2 * hs) := by
    refine ⟨⟨(Qs, Qs), ⟨hQs0, hQs0⟩, ?_⟩, ?_⟩
    · rw [vN_split p c x U hc hcp hx hU]; simp only; rw [hval]; ring
    · rintro _ ⟨Q, ⟨h1, h2⟩, rfl⟩
      rw [vN_split p c x U hc hcp hx hU]
      linarith [hbound Q.1 h1, hbound Q.2 h2]
  have hV : VN p c x U = 2 * hs := hG.csSup_eq
  refine ⟨?_, ?_⟩
  · rw [hV, vN_split p c x U hc hcp hx hU]; simp only; rw [hval]; ring
  · rw [hV, hhs]; ring
