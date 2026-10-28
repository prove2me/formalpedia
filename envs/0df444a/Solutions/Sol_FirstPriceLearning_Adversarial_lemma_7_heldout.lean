-- Prove2me | solution 1 for FirstPriceLearning.Adversarial.lemma_7_heldout
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:53:16.544427+00:00
-- url     : https://prove2.me/submissions/bb341336-b300-4ef8-9762-cfabf7acd806

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory ProbabilityTheory


namespace FPA2bConc

theorem chernoff_pi {n : ℕ} (μG : Measure ℝ) [IsProbabilityMeasure μG] (f : Fin n → ℝ → ℝ)
    (hf : ∀ s, Measurable (f s)) (B : ℝ) (hb : ∀ s x, |f s x| ≤ B) (lam : ℝ) (hlam : 0 ≤ lam)
    (y : ℝ) :
    (Measure.pi fun _ : Fin n => μG) {m | y ≤ ∑ s, f s (m s)} ≤
      ENNReal.ofReal (Real.exp (-lam * y) * ∏ s, ∫ x, Real.exp (lam * f s x) ∂μG) := by
  set μ := Measure.pi fun _ : Fin n => μG
  have hmeas : Measurable (fun m : Fin n → ℝ => ∑ s, f s (m s)) :=
    Finset.measurable_sum _ (fun s _ => (hf s).comp (measurable_pi_apply s))
  have hint : Integrable (fun m : Fin n → ℝ => Real.exp (lam * ∑ s, f s (m s))) μ := by
    refine Integrable.of_bound (C := Real.exp (lam * (n * B))) ?_ ?_
    · exact (Real.measurable_exp.comp (hmeas.const_mul lam)).aestronglyMeasurable
    · refine ae_of_all _ (fun m => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hlam
      calc ∑ s, f s (m s) ≤ ∑ _s : Fin n, B :=
            Finset.sum_le_sum (fun s _ => le_trans (le_abs_self _) (hb s _))
        _ = n * B := by simp
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  refine (measure_ge_le_exp_mul_mgf y hlam hint).trans_eq ?_
  congr 1
  unfold mgf
  have : (fun m : Fin n → ℝ => Real.exp (lam * ∑ s, f s (m s))) =
      fun m => ∏ s, Real.exp (lam * f s (m s)) := by
    funext m
    rw [Finset.mul_sum, Real.exp_sum]
  rw [this]
  exact integral_fintype_prod_eq_prod (fun s x => Real.exp (lam * f s x))

end FPA2bConc

namespace FPA2bHO

open FirstPriceLearning.Adversarial FPA2bConc

theorem record_le (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v y : ℕ → ℝ) (t : ℕ)
    (ht : t ≤ initLength T) :
    record T γ sel v y t = ((t - 1) / numGrid T, 0) := by
  rw [record]; simp [ht]

theorem numGrid_pos (T : ℕ) (hT : 1 ≤ T) : 1 ≤ numGrid T := by
  unfold numGrid
  apply Nat.one_le_iff_ne_zero.mpr
  intro h0
  rw [Nat.ceil_eq_zero] at h0
  have : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  linarith

theorem numGrid_le (T : ℕ) (hT : 1 ≤ T) : numGrid T ≤ T := by
  unfold numGrid
  rw [Nat.ceil_le]
  have h1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  calc Real.sqrt T ≤ Real.sqrt ((T : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = T := Real.sqrt_sq (by linarith)

theorem numGrid_le_init (T : ℕ) : numGrid T ≤ initLength T := by
  unfold initLength
  nlinarith

/-- The bid at an initialization round is `0`. -/
theorem mlBids_init (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ) (t : Fin T)
    (ht : t.val + 1 ≤ initLength T) : mlBids T γ sel v m t = 0 := by
  unfold mlBids runBids
  rw [runBidsNat]
  simp only [dif_pos t.isLt]
  unfold mlRule
  rw [record_le T γ sel _ _ _ ht]
  simp [grid]

theorem levelSet0_run (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (hT : 1 ≤ T) :
    levelSet (runRecord T γ sel v m) 0 (initLength T) = Finset.Icc 1 (numGrid T) := by
  have hK := numGrid_pos T hT
  have hKi := numGrid_le_init T
  ext s
  unfold levelSet runRecord
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [record_le T γ sel _ _ s h2] at h3
    simp only at h3
    refine ⟨h1, ?_⟩
    by_contra hc
    push Not at hc
    have : 1 ≤ (s - 1) / numGrid T := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, by omega⟩, ?_⟩
    rw [record_le T γ sel _ _ s (by omega)]
    simp only
    exact Nat.div_eq_of_lt (by omega)

theorem grid_nonneg (K j : ℕ) : 0 ≤ grid K j := by
  unfold grid; positivity

/-- The held-out estimate of the run, as an average over the first `K` HOBs. -/
theorem phat0_run (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (hT : 1 ≤ T) (j : ℕ) :
    phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j =
      (numGrid T : ℝ)⁻¹ * ∑ s : Fin T, (if s.val < numGrid T then
        (if grid (numGrid T) j < m s ∧ m s ≤ grid (numGrid T) (j + 1) then (1 : ℝ) else 0)
        else 0) := by
  have hK := numGrid_pos T hT
  have hKT := numGrid_le T hT
  have hKi := numGrid_le_init T
  unfold phat0
  rw [levelSet0_run T γ sel v m hT, Nat.card_Icc, Nat.add_sub_cancel]
  congr 1
  -- reindex the sum over `Icc 1 K` as a sum over `Fin T`
  symm
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun s _ => s.val + 1) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simp only [Finset.mem_Icc]; omega
  · intro a ha b hb hab
    exact Fin.ext (by omega)
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    refine ⟨⟨s - 1, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · simp only; omega
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    unfold runFeedback paperSeq
    rw [dif_pos ⟨by omega, by omega⟩]
    have hs' : (⟨s.val + 1 - 1, by omega⟩ : Fin T) = s := Fin.ext (by simp)
    rw [hs']
    have hb : mlBids T γ sel v m s = 0 := mlBids_init T γ sel v m s (by omega)
    have h0 := grid_nonneg (numGrid T) j
    have key : (grid (numGrid T) j < m s ∧ m s ≤ grid (numGrid T) (j + 1)) ↔
        (grid (numGrid T) j < max 0 (m s) ∧ max 0 (m s) ≤ grid (numGrid T) (j + 1)) := by
      constructor
      · rintro ⟨a, b⟩
        have : 0 < m s := lt_of_le_of_lt h0 a
        rw [max_eq_right this.le]; exact ⟨a, b⟩
      · rintro ⟨a, b⟩
        have h1 : 0 < max 0 (m s) := lt_of_le_of_lt h0 a
        have hm : 0 < m s := by
          by_contra hc; push Not at hc; rw [max_eq_left hc] at h1; exact lt_irrefl _ h1
        rw [max_eq_right hm.le] at a b; exact ⟨a, b⟩
    simp only [hb, key]

/-- Moment generating function of an interval indicator. -/
theorem integral_exp_ind (μG : Measure ℝ) [IsProbabilityMeasure μG] (a b lam : ℝ) :
    ∫ x, Real.exp (lam * (if a < x ∧ x ≤ b then (1 : ℝ) else 0)) ∂μG =
      1 + (Real.exp lam - 1) * μG.real (Set.Ioc a b) := by
  have : (fun x => Real.exp (lam * (if a < x ∧ x ≤ b then (1 : ℝ) else 0))) =
      fun x => 1 + (Real.exp lam - 1) * (Set.Ioc a b).indicator (1 : ℝ → ℝ) x := by
    funext x
    by_cases h : a < x ∧ x ≤ b
    · have hx : x ∈ Set.Ioc a b := h
      simp [h, hx]
    · have hx : x ∉ Set.Ioc a b := h
      simp [h, hx]
  rw [this, integral_add (integrable_const _), integral_const_mul,
    integral_indicator_one measurableSet_Ioc]
  · simp
  · exact (integrable_const _).indicator measurableSet_Ioc |>.const_mul _

theorem prod_mgf_le {T : ℕ} (μG : Measure ℝ) [IsProbabilityMeasure μG] (K : ℕ) (hKT : K ≤ T)
    (a b lam : ℝ) (sgn : ℝ) :
    ∏ s : Fin T, ∫ x, Real.exp (lam * (sgn * (if s.val < K then
        (if a < x ∧ x ≤ b then (1 : ℝ) else 0) else 0))) ∂μG ≤
      Real.exp (K * (μG.real (Set.Ioc a b) * (Real.exp (lam * sgn) - 1))) := by
  have hp0 : 0 ≤ μG.real (Set.Ioc a b) := measureReal_nonneg
  have hfac : ∀ s : Fin T, ∫ x, Real.exp (lam * (sgn * (if s.val < K then
        (if a < x ∧ x ≤ b then (1 : ℝ) else 0) else 0))) ∂μG =
      if s.val < K then 1 + (Real.exp (lam * sgn) - 1) * μG.real (Set.Ioc a b) else 1 := by
    intro s
    by_cases hs : s.val < K
    · simp only [hs, if_true]
      rw [← integral_exp_ind μG a b (lam * sgn)]
      congr 1; funext x; ring_nf
    · simp [hs]
  simp only [hfac]
  have hle : ∀ s : Fin T, (if s.val < K then
      1 + (Real.exp (lam * sgn) - 1) * μG.real (Set.Ioc a b) else 1) ≤
      Real.exp (if s.val < K then μG.real (Set.Ioc a b) * (Real.exp (lam * sgn) - 1) else 0) := by
    intro s
    split_ifs
    · have := Real.add_one_le_exp ((Real.exp (lam * sgn) - 1) * μG.real (Set.Ioc a b))
      rw [mul_comm] at this ⊢
      linarith [mul_comm (μG.real (Set.Ioc a b)) (Real.exp (lam * sgn) - 1)]
    · simp
  have hnn : ∀ s : Fin T, 0 ≤ (if s.val < K then
      1 + (Real.exp (lam * sgn) - 1) * μG.real (Set.Ioc a b) else (1 : ℝ)) := by
    intro s
    split_ifs
    · have hp1 : μG.real (Set.Ioc a b) ≤ 1 := measureReal_le_one
      have he : 0 < Real.exp (lam * sgn) := Real.exp_pos _
      nlinarith
    · norm_num
  calc _ ≤ ∏ s : Fin T, Real.exp (if s.val < K then
        μG.real (Set.Ioc a b) * (Real.exp (lam * sgn) - 1) else 0) :=
        Finset.prod_le_prod (fun s _ => hnn s) (fun s _ => hle s)
    _ = Real.exp (K * (μG.real (Set.Ioc a b) * (Real.exp (lam * sgn) - 1))) := by
        rw [← Real.exp_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul, Fin.card_filter_val_lt, min_eq_right hKT]

theorem intervalProb_eq (T : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG] (j : ℕ) :
    intervalProb T μG j =
      μG.real (Set.Ioc (grid (numGrid T) j) (grid (numGrid T) (j + 1))) := by
  have hab : grid (numGrid T) j ≤ grid (numGrid T) (j + 1) := by
    unfold grid
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    push_cast; linarith
  unfold intervalProb FirstPriceLearning.Stochastic.cdf
  rw [← Set.Iic_union_Ioc_eq_Iic hab]
  rw [show (μG (Set.Iic (grid (numGrid T) j) ∪
      Set.Ioc (grid (numGrid T) j) (grid (numGrid T) (j + 1)))).toReal =
      μG.real (Set.Iic (grid (numGrid T) j) ∪
      Set.Ioc (grid (numGrid T) j) (grid (numGrid T) (j + 1))) from rfl]
  rw [measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  simp [Measure.real]

theorem exp_neg_three_log (x : ℝ) (hx : 0 < x) : Real.exp (-(3 * Real.log x)) = 1 / x ^ 3 := by
  rw [Real.exp_neg, show (3 : ℝ) * Real.log x = ((3 : ℕ) : ℝ) * Real.log x by norm_num,
    Real.exp_nat_mul, Real.exp_log hx]
  simp

theorem heldout (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (v : Fin T → ℝ) (μG : Measure ℝ) [IsProbabilityMeasure μG]
    (j : ℕ) (hj : j < numGrid T) :
    (Measure.pi fun _ : Fin T => μG)
        {m | ¬ (intervalProb T μG j ≤
              2 * (phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j
                + γ * Real.log ((numGrid T : ℝ) * (T : ℝ)) / (numGrid T : ℝ)) ∧
            phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j ≤
              2 * (intervalProb T μG j
                + γ * Real.log ((numGrid T : ℝ) * (T : ℝ)) / (numGrid T : ℝ)))}
      ≤ ENNReal.ofReal (2 / ((numGrid T : ℝ) * (T : ℝ)) ^ 3) := by
  have hT : 1 ≤ T := by
    by_contra h; push Not at h
    interval_cases T; simp [numGrid] at hj
  have hK := numGrid_pos T hT
  have hKT := numGrid_le T hT
  set K := numGrid T with hKdef
  set a0 := grid K j
  set b0 := grid K (j + 1)
  set p := intervalProb T μG j with hpdef
  have hp : p = μG.real (Set.Ioc a0 b0) := intervalProb_eq T μG j
  have hp0 : 0 ≤ p := by rw [hp]; exact measureReal_nonneg
  set l0 := Real.log ((K : ℝ) * (T : ℝ)) with hl0
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hKTpos : (0 : ℝ) < (K : ℝ) * (T : ℝ) := by positivity
  have hl0nn : 0 ≤ l0 := Real.log_nonneg (by nlinarith)
  set F : ℝ → Fin T → ℝ → ℝ := fun sg s x =>
    sg * (if s.val < K then (if a0 < x ∧ x ≤ b0 then (1 : ℝ) else 0) else 0) with hF
  have hFmeas : ∀ sg s, Measurable (F sg s) := by
    intro sg s
    apply Measurable.const_mul
    by_cases hs : s.val < K
    · simp only [hs, if_true]
      apply Measurable.ite _ measurable_const measurable_const
      exact measurableSet_Ioc
    · simp only [hs, if_false]; exact measurable_const
  have hFb : ∀ s x, |F 1 s x| ≤ 1 ∧ |F (-1) s x| ≤ 1 := by
    intro s x
    simp only [hF]
    split_ifs <;> norm_num
  -- the inclusion
  have hsub : {m : Fin T → ℝ | ¬ (p ≤
              2 * (phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j
                + γ * l0 / (K : ℝ)) ∧
            phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j ≤
              2 * (p + γ * l0 / (K : ℝ)))} ⊆
      {m | 2 * K * p + 2 * (γ * l0) ≤ ∑ s, F 1 s (m s)} ∪
      {m | γ * l0 - K * p / 2 ≤ ∑ s, F (-1) s (m s)} := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    rw [phat0_run T γ sel v m hT j] at hm
    set Z := ∑ s : Fin T, (if s.val < K then
        (if a0 < m s ∧ m s ≤ b0 then (1 : ℝ) else 0) else 0) with hZ
    have hZ1 : ∑ s, F 1 s (m s) = Z := by simp [hF, hZ]
    have hZ2 : ∑ s, F (-1) s (m s) = -Z := by
      simp only [hF, hZ, neg_one_mul, Finset.sum_neg_distrib]
    simp only [Set.mem_union, Set.mem_setOf_eq, hZ1, hZ2]
    have hKpos : (0 : ℝ) < K := by linarith
    rw [not_and_or] at hm
    rcases hm with h | h
    · right
      push Not at h
      have : 2 * ((K : ℝ)⁻¹ * Z + γ * l0 / K) * K = 2 * Z + 2 * γ * l0 := by
        field_simp
      have h2 := mul_lt_mul_of_pos_right h hKpos
      nlinarith
    · left
      push Not at h
      have : 2 * (p + γ * l0 / K) * K = 2 * K * p + 2 * γ * l0 := by
        field_simp
      have h2 := mul_lt_mul_of_pos_right h hKpos
      have : (K : ℝ)⁻¹ * Z * K = Z := by field_simp
      nlinarith
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hei : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hbound : Real.exp (-(γ * l0)) ≤ 1 / ((K : ℝ) * (T : ℝ)) ^ 3 := by
    rw [← exp_neg_three_log _ hKTpos]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hU : (Measure.pi fun _ : Fin T => μG) {m | 2 * K * p + 2 * (γ * l0) ≤ ∑ s, F 1 s (m s)}
      ≤ ENNReal.ofReal (1 / ((K : ℝ) * (T : ℝ)) ^ 3) := by
    refine le_trans (chernoff_pi μG (F 1) (hFmeas 1) 1 (fun s x => (hFb s x).1) 1 zero_le_one _)
      (ENNReal.ofReal_le_ofReal ?_)
    have hprod := prod_mgf_le μG K hKT a0 b0 1 1
    rw [← hp] at hprod
    refine le_trans (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le) ?_
    rw [← Real.exp_add]
    refine le_trans (Real.exp_le_exp.mpr ?_) hbound
    simp only [mul_one]
    have : 0 ≤ (K : ℝ) * p := by positivity
    nlinarith
  have hL : (Measure.pi fun _ : Fin T => μG) {m | γ * l0 - K * p / 2 ≤ ∑ s, F (-1) s (m s)}
      ≤ ENNReal.ofReal (1 / ((K : ℝ) * (T : ℝ)) ^ 3) := by
    refine le_trans (chernoff_pi μG (F (-1)) (hFmeas (-1)) 1 (fun s x => (hFb s x).2) 1
      zero_le_one _) (ENNReal.ofReal_le_ofReal ?_)
    have hprod := prod_mgf_le μG K hKT a0 b0 1 (-1)
    rw [← hp] at hprod
    refine le_trans (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le) ?_
    rw [← Real.exp_add]
    refine le_trans (Real.exp_le_exp.mpr ?_) hbound
    simp only [one_mul]
    have : 0 ≤ (K : ℝ) * p := by positivity
    nlinarith
  refine le_trans (add_le_add hU hL) ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  ring_nf
  rfl

end FPA2bHO

open FirstPriceLearning.Adversarial in
theorem solution (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (j : ℕ) (hj : j < numGrid T) :
    (Measure.pi fun _ : Fin T => μG)
        {m | ¬ (intervalProb T μG j ≤
              2 * (phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j
                + γ * Real.log ((numGrid T : ℝ) * (T : ℝ)) / (numGrid T : ℝ)) ∧
            phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j ≤
              2 * (intervalProb T μG j
                + γ * Real.log ((numGrid T : ℝ) * (T : ℝ)) / (numGrid T : ℝ)))}
      ≤ ENNReal.ofReal (2 / ((numGrid T : ℝ) * (T : ℝ)) ^ 3) :=
  FPA2bHO.heldout T γ hγ sel v μG j hj
