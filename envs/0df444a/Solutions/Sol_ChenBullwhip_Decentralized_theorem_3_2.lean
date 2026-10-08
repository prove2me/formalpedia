-- Prove2me | solution 1 for ChenBullwhip.Decentralized.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:41:01.767432+00:00
-- url     : https://prove2.me/submissions/6b5dafca-bddf-4f57-93a5-b651059848d8

import Mathlib
import Definitions.Def_ChenBullwhip_Decentralized_IIDDemand
import Definitions.Def_ChenBullwhip_Decentralized_Chain

open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace ChenBullwhipThm32Aux

open ChenBullwhip.Decentralized

/-- telescoping of a window sum -/
lemma window_diff (f : ℕ → ℝ) (p : ℕ) :
    ∑ j ∈ Finset.range p, f j - ∑ j ∈ Finset.range p, f (j + 1) = f 0 - f p := by
  have h := Finset.sum_range_succ f p
  have h' := Finset.sum_range_succ' f p
  linarith

lemma sum_Icc_one_eq_range (g : ℕ → ℝ) (p : ℕ) :
    ∑ i ∈ Finset.Icc 1 p, g i = ∑ j ∈ Finset.range p, g (j + 1) := by
  induction p with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- one-step recursion: `q^{k+1}_t = (1 + a) q^k_t - a q^k_{t-p}` with `a = L_{k+1}/p`. -/
lemma stageOrder_succ_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : IIDDemand P) (p : ℕ) (hp : 1 ≤ p) (L : ℕ → ℕ) (k : ℕ) (t : ℤ) (ω : Ω) :
    X.stageOrder p L (k + 1) t ω =
      (1 + (L (k + 1) : ℝ) / p) * X.stageOrder p L k t ω
        - (L (k + 1) : ℝ) / p * X.stageOrder p L k (t - p) ω := by
  have hp' : (p : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  -- uniform forecast: in both cases it is the window average of `q^k`
  have hF : ∀ s : ℤ, X.stageForecast p (k + 1) (X.stageOrder p L k) s ω
      = (∑ j ∈ Finset.range p, X.stageOrder p L k (s - j) ω) / p := by
    intro s
    unfold IIDDemand.stageForecast
    split_ifs with h1
    · have hk : k = 0 := by omega
      subst hk
      congr 1
      rw [sum_Icc_one_eq_range (fun i => X.D (s - i) ω)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [IIDDemand.stageOrder]
      congr 1
      push_cast
      ring
    · rfl
  have hwin := window_diff (fun j => X.stageOrder p L k (t - j) ω) p
  have hshift : ∀ j : ℕ, X.stageOrder p L k (t - 1 - j) ω
      = X.stageOrder p L k (t - ((j + 1 : ℕ) : ℤ)) ω := by
    intro j; congr 1; push_cast; ring
  rw [IIDDemand.stageOrder]
  beta_reduce
  rw [hF t, hF (t - 1)]
  simp only [hshift]
  simp only [Nat.cast_zero, sub_zero] at hwin
  field_simp
  linear_combination (L (k + 1) : ℝ) * hwin

/-- the (sign-stripped) coefficients of `q^k` on the errors `ε_{t-1-jp}` -/
noncomputable def coef (p : ℕ) (L : ℕ → ℕ) : ℕ → ℕ → ℝ
  | 0 => fun j => if j = 0 then 1 else 0
  | k + 1 => fun j => (1 + (L (k + 1) : ℝ) / p) * coef p L k j
      + (L (k + 1) : ℝ) / p * (if j = 0 then 0 else coef p L k (j - 1))

lemma coef_zero_of_lt (p : ℕ) (L : ℕ → ℕ) (k : ℕ) : ∀ j, k < j → coef p L k j = 0 := by
  induction k with
  | zero =>
    intro j hj
    simp only [coef]
    rw [if_neg (by omega)]
  | succ n ih =>
    intro j hj
    simp only [coef]
    rw [ih j (by omega), if_neg (by omega), ih (j - 1) (by omega)]
    ring

lemma coef_nonneg (p : ℕ) (L : ℕ → ℕ) (k : ℕ) : ∀ j, 0 ≤ coef p L k j := by
  induction k with
  | zero =>
    intro j
    simp only [coef]
    split_ifs <;> norm_num
  | succ n ih =>
    intro j
    simp only [coef]
    have ha : 0 ≤ (L (n + 1) : ℝ) / p := by positivity
    have h1 := ih j
    have h2 : 0 ≤ (if j = 0 then (0 : ℝ) else coef p L n (j - 1)) := by
      split_ifs
      · exact le_refl _
      · exact ih _
    positivity

lemma coef_sq_sum (p : ℕ) (L : ℕ → ℕ) (k : ℕ) :
    ∏ i ∈ Finset.Icc 1 k, ((1 + (L i : ℝ) / p) ^ 2 + ((L i : ℝ) / p) ^ 2)
      ≤ ∑ j ∈ Finset.range (k + 1), (coef p L k j) ^ 2 := by
  induction k with
  | zero => simp [coef]
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    set a : ℝ := (L (n + 1) : ℝ) / p with ha_def
    have ha : 0 ≤ a := by positivity
    have hterm : ∀ j ∈ Finset.range (n + 1 + 1),
        (1 + a) ^ 2 * (coef p L n j) ^ 2
          + a ^ 2 * (if j = 0 then (0 : ℝ) else coef p L n (j - 1)) ^ 2
          ≤ (coef p L (n + 1) j) ^ 2 := by
      intro j _
      simp only [coef]
      rw [← ha_def]
      have h1 := coef_nonneg p L n j
      have h2 : 0 ≤ (if j = 0 then (0 : ℝ) else coef p L n (j - 1)) := by
        split_ifs
        · exact le_refl _
        · exact coef_nonneg p L n _
      nlinarith [mul_nonneg (mul_nonneg ha (by linarith : (0:ℝ) ≤ 1 + a)) (mul_nonneg h1 h2)]
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hA : ∑ j ∈ Finset.range (n + 1 + 1), (coef p L n j) ^ 2
        = ∑ j ∈ Finset.range (n + 1), (coef p L n j) ^ 2 := by
      rw [Finset.sum_range_succ, coef_zero_of_lt p L n (n + 1) (by omega)]
      ring
    have hB : ∑ j ∈ Finset.range (n + 1 + 1),
        (if j = 0 then (0 : ℝ) else coef p L n (j - 1)) ^ 2
        = ∑ j ∈ Finset.range (n + 1), (coef p L n j) ^ 2 := by
      rw [Finset.sum_range_succ']
      simp
    rw [hA, hB] at hsum
    have hP : 0 ≤ (1 + a) ^ 2 + a ^ 2 := by positivity
    calc (∏ i ∈ Finset.Icc 1 n, ((1 + (L i : ℝ) / p) ^ 2 + ((L i : ℝ) / p) ^ 2))
          * ((1 + a) ^ 2 + a ^ 2)
        ≤ (∑ j ∈ Finset.range (n + 1), (coef p L n j) ^ 2) * ((1 + a) ^ 2 + a ^ 2) :=
          mul_le_mul_of_nonneg_right ih hP
      _ = (1 + a) ^ 2 * ∑ j ∈ Finset.range (n + 1), (coef p L n j) ^ 2
          + a ^ 2 * ∑ j ∈ Finset.range (n + 1), (coef p L n j) ^ 2 := by ring
      _ ≤ _ := hsum

/-- representation of `q^k_t` as `μ + ∑_j (-1)^j c_j ε_{t-1-jp}`. -/
lemma stageOrder_repr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : IIDDemand P) (p : ℕ) (hp : 1 ≤ p) (L : ℕ → ℕ) (k : ℕ) :
    ∀ (t : ℤ) (ω : Ω), X.stageOrder p L k t ω = X.mu
      + ∑ j ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ j * coef p L k j * X.eps (t - 1 - (j : ℤ) * p) ω := by
  induction k with
  | zero =>
    intro t ω
    simp [IIDDemand.stageOrder, IIDDemand.D, coef]
  | succ n ih =>
    intro t ω
    rw [stageOrder_succ_eq X p hp L n t ω, ih t ω, ih (t - p) ω]
    set a : ℝ := (L (n + 1) : ℝ) / p with ha_def
    have hsplit : ∑ j ∈ Finset.range (n + 1 + 1),
        (-1 : ℝ) ^ j * coef p L (n + 1) j * X.eps (t - 1 - (j : ℤ) * p) ω
        = ∑ j ∈ Finset.range (n + 1 + 1),
            (1 + a) * ((-1 : ℝ) ^ j * coef p L n j * X.eps (t - 1 - (j : ℤ) * p) ω)
          + ∑ j ∈ Finset.range (n + 1 + 1),
            a * ((-1 : ℝ) ^ j * (if j = 0 then (0 : ℝ) else coef p L n (j - 1))
              * X.eps (t - 1 - (j : ℤ) * p) ω) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [coef]
      rw [← ha_def]
      ring
    have hA : ∑ j ∈ Finset.range (n + 1 + 1),
            (1 + a) * ((-1 : ℝ) ^ j * coef p L n j * X.eps (t - 1 - (j : ℤ) * p) ω)
        = (1 + a) * ∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ j * coef p L n j * X.eps (t - 1 - (j : ℤ) * p) ω := by
      rw [Finset.sum_range_succ, coef_zero_of_lt p L n (n + 1) (by omega), ← Finset.mul_sum]
      ring
    have hB : ∑ j ∈ Finset.range (n + 1 + 1),
            a * ((-1 : ℝ) ^ j * (if j = 0 then (0 : ℝ) else coef p L n (j - 1))
              * X.eps (t - 1 - (j : ℤ) * p) ω)
        = -(a * ∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ j * coef p L n j * X.eps (t - p - 1 - (j : ℤ) * p) ω) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, ← Finset.sum_neg_distrib]
      simp only [if_pos, mul_zero, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [if_neg (by omega), Nat.add_sub_cancel]
      have : t - 1 - ((j + 1 : ℕ) : ℤ) * p = t - p - 1 - (j : ℤ) * p := by push_cast; ring
      rw [this, pow_succ]
      ring
    rw [hsplit, hA, hB]
    ring


lemma variance_repr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : IIDDemand P) (p : ℕ) (hp : 1 ≤ p) (N : ℕ) (c : ℕ → ℝ) (t : ℤ) :
    variance (fun ω => X.mu + ∑ j ∈ Finset.range N, c j * X.eps (t - 1 - (j : ℤ) * p) ω) P
      = X.sigma ^ 2 * ∑ j ∈ Finset.range N, (c j) ^ 2 := by
  set Y : ℕ → Ω → ℝ := fun j ω => c j * X.eps (t - 1 - (j : ℤ) * p) ω with hY
  have hYm : ∀ j, Measurable (Y j) := fun j =>
    measurable_const.mul (X.measurable_eps _)
  have hfun : (fun ω => X.mu + ∑ j ∈ Finset.range N, c j * X.eps (t - 1 - (j : ℤ) * p) ω)
      = fun ω => X.mu + (∑ j ∈ Finset.range N, Y j) ω := by
    funext ω
    rw [Finset.sum_apply]
  have hm : AEMeasurable (∑ j ∈ Finset.range N, Y j) P :=
    Finset.aemeasurable_sum _ (fun j _ => (hYm j).aemeasurable)
  rw [hfun, variance_const_add hm.aestronglyMeasurable]
  have hL : ∀ j ∈ Finset.range N, MemLp (Y j) 2 P := fun j _ =>
    (X.memLp _).const_mul (c j)
  have hpair : Set.Pairwise ↑(Finset.range N) fun i j => IndepFun (Y i) (Y j) P := by
    intro i _ j _ hij
    have hne : t - 1 - (i : ℤ) * p ≠ t - 1 - (j : ℤ) * p := by
      intro h
      apply hij
      have hp0 : (p : ℤ) ≠ 0 := by omega
      have : (i : ℤ) * p = (j : ℤ) * p := by linarith
      exact_mod_cast mul_right_cancel₀ hp0 this
    exact (X.indep.indepFun hne).comp (measurable_const.mul measurable_id)
      (measurable_const.mul measurable_id)
  rw [IndepFun.variance_sum hL hpair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  show variance (fun ω => c j * X.eps (t - 1 - (j : ℤ) * p) ω) P = _
  rw [variance_const_mul, X.variance_eq]
  ring

end ChenBullwhipThm32Aux

open MeasureTheory ProbabilityTheory ChenBullwhip.Decentralized in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : IIDDemand P) (p : ℕ) (hp : 1 ≤ p) (L : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k) (t : ℤ) :
    variance (X.stageOrder p L k t) P / variance (X.D t) P
      ≥ ∏ i ∈ Finset.Icc 1 k, (1 + 2 * (L i : ℝ) / p + 2 * (L i : ℝ) ^ 2 / (p : ℝ) ^ 2) := by
  have hp' : (p : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hrepr : X.stageOrder p L k t = fun ω => X.mu
      + ∑ j ∈ Finset.range (k + 1),
          ((-1 : ℝ) ^ j * ChenBullwhipThm32Aux.coef p L k j) * X.eps (t - 1 - (j : ℤ) * p) ω := by
    funext ω
    exact ChenBullwhipThm32Aux.stageOrder_repr X p hp L k t ω
  have hVarQ : variance (X.stageOrder p L k t) P
      = X.sigma ^ 2 * ∑ j ∈ Finset.range (k + 1), (ChenBullwhipThm32Aux.coef p L k j) ^ 2 := by
    rw [hrepr, ChenBullwhipThm32Aux.variance_repr X p hp (k + 1)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  have hVarD : variance (X.D t) P = X.sigma ^ 2 := by
    have : X.D t = fun ω => X.mu + X.eps t ω := rfl
    rw [this, variance_const_add (X.measurable_eps t).aestronglyMeasurable, X.variance_eq]
  have hs2 : 0 < X.sigma ^ 2 := by have := X.sigma_pos; positivity
  rw [hVarQ, hVarD, mul_div_cancel_left₀ _ hs2.ne']
  have hfac : ∀ i ∈ Finset.Icc 1 k,
      (1 + 2 * (L i : ℝ) / p + 2 * (L i : ℝ) ^ 2 / (p : ℝ) ^ 2)
        = (1 + (L i : ℝ) / p) ^ 2 + ((L i : ℝ) / p) ^ 2 := by
    intro i _
    field_simp
    ring
  rw [Finset.prod_congr rfl hfac]
  exact ChenBullwhipThm32Aux.coef_sq_sum p L k
