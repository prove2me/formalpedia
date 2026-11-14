-- Prove2me | solution 1 for BosonicLearn.geometric_threshold_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:11:02.795226+00:00
-- url     : https://prove2.me/submissions/5eb4a07a-1015-4461-a509-d55d37d7ae8d

import Mathlib
import Theorems.Thm_BosonicLearn_geometric_pgf_threshold

open BosonicLearn

noncomputable section

/-! ### The binomial kernel, defined by Pascal's recursion -/

/-- `binK η k j = Pr(Bin(k, η) = j) = (k choose j) η^j (1-η)^(k-j)`, defined by Pascal's recursion. -/
private def binK (η : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => (1 - η) * binK η k 0
  | k + 1, j + 1 => (1 - η) * binK η k (j + 1) + η * binK η k j

private lemma binK_nonneg {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) : ∀ k j, 0 ≤ binK η k j
  | 0, 0 => by simp [binK]
  | 0, _ + 1 => by simp [binK]
  | k + 1, 0 => by
      simp only [binK]
      exact mul_nonneg (by linarith) (binK_nonneg h0 h1 k 0)
  | k + 1, j + 1 => by
      simp only [binK]
      exact add_nonneg (mul_nonneg (by linarith) (binK_nonneg h0 h1 k (j + 1)))
        (mul_nonneg h0 (binK_nonneg h0 h1 k j))

private lemma binK_eq_zero (η : ℝ) : ∀ k j, k < j → binK η k j = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => by simp [binK]
  | k + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, j + 1, h => by
      simp only [binK]
      rw [binK_eq_zero η k (j + 1) (by omega), binK_eq_zero η k j (by omega)]
      ring

/-- `binE η k a = E[a(Bin(k, η))]`. -/
private def binE (η : ℝ) (k : ℕ) (a : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range (k + 1), binK η k j * a j

private lemma binE_zero (η : ℝ) (a : ℕ → ℝ) : binE η 0 a = a 0 := by
  simp [binE, binK]

private lemma binE_succ (η : ℝ) (k : ℕ) (a : ℕ → ℝ) :
    binE η (k + 1) a = (1 - η) * binE η k a + η * binE η k (fun j => a (j + 1)) := by
  have h1 : ∑ j ∈ Finset.range (k + 1 + 1), binK η k j * a j = binE η k a := by
    rw [Finset.sum_range_succ, binK_eq_zero η k (k + 1) (Nat.lt_succ_self k)]
    simp [binE]
  have h2 : ∑ j ∈ Finset.range (k + 1 + 1), binK η k j * a j
      = ∑ j ∈ Finset.range (k + 1), binK η k (j + 1) * a (j + 1) + binK η k 0 * a 0 :=
    Finset.sum_range_succ' _ _
  unfold binE at *
  rw [Finset.sum_range_succ', ← h1, h2]
  simp only [binK]
  rw [Finset.mul_sum, mul_add, Finset.mul_sum, add_assoc, add_comm ((1 - η) * (binK η k 0 * a 0)),
    ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · ring

private lemma binE_nonneg {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (k : ℕ) {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) :
    0 ≤ binE η k a :=
  Finset.sum_nonneg fun j _ => mul_nonneg (binK_nonneg h0 h1 k j) (ha j)

private lemma binE_mono {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (k : ℕ) {a b : ℕ → ℝ} (hab : ∀ j, a j ≤ b j) :
    binE η k a ≤ binE η k b :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hab j) (binK_nonneg h0 h1 k j)

private lemma binE_pow (η z : ℝ) : ∀ k : ℕ, binE η k (fun j => z ^ j) = (1 - η + η * z) ^ k
  | 0 => by simp [binE_zero]
  | k + 1 => by
      rw [binE_succ]
      have : binE η k (fun j => z ^ (j + 1)) = z * binE η k (fun j => z ^ j) := by
        unfold binE
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this, binE_pow η z k]
      ring

private lemma binE_one (η : ℝ) (k : ℕ) : binE η k (fun _ => 1) = 1 := by
  have := binE_pow η 1 k
  simpa using this

private lemma binE_le_one {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (k : ℕ) {a : ℕ → ℝ} (ha : ∀ j, a j ≤ 1) :
    binE η k a ≤ 1 :=
  (binE_mono h0 h1 k ha).trans (binE_one η k).le

/-- For a nondecreasing test function the binomial expectation is nondecreasing in the number of trials. -/
private lemma binE_le_succ {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (k : ℕ) {a : ℕ → ℝ}
    (ha : ∀ j, a j ≤ a (j + 1)) : binE η k a ≤ binE η (k + 1) a := by
  rw [binE_succ]
  have := binE_mono h0 h1 k ha
  nlinarith [this]

private lemma hasSum_binK (η : ℝ) (k : ℕ) (a : ℕ → ℝ) :
    HasSum (fun j => binK η k j * a j) (binE η k a) := by
  unfold binE
  refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
  rw [binK_eq_zero η k j (by simpa using hj), zero_mul]

/-! ### Exchanging nonnegative double series -/

private lemma hasSum_swap {F : ℕ → ℕ → ℝ} (hF : ∀ k j, 0 ≤ F k j) {r : ℕ → ℝ} {S : ℝ}
    (hr : ∀ k, HasSum (fun j => F k j) (r k)) (hS : HasSum r S) :
    HasSum (fun j => ∑' k, F k j) S := by
  have hsum : Summable (fun x : ℕ × ℕ => F x.1 x.2) := by
    rw [summable_prod_of_nonneg (fun x => hF x.1 x.2)]
    refine ⟨fun k => (hr k).summable, ?_⟩
    have : (fun k => ∑' j, F k j) = r := funext fun k => (hr k).tsum_eq
    simpa [this] using hS.summable
  have h1 : HasSum (fun x : ℕ × ℕ => F x.1 x.2) S := by
    have h := hsum.hasSum
    have h2 := h.prod_fiberwise hr
    rwa [h2.unique hS] at h
  have h3 : HasSum (fun x : ℕ × ℕ => F x.2 x.1) S := by
    have := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h1
    simpa [Function.comp_def] using this
  refine h3.prod_fiberwise fun j => ?_
  have : Summable (fun k => F k j) := h3.summable.prod_factor j
  exact this.hasSum

/-! ### Binomial thinning of a law on `ℕ` -/

/-- The law of a `Bin(K, η)` variable when `K` has law `p`. -/
private def thin (η : ℝ) (p : ℕ → ℝ) (j : ℕ) : ℝ := ∑' k, p k * binK η k j

private lemma thin_nonneg {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (j : ℕ) :
    0 ≤ thin η p j :=
  tsum_nonneg fun k => mul_nonneg (hp k) (binK_nonneg h0 h1 k j)

private lemma thin_hasSum {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) {S : ℝ} (hS : HasSum (fun k => p k * binE η k a) S) :
    HasSum (fun j => thin η p j * a j) S := by
  have key := hasSum_swap (F := fun k j => p k * (binK η k j * a j))
    (fun k j => mul_nonneg (hp k) (mul_nonneg (binK_nonneg h0 h1 k j) (ha j)))
    (fun k => (hasSum_binK η k a).mul_left (p k)) hS
  have : (fun j => thin η p j * a j) = fun j => ∑' k, p k * (binK η k j * a j) := by
    funext j
    unfold thin
    rw [← tsum_mul_right]
    exact tsum_congr fun k => by ring
  rw [this]
  exact key

/-- A thinned threshold test is a mixture of threshold tests. -/
private lemma abel_hasSum {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : ∀ k, f k ≤ f (k + 1)) {S : ℝ} (hS : HasSum (fun k => p k * f k) S) :
    HasSum (fun t => (f (t + 1) - f t) * ∑' k, if t < k then p k else 0) S := by
  have key := hasSum_swap (F := fun k t => if t < k then p k * (f (t + 1) - f t) else 0)
    (r := fun k => p k * f k)
    (fun k t => by
      split_ifs
      · exact mul_nonneg (hp k) (by linarith [hf t])
      · exact le_rfl)
    (fun k => by
      have h : ∑ t ∈ Finset.range k, (if t < k then p k * (f (t + 1) - f t) else 0) = p k * f k := by
        rw [Finset.sum_congr rfl (g := fun t => p k * (f (t + 1) - f t))
          (fun t ht => if_pos (Finset.mem_range.mp ht)), ← Finset.mul_sum, Finset.sum_range_sub, hf0,
          sub_zero]
      rw [← h]
      refine hasSum_sum_of_ne_finset_zero fun t ht => ?_
      exact if_neg (by simpa using ht)) hS
  have : (fun t => (f (t + 1) - f t) * ∑' k, if t < k then p k else 0)
      = fun t => ∑' k, if t < k then p k * (f (t + 1) - f t) else 0 := by
    funext t
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    split_ifs <;> ring
  rw [this]
  exact key

/-- If a sub-probability mixture of the numbers `D t` is at least `L > 0`, some `D t` is at least `L`. -/
private lemma exists_of_mixture {w D : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hw1 : ∀ n, ∑ t ∈ Finset.range n, w t ≤ 1) {A L : ℝ} (hA : HasSum (fun t => w t * D t) A)
    (hL : 0 < L) (hLA : L ≤ A) : ∃ t, L ≤ D t := by
  by_contra hcon
  push Not at hcon
  have hws : Summable w := summable_of_sum_range_le hw hw1
  have hwt : ∑' t, w t ≤ 1 := Real.tsum_le_of_sum_range_le hw hw1
  by_cases h0 : ∃ t0, 0 < w t0
  · obtain ⟨t0, ht0⟩ := h0
    have hlt : ∑' t, w t * D t < ∑' t, w t * L :=
      Summable.tsum_lt_tsum (i := t0)
        (fun t => mul_le_mul_of_nonneg_left (hcon t).le (hw t))
        (mul_lt_mul_of_pos_left (hcon t0) ht0) hA.summable (hws.mul_right L)
    rw [hA.tsum_eq, tsum_mul_right] at hlt
    nlinarith
  · push Not at h0
    have hz : ∀ t, w t = 0 := fun t => le_antisymm (h0 t) (hw t)
    have : A = 0 := by
      refine hA.unique ?_
      have : (fun t => w t * D t) = fun _ => (0 : ℝ) := by
        funext t
        rw [hz t, zero_mul]
      rw [this]
      exact hasSum_zero
    linarith

/-! ### Numerical facts -/

private lemma scaled_term {Λ l : ℝ} (hΛ : 1 ≤ Λ) (hl : 0 ≤ l) :
    l * (1 + l) / Λ ^ 2 ≤ l / Λ * (1 + l / Λ) := by
  have hΛ0 : 0 < Λ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have : l / Λ * (1 + l / Λ) * Λ ^ 2 = l * Λ + l * l := by
    field_simp
  rw [this]
  nlinarith

private lemma scaled_sq {Λ : ℝ} (hΛ : 1 ≤ Λ) {m : ℕ} {lm : Fin m → ℝ} (hlm : ∀ i, 0 ≤ lm i) {δ : ℝ}
    (h : δ ^ 2 ≤ 1 + ∑ i, lm i * (1 + lm i)) :
    (δ / Λ) ^ 2 ≤ 1 + ∑ i, lm i / Λ * (1 + lm i / Λ) := by
  have hΛ0 : 0 < Λ := by linarith
  have h1 : (δ / Λ) ^ 2 ≤ (1 + ∑ i, lm i * (1 + lm i)) / Λ ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right h (by positivity)
  have h2 : (1 + ∑ i, lm i * (1 + lm i)) / Λ ^ 2 = 1 / Λ ^ 2 + ∑ i, lm i * (1 + lm i) / Λ ^ 2 := by
    rw [add_div, Finset.sum_div]
  have h3 : 1 / Λ ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have h4 : ∑ i, lm i * (1 + lm i) / Λ ^ 2 ≤ ∑ i, lm i / Λ * (1 + lm i / Λ) :=
    Finset.sum_le_sum fun i _ => scaled_term hΛ (hlm i)
  linarith

/-! ### The thinned laws -/

/-- Thinning with probability `1/Λ` divides the means of the geometric variables by `Λ`. -/
private lemma thin_gf {Λ : ℝ} (hΛ : 1 ≤ Λ) {m : ℕ} {l : Fin m → ℝ} {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hG : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → HasSum (fun k => p k * z ^ k) (∏ i, (1 + l i * (1 - z))⁻¹))
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    HasSum (fun j => thin Λ⁻¹ p j * z ^ j) (∏ i, (1 + l i / Λ * (1 - z))⁻¹) := by
  have hΛ0 : 0 < Λ := by linarith
  have h0 : (0 : ℝ) ≤ Λ⁻¹ := inv_nonneg.mpr hΛ0.le
  have h1 : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
  have hw0 : 0 ≤ 1 - Λ⁻¹ + Λ⁻¹ * z := by nlinarith [mul_nonneg h0 hz0]
  have hw1 : 1 - Λ⁻¹ + Λ⁻¹ * z ≤ 1 := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr hz1)]
  have hS := hG _ hw0 hw1
  have e1 : (fun k => p k * (1 - Λ⁻¹ + Λ⁻¹ * z) ^ k)
      = fun k => p k * binE Λ⁻¹ k (fun j => z ^ j) := by
    funext k
    rw [binE_pow]
  have e2 : ∏ i, (1 + l i * (1 - (1 - Λ⁻¹ + Λ⁻¹ * z)))⁻¹ = ∏ i, (1 + l i / Λ * (1 - z))⁻¹ := by
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 2
    field_simp
    ring
  rw [e1, e2] at hS
  exact thin_hasSum h0 h1 hp (fun j => pow_nonneg hz0 j) hS

/-- The tail of a thinned law is a sub-probability mixture (with weights independent of the law) of the
tails of the original law. -/
private lemma thin_tail {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (τ : ℕ) :
    ∃ w : ℕ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ n, ∑ t ∈ Finset.range n, w t ≤ 1) ∧
      ∀ p : ℕ → ℝ, (∀ k, 0 ≤ p k) → Summable p →
        HasSum (fun t => w t * ∑' k, if t < k then p k else 0)
          (∑' j, if τ < j then thin η p j else 0) := by
  set a : ℕ → ℝ := fun j => if τ < j then 1 else 0 with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => by
    simp only [ha]
    split_ifs <;> norm_num
  have ha1 : ∀ j, a j ≤ 1 := fun j => by
    simp only [ha]
    split_ifs <;> norm_num
  have hamono : ∀ j, a j ≤ a (j + 1) := fun j => by
    simp only [ha]
    split_ifs with h h'
    · exact le_rfl
    · exact absurd (Nat.lt_succ_of_lt h) h'
    · exact zero_le_one
    · exact le_rfl
  have hf0 : binE η 0 a = 0 := by
    rw [binE_zero]
    simp [ha]
  refine ⟨fun t => binE η (t + 1) a - binE η t a, fun t => ?_, fun n => ?_, fun p hp hps => ?_⟩
  · exact sub_nonneg.mpr (binE_le_succ h0 h1 t hamono)
  · have := Finset.sum_range_sub (fun t => binE η t a) n
    simp only at this ⊢
    rw [this, hf0, sub_zero]
    exact binE_le_one h0 h1 n ha1
  · have hsum : Summable (fun k => p k * binE η k a) :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (hp k) (binE_nonneg h0 h1 k ha0))
        (fun k => mul_le_of_le_one_right (hp k) (binE_le_one h0 h1 k ha1)) hps
    have hT := thin_hasSum h0 h1 hp ha0 hsum.hasSum
    have e : (fun j => thin η p j * a j) = fun j => if τ < j then thin η p j else 0 := by
      funext j
      simp only [ha]
      split_ifs <;> simp
    rw [e] at hT
    rw [hT.tsum_eq]
    exact abel_hasSum hp hf0 (fun k => binE_le_succ h0 h1 k hamono) hsum.hasSum

/-! ### Main statement -/

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ Λ : ℝ, 1 ≤ Λ →
      ∀ (m : ℕ) (lp lm : Fin m → ℝ), (∀ i, 0 ≤ lm i) → (∀ i, lm i ≤ lp i) → (∀ i, lp i ≤ Λ) →
      ∀ (pp pm : ℕ → ℝ), (∀ k, 0 ≤ pp k) → (∀ k, 0 ≤ pm k) →
        (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          HasSum (fun k => pp k * z ^ k) (∏ i, (1 + lp i * (1 - z))⁻¹)) →
        (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          HasSum (fun k => pm k * z ^ k) (∏ i, (1 + lm i * (1 - z))⁻¹)) →
        0 < ∑ i, (lp i - lm i) →
        (∑ i, (lp i - lm i)) ^ 2 ≤ 1 + ∑ i, lm i * (1 + lm i) →
        ∃ τ : ℕ, c * ((∑ i, (lp i - lm i)) / Λ) /
            Real.sqrt (1 + ∑ i, lm i / Λ * (1 + lm i / Λ)) ≤
          (∑' k, if τ < k then pp k else 0) - ∑' k, if τ < k then pm k else 0 := by
  obtain ⟨c, hc, H⟩ := geometric_pgf_threshold 1 one_pos
  refine ⟨c, hc, ?_⟩
  intro Λ hΛ m lp lm hlm0 hlmp hlpΛ pp pm hpp hpm hGp hGm hδ hδ2
  have hΛ0 : 0 < Λ := by linarith
  have h0 : (0 : ℝ) ≤ Λ⁻¹ := inv_nonneg.mpr hΛ0.le
  have h1 : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
  have hsumdiv : ∑ i, (lp i / Λ - lm i / Λ) = (∑ i, (lp i - lm i)) / Λ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨τ, hτ⟩ := H m (fun i => lp i / Λ) (fun i => lm i / Λ)
    (fun i => div_nonneg (hlm0 i) hΛ0.le)
    (fun i => div_le_div_of_nonneg_right (hlmp i) hΛ0.le)
    (fun i => (div_le_one hΛ0).mpr (hlpΛ i))
    (thin Λ⁻¹ pp) (thin Λ⁻¹ pm) (thin_nonneg h0 h1 hpp) (thin_nonneg h0 h1 hpm)
    (thin_gf hΛ hpp hGp) (thin_gf hΛ hpm hGm)
    (by rw [hsumdiv]; exact div_pos hδ hΛ0)
    (by rw [hsumdiv]; exact scaled_sq hΛ hlm0 hδ2)
  rw [hsumdiv] at hτ
  have hpps : Summable pp := by simpa using (hGp 1 zero_le_one le_rfl).summable
  have hpms : Summable pm := by simpa using (hGm 1 zero_le_one le_rfl).summable
  obtain ⟨w, hw0, hw1, hw⟩ := thin_tail h0 h1 τ
  have hD := (hw pp hpp hpps).sub (hw pm hpm hpms)
  have hL : 0 < c * ((∑ i, (lp i - lm i)) / Λ) /
      Real.sqrt (1 + ∑ i, lm i / Λ * (1 + lm i / Λ)) := by
    have hs : 0 ≤ ∑ i, lm i / Λ * (1 + lm i / Λ) :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (div_nonneg (hlm0 i) hΛ0.le) (add_nonneg zero_le_one (div_nonneg (hlm0 i) hΛ0.le))
    exact div_pos (mul_pos hc (div_pos hδ hΛ0)) (Real.sqrt_pos.mpr (by linarith))
  exact exists_of_mixture (D := fun t => (∑' k, if t < k then pp k else 0) - ∑' k, if t < k then pm k else 0)
    hw0 hw1 (by simpa only [mul_sub] using hD) hL hτ
