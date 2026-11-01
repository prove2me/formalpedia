-- Prove2me | solution 1 for DeFinetti.exchangeable_zero_one_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T19:52:19.577976+00:00
-- url     : https://prove2.me/submissions/c4b33080-fbfa-4f4a-9787-2681b02ae1c8

import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace DeFinettiAux

/-- Moments of the exchangeable 0-1 sequence: `c m = E[X 0 ⋯ X (m-1)]`. -/
noncomputable def cm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (m : ℕ) : ℝ :=
  ∫ ω, ∏ i ∈ Finset.range m, X i ω ∂P

lemma exists_perm (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, ((σ i : ℕ) ∈ S ↔ (i : ℕ) < S.card) := by
  classical
  have hm : S.card ≤ n := by simpa using Finset.card_le_card hS
  let e1 : {i : Fin n // (i : ℕ) < S.card} ≃ Fin S.card :=
    { toFun := fun i => ⟨i.1.1, i.2⟩
      invFun := fun j => ⟨⟨j.1, lt_of_lt_of_le j.2 hm⟩, j.2⟩
      left_inv := fun i => rfl
      right_inv := fun j => rfl }
  let e2 : {j : Fin n // (j : ℕ) ∈ S} ≃ {x : ℕ // x ∈ S} :=
    { toFun := fun j => ⟨j.1.1, j.2⟩
      invFun := fun x => ⟨⟨x.1, Finset.mem_range.1 (hS x.2)⟩, x.2⟩
      left_inv := fun j => rfl
      right_inv := fun x => rfl }
  let e : {i : Fin n // (i : ℕ) < S.card} ≃ {j : Fin n // (j : ℕ) ∈ S} :=
    e1.trans (S.equivFin.symm.trans e2.symm)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  by_cases hi : (i : ℕ) < S.card
  · exact ⟨fun _ => hi, fun _ => e.extendSubtype_mem i hi⟩
  · exact ⟨fun h => absurd h (e.extendSubtype_not_mem i hi), fun h => absurd h hi⟩

lemma prod_fin (n : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range n) (x : ℕ → ℝ) :
    ∏ j : Fin n, (if (j : ℕ) ∈ T then x j else 1) = ∏ i ∈ T, x i := by
  classical
  rw [Fin.prod_univ_eq_prod_range (fun i => if i ∈ T then x i else 1) n, Finset.prod_ite_mem,
    Finset.inter_eq_right.2 hT]

section main

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X : ℕ → Ω → ℝ)

lemma int_of_bdd {g : Ω → ℝ} (hg : Measurable g) (hb : ∀ ω, |g ω| ≤ 1) : Integrable g P :=
  Integrable.of_bound hg.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hb ω))

lemma abs_le_one_of {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : |x| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith

variable {X}

lemma X_bounds (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (i : ℕ) (ω : Ω) :
    0 ≤ X i ω ∧ X i ω ≤ 1 := by
  rcases hX01 i ω with h | h <;> rw [h] <;> norm_num

lemma prod_bounds (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (S : Finset ℕ) (ω : Ω) :
    0 ≤ ∏ i ∈ S, X i ω ∧ ∏ i ∈ S, X i ω ≤ 1 :=
  ⟨Finset.prod_nonneg (fun i _ => (X_bounds hX01 i ω).1),
    Finset.prod_le_one (fun i _ => (X_bounds hX01 i ω).1) (fun i _ => (X_bounds hX01 i ω).2)⟩

lemma prod_one_sub_bounds (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (S : Finset ℕ) (ω : Ω) :
    0 ≤ ∏ i ∈ S, (1 - X i ω) ∧ ∏ i ∈ S, (1 - X i ω) ≤ 1 :=
  ⟨Finset.prod_nonneg (fun i _ => by linarith [(X_bounds hX01 i ω).2]),
    Finset.prod_le_one (fun i _ => by linarith [(X_bounds hX01 i ω).2])
      (fun i _ => by linarith [(X_bounds hX01 i ω).1])⟩

lemma meas_prod (hXmeas : ∀ i, Measurable (X i)) (S : Finset ℕ) :
    Measurable (fun ω => ∏ i ∈ S, X i ω) :=
  Finset.measurable_prod _ (fun i _ => hXmeas i)

lemma meas_prod_one_sub (hXmeas : ∀ i, Measurable (X i)) (S : Finset ℕ) :
    Measurable (fun ω => ∏ i ∈ S, (1 - X i ω)) :=
  Finset.measurable_prod _ (fun i _ => measurable_const.sub (hXmeas i))

/-- Exchangeability: the expectation of a product over any finite index set depends only on
its cardinality. -/
lemma prod_integral (hXmeas : ∀ i, Measurable (X i))
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω))
    (S : Finset ℕ) : ∫ ω, ∏ i ∈ S, X i ω ∂P = cm P X S.card := by
  classical
  set n := S.sup id + 1 with hn
  have hS : S ⊆ Finset.range n := fun i hi =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hm : Finset.range S.card ⊆ Finset.range n :=
    fun i hi => Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hi) (by simpa using Finset.card_le_card hS))
  obtain ⟨σ, hσ⟩ := exists_perm n S hS
  let g : (Fin n → ℝ) → ℝ := fun x => ∏ i : Fin n, (if (i : ℕ) < S.card then x i else 1)
  have hg : Continuous g := by
    refine continuous_finsetProd _ (fun i _ => ?_)
    by_cases h : (i : ℕ) < S.card
    · simp only [h, if_true]; exact continuous_apply i
    · simp only [h, if_false]; exact continuous_const
  have hmeasσ : Measurable (fun ω (i : Fin n) => X (σ i) ω) :=
    measurable_pi_lambda _ (fun i => hXmeas _)
  have hmeas1 : Measurable (fun ω (i : Fin n) => X i ω) :=
    measurable_pi_lambda _ (fun i => hXmeas _)
  have h1 := congrArg (fun μ => ∫ x, g x ∂μ) (hexch n σ)
  try simp only at h1
  rw [integral_map hmeasσ.aemeasurable hg.aestronglyMeasurable,
    integral_map hmeas1.aemeasurable hg.aestronglyMeasurable] at h1
  have e1 : ∀ ω, g (fun i => X (σ i) ω) = ∏ i ∈ S, X i ω := by
    intro ω
    calc g (fun i => X (σ i) ω)
        = ∏ i : Fin n, (fun j : Fin n => if (j : ℕ) ∈ S then X j ω else 1) (σ i) :=
          Finset.prod_congr rfl (fun i _ => by simp only [hσ i])
      _ = ∏ j : Fin n, (if (j : ℕ) ∈ S then X j ω else 1) :=
          Equiv.prod_comp σ (fun j : Fin n => if (j : ℕ) ∈ S then X j ω else 1)
      _ = ∏ i ∈ S, X i ω := prod_fin n S hS (fun i => X i ω)
  have e2 : ∀ ω, g (fun i => X i ω) = ∏ i ∈ Finset.range S.card, X i ω := by
    intro ω
    calc g (fun i => X i ω)
        = ∏ j : Fin n, (if (j : ℕ) ∈ Finset.range S.card then X j ω else 1) :=
          Finset.prod_congr rfl (fun i _ => by simp only [Finset.mem_range])
      _ = ∏ i ∈ Finset.range S.card, X i ω := prod_fin n _ hm (fun i => X i ω)
  simp only [e1, e2] at h1
  exact h1

lemma XX_integral (hXmeas : ∀ i, Measurable (X i)) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω))
    (i j : ℕ) : ∫ ω, X i ω * X j ω ∂P = if i = j then cm P X 1 else cm P X 2 := by
  classical
  split_ifs with h
  · subst h
    have : ∀ ω, X i ω * X i ω = ∏ k ∈ ({i} : Finset ℕ), X k ω := by
      intro ω; rw [Finset.prod_singleton]; rcases hX01 i ω with h0 | h0 <;> rw [h0] <;> norm_num
    simp_rw [this]
    rw [prod_integral P hXmeas hexch]; rfl
  · have : ∀ ω, X i ω * X j ω = ∏ k ∈ ({i, j} : Finset ℕ), X k ω := by
      intro ω; rw [Finset.prod_pair h]
    simp_rw [this]
    rw [prod_integral P hXmeas hexch, Finset.card_pair h]

lemma quad_alg (s : Finset ℕ) (a : ℕ → ℝ) (c1 c2 : ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, a i * a j * (if i = j then c1 else c2)
      = c2 * (∑ i ∈ s, a i) ^ 2 + (c1 - c2) * ∑ i ∈ s, a i ^ 2 := by
  classical
  have h : ∀ i j, a i * a j * (if i = j then c1 else c2)
      = c2 * (a i * a j) + (if i = j then (c1 - c2) * a i ^ 2 else 0) := by
    intro i j
    split_ifs with h
    · subst h; ring
    · ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.mul_sum]
  rw [Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum]
  rw [sq, Finset.sum_mul]

lemma quad (hXmeas : ∀ i, Measurable (X i)) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω))
    (n : ℕ) (a : ℕ → ℝ) :
    ∫ ω, (∑ i ∈ Finset.range n, a i * X i ω) ^ 2 ∂P
      = cm P X 2 * (∑ i ∈ Finset.range n, a i) ^ 2
        + (cm P X 1 - cm P X 2) * ∑ i ∈ Finset.range n, a i ^ 2 := by
  have e : ∀ ω, (∑ i ∈ Finset.range n, a i * X i ω) ^ 2
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, a i * a j * (X i ω * X j ω) := by
    intro ω; rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)); ring
  have hint : ∀ i j, Integrable (fun ω => a i * a j * (X i ω * X j ω)) P := by
    intro i j
    refine Integrable.const_mul (int_of_bdd P ((hXmeas i).mul (hXmeas j)) (fun ω => ?_)) _
    exact abs_le_one_of (mul_nonneg (X_bounds hX01 i ω).1 (X_bounds hX01 j ω).1)
      (mul_le_one₀ (X_bounds hX01 i ω).2 (X_bounds hX01 j ω).1 (X_bounds hX01 j ω).2)
  simp_rw [e]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  rw [Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_const_mul, XX_integral P hXmeas hX01 hexch]
  exact quad_alg _ a _ _

lemma filter_lt_range (A B : ℕ) (h : A ≤ B) :
    (Finset.range B).filter (· < A) = Finset.range A := by
  ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma card_filter_not_lt (A B : ℕ) (h : A ≤ B) :
    ((Finset.range B).filter (fun i => ¬ i < A)).card = B - A := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.range B) (fun i => i < A)
  rw [filter_lt_range A B h, Finset.card_range, Finset.card_range] at this
  omega

/-- the running average `Y N = (X 0 + ⋯ + X (N-1)) / N`. -/
noncomputable def Yav (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range N, X i ω) / (N : ℝ)

lemma Yav_bounds (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (N : ℕ) (hN : 1 ≤ N) (ω : Ω) :
    0 ≤ Yav X N ω ∧ Yav X N ω ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 ≤ ∑ i ∈ Finset.range N, X i ω :=
    Finset.sum_nonneg (fun i _ => (X_bounds hX01 i ω).1)
  have h1 : ∑ i ∈ Finset.range N, X i ω ≤ N := by
    calc ∑ i ∈ Finset.range N, X i ω ≤ ∑ i ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => (X_bounds hX01 i ω).2)
      _ = N := by simp
  exact ⟨div_nonneg h0 hNpos.le, (div_le_one hNpos).2 h1⟩

lemma Yav_meas (hXmeas : ∀ i, Measurable (X i)) (N : ℕ) : Measurable (Yav X N) :=
  (Finset.measurable_sum _ (fun i _ => hXmeas i)).div_const _

lemma sq_diff_le (hXmeas : ∀ i, Measurable (X i)) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω))
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∫ ω, (Yav X A ω - Yav X B ω) ^ 2 ∂P ≤ 1 / (A : ℝ) := by
  classical
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (le_trans hA hAB)
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  set u : ℝ := 1 / A - 1 / B with hu
  set v : ℝ := -(1 / B) with hv
  let a : ℕ → ℝ := fun i => if i < A then u else v
  have hcard1 : ((Finset.range B).filter (· < A)).card = A := by
    rw [filter_lt_range A B hAB, Finset.card_range]
  have hcard2 := card_filter_not_lt A B hAB
  have hY : ∀ ω, Yav X A ω - Yav X B ω = ∑ i ∈ Finset.range B, a i * X i ω := by
    intro ω
    have e1 : ∑ i ∈ Finset.range B, a i * X i ω
        = ∑ i ∈ Finset.range B, (if i < A then u * X i ω else v * X i ω) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [a]; split_ifs <;> rfl
    rw [e1, Finset.sum_ite, filter_lt_range A B hAB, ← Finset.mul_sum, ← Finset.mul_sum]
    have e2 := Finset.sum_filter_add_sum_filter_not (Finset.range B) (fun i => i < A) (fun i => X i ω)
    rw [filter_lt_range A B hAB] at e2
    simp only [Yav]
    rw [← e2, hu, hv]
    field_simp
    ring
  have hsa : ∑ i ∈ Finset.range B, a i = 0 := by
    simp only [a]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard1, hcard2, nsmul_eq_mul,
      nsmul_eq_mul, Nat.cast_sub hAB, hu, hv]
    field_simp
    ring
  have hsa2 : ∑ i ∈ Finset.range B, a i ^ 2 = 1 / A - 1 / B := by
    simp only [a, ite_pow]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard1, hcard2, nsmul_eq_mul,
      nsmul_eq_mul, Nat.cast_sub hAB, hu, hv]
    field_simp
    ring
  have hc1 : cm P X 1 ≤ 1 := by
    have : cm P X 1 = ∫ ω, X 0 ω ∂P := by simp [cm]
    rw [this]
    calc ∫ ω, X 0 ω ∂P ≤ ∫ _ω, (1 : ℝ) ∂P :=
          integral_mono (int_of_bdd P (hXmeas 0) (fun ω => abs_le_one_of (X_bounds hX01 0 ω).1
            (X_bounds hX01 0 ω).2)) (integrable_const _) (fun ω => (X_bounds hX01 0 ω).2)
      _ = 1 := by simp
  have hc2 : 0 ≤ cm P X 2 :=
    integral_nonneg (fun ω => (prod_bounds hX01 (Finset.range 2) ω).1)
  have ht : 0 ≤ 1 / (A : ℝ) - 1 / B := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hApos hABr
  calc ∫ ω, (Yav X A ω - Yav X B ω) ^ 2 ∂P
      = ∫ ω, (∑ i ∈ Finset.range B, a i * X i ω) ^ 2 ∂P := by simp_rw [hY]
    _ = (cm P X 1 - cm P X 2) * (1 / A - 1 / B) := by
        rw [quad P hXmeas hX01 hexch, hsa, hsa2]; ring
    _ ≤ 1 * (1 / A - 1 / B) := mul_le_mul_of_nonneg_right (by linarith) ht
    _ ≤ 1 / A := by have : 0 ≤ 1 / (B : ℝ) := by positivity
                    linarith

lemma exists_limit (hXmeas : ∀ i, Measurable (X i)) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω)) :
    ∃ T : Ω → ℝ, Measurable T ∧ (∀ ω, 0 ≤ T ω ∧ T ω ≤ 1) ∧
      ∀ᵐ ω ∂P, Tendsto (fun l : ℕ => Yav X (4 ^ l) ω) atTop (𝓝 (T ω)) := by
  set f : ℕ → Ω → ℝ := fun l => Yav X (4 ^ l) with hfdef
  have hpos : ∀ l : ℕ, 1 ≤ 4 ^ l := fun l => Nat.one_le_pow _ _ (by norm_num)
  have hfm : ∀ l, Measurable (f l) := fun l => Yav_meas hXmeas _
  have hf01 : ∀ l ω, 0 ≤ f l ω ∧ f l ω ≤ 1 := fun l ω => Yav_bounds hX01 _ (hpos l) ω
  have hsq : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      ∫ ω, (f n ω - f m ω) ^ 2 ∂P ≤ ((1 / 2 : ℝ) ^ N) ^ 2 := by
    intro N n m hn hm
    have key : ∀ a b : ℕ, a ≤ b → N ≤ a →
        ∫ ω, (f a ω - f b ω) ^ 2 ∂P ≤ ((1 / 2 : ℝ) ^ N) ^ 2 := by
      intro a b hab ha
      have h1 := sq_diff_le P hXmeas hX01 hexch (4 ^ a) (4 ^ b) (hpos a)
        (Nat.pow_le_pow_right (by norm_num) hab)
      refine h1.trans ?_
      calc 1 / ((4 ^ a : ℕ) : ℝ) = 1 / (4 : ℝ) ^ a := by push_cast; ring
        _ ≤ 1 / (4 : ℝ) ^ N :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) ha)
        _ = ((1 / 2 : ℝ) ^ N) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul, one_div_pow, one_div_pow]; norm_num
    rcases le_total n m with h | h
    · exact key n m h hn
    · calc ∫ ω, (f n ω - f m ω) ^ 2 ∂P = ∫ ω, (f m ω - f n ω) ^ 2 ∂P := by
            congr 1; ext ω; ring
        _ ≤ _ := key m n h hm
  have hdb : ∀ n m ω, |(f n - f m) ω| ≤ 1 := by
    intro n m ω
    simp only [Pi.sub_apply]
    rw [abs_le]; constructor <;> linarith [hf01 n ω, hf01 m ω]
  have hint : ∀ n m, Integrable (f n - f m) P := fun n m =>
    int_of_bdd P ((hfm n).sub (hfm m)) (hdb n m)
  have hcau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (f n - f m) 1 P < ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N) := by
    intro N n m hn hm
    set ε : ℝ := (1 / 2 : ℝ) ^ N with hεdef
    have hε : 0 < ε := by positivity
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hint n m),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hpt : ∀ ω, ‖(f n - f m) ω‖ ≤ (ε + (f n ω - f m ω) ^ 2 / ε) / 2 := by
      intro ω
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      set x := f n ω - f m ω
      have key : (ε + x ^ 2 / ε) / 2 - |x| = (|x| - ε) ^ 2 / (2 * ε) := by
        rw [← sq_abs x]; field_simp; ring
      have : 0 ≤ (|x| - ε) ^ 2 / (2 * ε) := by positivity
      linarith
    have hsqint : Integrable (fun ω => (f n ω - f m ω) ^ 2) P := by
      refine int_of_bdd P (((hfm n).sub (hfm m)).pow_const 2) (fun ω => ?_)
      have h1 := hdb n m ω
      simp only [Pi.sub_apply] at h1
      rw [abs_le] at h1 ⊢
      constructor <;> nlinarith [sq_nonneg (f n ω - f m ω)]
    calc ∫ x, ‖(f n - f m) x‖ ∂P ≤ ∫ ω, (ε + (f n ω - f m ω) ^ 2 / ε) / 2 ∂P :=
          integral_mono (hint n m).norm
            (((integrable_const ε).add (hsqint.div_const ε)).div_const 2) hpt
      _ = (ε + (∫ ω, (f n ω - f m ω) ^ 2 ∂P) / ε) / 2 := by
          rw [integral_div, integral_add (integrable_const ε) (hsqint.div_const ε), integral_div]
          simp
      _ ≤ (ε + ε ^ 2 / ε) / 2 := by
          gcongr
          exact hsq N n m hn hm
      _ = ε := by field_simp; ring
      _ < 2 * ε := by linarith
  have hB : ∑' i : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ i) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_geometric_two.mul_left 2)]
    exact ENNReal.ofReal_ne_top
  have hae := MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm (fun n => (hfm n).aestronglyMeasurable) le_rfl hB hcau
  obtain ⟨T0, hT0m, hT0⟩ :=
    measurable_limit_of_tendsto_metrizable_ae (fun n => (hfm n).aemeasurable) hae
  refine ⟨fun ω => max 0 (min 1 (T0 ω)), measurable_const.max (measurable_const.min hT0m),
    fun ω => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, hT0.mono fun ω hω => ?_⟩
  have hc : Continuous (fun x : ℝ => max 0 (min 1 x)) :=
    continuous_const.max (continuous_const.min continuous_id)
  refine ((hc.tendsto _).comp hω).congr (fun l => ?_)
  simp only [Function.comp]
  rw [min_eq_right (hf01 l ω).2, max_eq_right (hf01 l ω).1]

lemma moment (hXmeas : ∀ i, Measurable (X i)) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω))
    (T : Ω → ℝ) (hTm : Measurable T) (hT01 : ∀ ω, 0 ≤ T ω ∧ T ω ≤ 1)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun l : ℕ => Yav X (4 ^ l) ω) atTop (𝓝 (T ω))) :
    ∀ (j : ℕ) (S : Finset ℕ), ∫ ω, T ω ^ j * ∏ i ∈ S, X i ω ∂P = cm P X (j + S.card) := by
  classical
  have hpos : ∀ l : ℕ, 1 ≤ 4 ^ l := fun l => Nat.one_le_pow _ _ (by norm_num)
  intro j
  induction j with
  | zero =>
    intro S
    simp only [pow_zero, one_mul, zero_add]
    exact prod_integral P hXmeas hexch S
  | succ j ih =>
    intro S
    set s := S.card with hs
    set W : Ω → ℝ := fun ω => T ω ^ j * ∏ i ∈ S, X i ω with hW
    have hWm : Measurable W := (hTm.pow_const j).mul (meas_prod hXmeas S)
    have hWb : ∀ ω, 0 ≤ W ω ∧ W ω ≤ 1 := fun ω =>
      ⟨mul_nonneg (pow_nonneg (hT01 ω).1 j) (prod_bounds hX01 S ω).1,
        mul_le_one₀ (pow_le_one₀ (hT01 ω).1 (hT01 ω).2) (prod_bounds hX01 S ω).1
          (prod_bounds hX01 S ω).2⟩
    have ha : Tendsto (fun l : ℕ => ∫ ω, Yav X (4 ^ l) ω * W ω ∂P) atTop
        (𝓝 (∫ ω, T ω * W ω ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun l => ((Yav_meas hXmeas _).mul hWm).aestronglyMeasurable) (integrable_const 1)
        (fun l => Eventually.of_forall (fun ω => ?_)) (hlim.mono fun ω h => h.mul_const (W ω))
      rw [Real.norm_eq_abs]
      exact abs_le_one_of (mul_nonneg (Yav_bounds hX01 _ (hpos l) ω).1 (hWb ω).1)
        (mul_le_one₀ (Yav_bounds hX01 _ (hpos l) ω).2 (hWb ω).1 (hWb ω).2)
    have hXW : ∀ i, ∫ ω, X i ω * W ω ∂P
        = if i ∈ S then cm P X (j + s) else cm P X (j + s + 1) := by
      intro i
      split_ifs with hi
      · have : ∀ ω, X i ω * W ω = T ω ^ j * ∏ k ∈ S, X k ω := by
          intro ω
          simp only [hW]
          rcases hX01 i ω with h0 | h0
          · rw [h0, Finset.prod_eq_zero hi h0]; ring
          · rw [h0]; ring
        simp_rw [this]; exact ih S
      · have : ∀ ω, X i ω * W ω = T ω ^ j * ∏ k ∈ insert i S, X k ω := by
          intro ω; simp only [hW]; rw [Finset.prod_insert hi]; ring
        simp_rw [this]
        rw [ih (insert i S), Finset.card_insert_of_notMem hi]
        rfl
    have hb : ∀ l : ℕ, S ⊆ Finset.range (4 ^ l) → ∫ ω, Yav X (4 ^ l) ω * W ω ∂P
        = cm P X (j + s + 1) + s * (cm P X (j + s) - cm P X (j + s + 1)) / (4 : ℝ) ^ l := by
      intro l hl
      have e : ∀ ω, Yav X (4 ^ l) ω * W ω
          = (∑ i ∈ Finset.range (4 ^ l), X i ω * W ω) / ((4 ^ l : ℕ) : ℝ) := by
        intro ω; simp only [Yav]; rw [div_mul_eq_mul_div, Finset.sum_mul]
      simp_rw [e]
      rw [integral_div, integral_finsetSum (f := fun i ω => X i ω * W ω) _ (fun i _ => int_of_bdd P ((hXmeas i).mul hWm)
        (fun ω => abs_le_one_of (mul_nonneg (X_bounds hX01 i ω).1 (hWb ω).1)
          (mul_le_one₀ (X_bounds hX01 i ω).2 (hWb ω).1 (hWb ω).2)))]
      simp_rw [hXW]
      have hcard := Finset.card_filter_add_card_filter_not (s := Finset.range (4 ^ l))
        (fun i => i ∈ S)
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hl, Finset.card_range] at hcard
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
        Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hl]
      have hsl : s ≤ 4 ^ l := by omega
      rw [show ((Finset.range (4 ^ l)).filter (fun i => i ∉ S)).card = 4 ^ l - s by omega,
        Nat.cast_sub hsl]
      push_cast
      field_simp
      ring
    have hc : Tendsto (fun l : ℕ => ∫ ω, Yav X (4 ^ l) ω * W ω ∂P) atTop
        (𝓝 (cm P X (j + s + 1))) := by
      have h4 : Tendsto (fun l : ℕ => (4 : ℝ) ^ l) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      have h0 : Tendsto (fun l : ℕ => cm P X (j + s + 1)
          + s * (cm P X (j + s) - cm P X (j + s + 1)) / (4 : ℝ) ^ l) atTop
          (𝓝 (cm P X (j + s + 1) + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop h4)
      rw [add_zero] at h0
      refine h0.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      refine ⟨S.sup id + 1, fun l hl => (hb l ?_).symm⟩
      intro i hi
      have h1 : i ≤ S.sup id := Finset.le_sup (f := id) hi
      have h2 : l < 4 ^ l := Nat.lt_pow_self (by norm_num)
      exact Finset.mem_range.2 (by omega)
    have hlim' := tendsto_nhds_unique ha hc
    calc ∫ ω, T ω ^ (j + 1) * ∏ i ∈ S, X i ω ∂P = ∫ ω, T ω * W ω ∂P := by
          congr 1; ext ω; simp only [hW]; ring
      _ = cm P X (j + s + 1) := hlim'
      _ = cm P X (j + 1 + s) := by congr 1; omega

lemma pattern (hXmeas : ∀ i, Measurable (X i)) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω))
    (T : Ω → ℝ) (hTm : Measurable T) (hT01 : ∀ ω, 0 ≤ T ω ∧ T ω ≤ 1)
    (hmom0 : ∀ m, ∫ ω, T ω ^ m ∂P = cm P X m) :
    ∀ (B A : Finset ℕ), Disjoint A B →
      ∫ ω, (∏ i ∈ A, X i ω) * ∏ i ∈ B, (1 - X i ω) ∂P
        = ∫ ω, T ω ^ A.card * (1 - T ω) ^ B.card ∂P := by
  classical
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro A _
    simp only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero]
    rw [prod_integral P hXmeas hexch A, hmom0]
  | insert b B hb ih =>
    intro A hAB
    have hbA : b ∉ A := fun h => Finset.disjoint_left.1 hAB h (Finset.mem_insert_self b B)
    have hAB0 : Disjoint A B := hAB.mono_right (Finset.subset_insert b B)
    have hAB1 : Disjoint (insert b A) B := Finset.disjoint_insert_left.2 ⟨hb, hAB0⟩
    have e : ∀ ω, (∏ i ∈ A, X i ω) * ∏ i ∈ insert b B, (1 - X i ω)
        = (∏ i ∈ A, X i ω) * ∏ i ∈ B, (1 - X i ω)
          - (∏ i ∈ insert b A, X i ω) * ∏ i ∈ B, (1 - X i ω) := by
      intro ω; rw [Finset.prod_insert hb, Finset.prod_insert hbA]; ring
    have hi : ∀ A' : Finset ℕ,
        Integrable (fun ω => (∏ i ∈ A', X i ω) * ∏ i ∈ B, (1 - X i ω)) P := fun A' =>
      int_of_bdd P ((meas_prod hXmeas A').mul (meas_prod_one_sub hXmeas B)) (fun ω =>
        abs_le_one_of (mul_nonneg (prod_bounds hX01 A' ω).1 (prod_one_sub_bounds hX01 B ω).1)
          (mul_le_one₀ (prod_bounds hX01 A' ω).2 (prod_one_sub_bounds hX01 B ω).1
            (prod_one_sub_bounds hX01 B ω).2))
    have hTi : ∀ a c : ℕ, Integrable (fun ω => T ω ^ a * (1 - T ω) ^ c) P := fun a c =>
      int_of_bdd P ((hTm.pow_const a).mul ((measurable_const.sub hTm).pow_const c)) (fun ω =>
        abs_le_one_of (mul_nonneg (pow_nonneg (hT01 ω).1 a)
          (pow_nonneg (by linarith [(hT01 ω).2]) c))
          (mul_le_one₀ (pow_le_one₀ (hT01 ω).1 (hT01 ω).2)
            (pow_nonneg (by linarith [(hT01 ω).2]) c)
            (pow_le_one₀ (by linarith [(hT01 ω).2]) (by linarith [(hT01 ω).1]))))
    simp_rw [e]
    rw [integral_sub (hi A) (hi (insert b A)), ih A hAB0, ih (insert b A) hAB1,
      ← integral_sub (hTi _ _) (hTi _ _), Finset.card_insert_of_notMem hb,
      Finset.card_insert_of_notMem hbA]
    congr 1; ext ω; ring

lemma prod_pattern (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (n : ℕ) (p : ℕ → Prop)
    [DecidablePred p] (ω : Ω) :
    ∏ i ∈ Finset.range n, (if p i then X i ω else 1 - X i ω)
      = if (∀ i < n, X i ω = if p i then 1 else 0) then 1 else 0 := by
  split_ifs with h
  · apply Finset.prod_eq_one
    intro i hi
    have := h i (Finset.mem_range.1 hi)
    split_ifs at this ⊢ <;> rw [this] <;> norm_num
  · push_neg at h
    obtain ⟨i, hi, hne⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_range.2 hi)
    split_ifs at hne ⊢ with hp
    · rcases hX01 i ω with h0 | h0
      · exact h0
      · exact absurd h0 hne
    · rcases hX01 i ω with h0 | h0
      · exact absurd h0 hne
      · rw [h0]; norm_num

lemma meas_pat (hXmeas : ∀ i, Measurable (X i)) (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    MeasurableSet {ω | ∀ i < n, X i ω = if p i then (1 : ℝ) else 0} := by
  have : {ω | ∀ i < n, X i ω = if p i then (1 : ℝ) else 0}
      = ⋂ i ∈ Finset.range n, {ω | X i ω = if p i then (1 : ℝ) else 0} := by
    ext ω; simp
  rw [this]
  exact Finset.measurableSet_biInter _ (fun i _ => measurableSet_eq_fun (hXmeas i) measurable_const)

lemma pat_prob (hXmeas : ∀ i, Measurable (X i)) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (P {ω | ∀ i < n, X i ω = if p i then (1 : ℝ) else 0}).toReal
      = ∫ ω, ∏ i ∈ Finset.range n, (if p i then X i ω else 1 - X i ω) ∂P := by
  rw [← measureReal_def, ← integral_indicator_one (meas_pat hXmeas n p)]
  congr 1; ext ω
  rw [prod_pattern hX01 n p ω]
  by_cases h : ∀ i < n, X i ω = if p i then (1 : ℝ) else 0
  · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω | ∀ i < n, X i ω = if p i then (1 : ℝ) else 0}
      from h)]; rfl
  · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | ∀ i < n, X i ω = if p i then (1 : ℝ) else 0}
      from h)]

lemma pat_integral (hXmeas : ∀ i, Measurable (X i)) (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω))
    (T : Ω → ℝ) (hTm : Measurable T) (hT01 : ∀ ω, 0 ≤ T ω ∧ T ω ≤ 1)
    (hmom0 : ∀ m, ∫ ω, T ω ^ m ∂P = cm P X m) (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ∫ ω, ∏ i ∈ Finset.range n, (if p i then X i ω else 1 - X i ω) ∂P
      = ∫ ω, T ω ^ ((Finset.range n).filter p).card
          * (1 - T ω) ^ (n - ((Finset.range n).filter p).card) ∂P := by
  simp_rw [Finset.prod_ite]
  rw [pattern P hXmeas hX01 hexch T hTm hT01 hmom0 ((Finset.range n).filter (fun i => ¬ p i))
    ((Finset.range n).filter p) (Finset.disjoint_filter_filter_not _ _ _)]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.range n) p
  rw [Finset.card_range] at hc
  rw [show ((Finset.range n).filter (fun i => ¬ p i)).card
      = n - ((Finset.range n).filter p).card by omega]

end main

lemma moments_ext (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0) (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (h : ∀ m : ℕ, ∫ x, x ^ m ∂μ = ∫ x, x ^ m ∂ν) : μ = ν := by
  have aeμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1 := mem_ae_iff.2 hμ
  have aeν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1 := mem_ae_iff.2 hν
  have hmono : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (i : ℕ) (a : ℝ), Integrable (fun x : ℝ => a * x ^ i) ρ := by
    intro ρ _ hρ i a
    refine Integrable.const_mul (Integrable.of_bound (continuous_pow i).aestronglyMeasurable 1
      (hρ.mono fun x hx => ?_)) a
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
  have hevint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ q : Polynomial ℝ, Integrable (fun x => q.eval x) ρ := by
    intro ρ _ hρ q
    simp_rw [Polynomial.eval_eq_sum_range]
    exact integrable_finsetSum _ (fun i _ => hmono ρ hρ i _)
  have hpoly : ∀ q : Polynomial ℝ, ∫ x, q.eval x ∂μ = ∫ x, q.eval x ∂ν := by
    intro q
    simp_rw [Polynomial.eval_eq_sum_range]
    rw [integral_finsetSum _ (fun i _ => hmono μ aeμ i _),
      integral_finsetSum _ (fun i _ => hmono ν aeν i _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul, integral_const_mul, h i]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 1 f f.continuous.continuousOn
    (ε / 2) (by linarith)
  have hclose : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      (∀ᵐ x ∂ρ, x ∈ Set.Icc (0 : ℝ) 1) → |∫ x, f x ∂ρ - ∫ x, q.eval x ∂ρ| ≤ ε / 2 := by
    intro ρ _ hρ
    rw [← integral_sub (f.integrable ρ) (hevint ρ hρ q)]
    have := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun x => f x - q.eval x)
      (C := ε / 2) (hρ.mono fun x hx => by rw [Real.norm_eq_abs, abs_sub_comm]; exact (hq x hx).le)
    simpa using this
  have h1 := hclose μ aeμ
  have h2 := hclose ν aeν
  rw [hpoly q] at h1
  rw [Real.dist_eq]
  have h3 := abs_sub_le (∫ x, f x ∂μ) (∫ x, q.eval x ∂ν) (∫ x, f x ∂ν)
  rw [abs_sub_comm (∫ x, q.eval x ∂ν)] at h3
  linarith

end DeFinettiAux

open MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXmeas : ∀ i, Measurable (X i))
    (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hexch : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      P.map (fun ω (i : Fin n) => X (σ i) ω) = P.map (fun ω (i : Fin n) => X i ω)) :
    ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      (∀ n k : ℕ, k ≤ n →
        (P {ω | ∀ i < n, X i ω = if i < k then 1 else 0}).toReal
            = ∫ θ, θ ^ k * (1 - θ) ^ (n - k) ∂F ∧
        (P {ω | ∑ i ∈ Finset.range n, X i ω = k}).toReal
            = (n.choose k : ℝ) * ∫ θ, θ ^ k * (1 - θ) ^ (n - k) ∂F) ∧
      ∀ G : Measure ℝ, IsProbabilityMeasure G → G (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        (∀ n k : ℕ, k ≤ n →
          (P {ω | ∀ i < n, X i ω = if i < k then 1 else 0}).toReal
            = ∫ θ, θ ^ k * (1 - θ) ^ (n - k) ∂G) →
        G = F := by
  classical
  obtain ⟨T, hTm, hT01, hlim⟩ := DeFinettiAux.exists_limit P hXmeas hX01 hexch
  have hmom := DeFinettiAux.moment P hXmeas hX01 hexch T hTm hT01 hlim
  have hmom0 : ∀ m, ∫ ω, T ω ^ m ∂P = DeFinettiAux.cm P X m := fun m => by
    simpa using hmom m ∅
  set F : Measure ℝ := P.map T with hFdef
  have hF : IsProbabilityMeasure F := Measure.isProbabilityMeasure_map hTm.aemeasurable
  have hFsupp : F (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [hFdef, Measure.map_apply hTm measurableSet_Icc.compl]
    have : T ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ = ∅ := by
      ext ω; simp [hT01 ω]
    rw [this, measure_empty]
  have hFint : ∀ a c : ℕ, ∫ θ, θ ^ a * (1 - θ) ^ c ∂F = ∫ ω, T ω ^ a * (1 - T ω) ^ c ∂P :=
    fun a c => integral_map hTm.aemeasurable (by fun_prop : Continuous fun θ : ℝ =>
      θ ^ a * (1 - θ) ^ c).aestronglyMeasurable
  have hpatI := DeFinettiAux.pat_integral P hXmeas hX01 hexch T hTm hT01 hmom0
  have hpat : ∀ n k : ℕ, k ≤ n →
      (P {ω | ∀ i < n, X i ω = if i < k then 1 else 0}).toReal
        = ∫ θ, θ ^ k * (1 - θ) ^ (n - k) ∂F := by
    intro n k hkn
    rw [DeFinettiAux.pat_prob P hXmeas hX01 n (fun i => i < k), hpatI n (fun i => i < k), hFint,
      DeFinettiAux.filter_lt_range k n hkn, Finset.card_range]
  refine ⟨F, hF, hFsupp, fun n k hkn => ⟨hpat n k hkn, ?_⟩, ?_⟩
  · -- the law of the partial sum
    have hpt : ∀ ω, (∑ A ∈ Finset.powersetCard k (Finset.range n),
        ∏ i ∈ Finset.range n, (if i ∈ A then X i ω else 1 - X i ω))
          = if ∑ i ∈ Finset.range n, X i ω = k then 1 else 0 := by
      intro ω
      set A0 := (Finset.range n).filter (fun i => X i ω = 1) with hA0
      have hterm : ∀ A ∈ Finset.powersetCard k (Finset.range n),
          ∏ i ∈ Finset.range n, (if i ∈ A then X i ω else 1 - X i ω)
            = if A = A0 then 1 else 0 := by
        intro A hA
        have hAsub := (Finset.mem_powersetCard.1 hA).1
        rw [DeFinettiAux.prod_pattern hX01 n (fun i => i ∈ A) ω]
        refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
        · ext i
          simp only [hA0, Finset.mem_filter, Finset.mem_range]
          constructor
          · intro hi
            have hin := Finset.mem_range.1 (hAsub hi)
            exact ⟨hin, by rw [h i hin, if_pos hi]⟩
          · rintro ⟨hin, h1⟩
            by_contra hi
            rw [h i hin, if_neg hi] at h1
            norm_num at h1
        · intro i hi
          subst h
          by_cases h1 : X i ω = 1
          · rw [if_pos (show i ∈ A0 from Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, h1⟩), h1]
          · rw [if_neg (show i ∉ A0 from fun hm => h1 (Finset.mem_filter.1 hm).2)]
            rcases hX01 i ω with h0 | h0
            · exact h0
            · exact absurd h0 h1
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      have hsum : ∑ i ∈ Finset.range n, X i ω = (A0.card : ℝ) := by
        calc ∑ i ∈ Finset.range n, X i ω
            = ∑ i ∈ Finset.range n, (if X i ω = 1 then (1 : ℝ) else 0) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rcases hX01 i ω with h | h <;> simp [h]
          _ = A0.card := by rw [Finset.sum_boole]
      rw [hsum]
      exact if_congr ⟨fun h => by rw [(Finset.mem_powersetCard.1 h).2],
        fun h => Finset.mem_powersetCard.2 ⟨Finset.filter_subset _ _, by exact_mod_cast h⟩⟩
        rfl rfl
    have hmeasS : MeasurableSet {ω | ∑ i ∈ Finset.range n, X i ω = k} :=
      measurableSet_eq_fun (Finset.measurable_sum _ (fun i _ => hXmeas i)) measurable_const
    have hind : ∀ ω, Set.indicator {ω | ∑ i ∈ Finset.range n, X i ω = k} 1 ω
        = ∑ A ∈ Finset.powersetCard k (Finset.range n),
            ∏ i ∈ Finset.range n, (if i ∈ A then X i ω else 1 - X i ω) := by
      intro ω
      rw [hpt ω]
      by_cases h : ∑ i ∈ Finset.range n, X i ω = k
      · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω | ∑ i ∈ Finset.range n, X i ω = k}
          from h)]; rfl
      · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | ∑ i ∈ Finset.range n, X i ω = k}
          from h)]
    have hprodint : ∀ A : Finset ℕ, Integrable (fun ω =>
        ∏ i ∈ Finset.range n, (if i ∈ A then X i ω else 1 - X i ω)) P := by
      intro A
      refine DeFinettiAux.int_of_bdd P ?_ (fun ω => ?_)
      · exact Finset.measurable_prod _ (fun i _ => by
          by_cases h : i ∈ A
          · simp only [h, if_true]; exact hXmeas i
          · simp only [h, if_false]; exact measurable_const.sub (hXmeas i))
      · rw [DeFinettiAux.prod_pattern hX01 n (fun i => i ∈ A) ω]
        split_ifs <;> norm_num
    rw [← measureReal_def, ← integral_indicator_one hmeasS]
    simp_rw [hind]
    rw [integral_finsetSum _ (fun A _ => hprodint A)]
    rw [Finset.sum_congr rfl (fun A hA => by
      rw [hpatI n (fun i => i ∈ A), Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 (Finset.mem_powersetCard.1 hA).1,
        (Finset.mem_powersetCard.1 hA).2, ← hFint])]
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_range, nsmul_eq_mul]
  · intro G hG hGsupp hGid
    haveI := hG
    apply DeFinettiAux.moments_ext G F hGsupp hFsupp
    intro m
    have h1 := hGid m m le_rfl
    rw [hpat m m le_rfl] at h1
    simpa using h1.symm
