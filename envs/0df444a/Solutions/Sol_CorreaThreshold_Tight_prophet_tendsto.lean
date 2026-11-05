-- Prove2me | solution 1 for CorreaThreshold.Tight.prophet_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:09:26.115428+00:00
-- url     : https://prove2.me/submissions/0d4a972b-3eff-43da-ada3-fa0c91bf837f

import Mathlib
import Definitions.Def_CorreaThreshold_Tight_Setting
import Theorems.Thm_CorreaThreshold_Tight_prop_A_3

open MeasureTheory CorreaThreshold.Tight

namespace CorreaIIDTightAux

lemma e_bounds : (2.7182818283 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 2.7182818286 :=
  ⟨Real.exp_one_gt_d9, Real.exp_one_lt_d9⟩

lemma c_pos : 0 < Real.exp 1 - 2 := by linarith [e_bounds.1]

lemma c_lt_one : Real.exp 1 - 2 < 1 := by linarith [e_bounds.2]

lemma hi_gt (n : ℕ) (hn : 2 ≤ n) : (n : ℝ) < hi n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold hi
  rw [lt_div_iff₀ c_pos]
  nlinarith [c_lt_one]

lemma hi_ne_one (n : ℕ) (hn : 2 ≤ n) : hi n ≠ 1 := by
  have := hi_gt n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  intro h; linarith

lemma hi_ne_zero (n : ℕ) (hn : 2 ≤ n) : hi n ≠ 0 := by
  have := hi_gt n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  intro h; linarith

lemma lint_lawN (n : ℕ) (g : ℝ → ENNReal) :
    ∫⁻ y, g y ∂(lawN n) = ENNReal.ofReal (1 / (n : ℝ) ^ 3) * g (hi n) +
      ENNReal.ofReal (1 / (n : ℝ)) * g 1 +
      ENNReal.ofReal (1 - 1 / (n : ℝ) - 1 / (n : ℝ) ^ 3) * g 0 := by
  simp [lawN, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]

lemma weights_sum (n : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal (1 / (n : ℝ) ^ 3) + ENNReal.ofReal (1 / (n : ℝ)) +
      ENNReal.ofReal (1 - 1 / (n : ℝ) - 1 / (n : ℝ) ^ 3) = 1 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 ≤ 1 / (n : ℝ) ^ 3 := by positivity
  have h2 : 0 ≤ 1 / (n : ℝ) := by positivity
  have h3 : 0 ≤ 1 - 1 / (n : ℝ) - 1 / (n : ℝ) ^ 3 := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have : 1 / (n : ℝ) ^ 3 ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (8:ℝ) ≤ (n:ℝ)^3 := by
        have := pow_le_pow_left₀ (by norm_num) hn' 3; norm_num at this; linarith
      linarith
    linarith
  rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by positivity) h3]
  rw [show 1 / (n : ℝ) ^ 3 + 1 / (n : ℝ) + (1 - 1 / (n : ℝ) - 1 / (n : ℝ) ^ 3) = 1 by ring]
  simp

instance lawN_prob (n : ℕ) [Fact (2 ≤ n)] : IsProbabilityMeasure (lawN n) := by
  constructor
  have := lint_lawN n (fun _ => 1)
  simp only [lintegral_const, mul_one, one_mul] at this
  rw [this]
  exact weights_sum n Fact.out

lemma lint_pi_prod (n m : ℕ) [Fact (2 ≤ n)] (f : Fin m → ℝ → ENNReal)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) =
      ∏ i, ∫⁻ y, f i y ∂(lawN n) := by
  unfold SamuelCahnProphet.IID.iidLaw
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : Fin m → ℝ) => f i (x i))
    (ProbabilityTheory.iIndepFun_pi (fun i => (hf i).aemeasurable))
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : Fin m => lawN n) i).lintegral_comp (hf i)


/-! ### `t`-integrals -/

lemma lint_Ioc_ofReal (f : ℝ → ℝ) (hf : Continuous f) (hnn : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f t) :
    ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (f t) = ENNReal.ofReal (∫ t in (0:ℝ)..1, f t) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact (hf.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hnn t ht.1.le ht.2

lemma lint_tpow (J : ℕ) :
    ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal t ^ J = ENNReal.ofReal (1 / ((J : ℝ) + 1)) := by
  have : ∀ t : ℝ, t ∈ Set.Ioc (0:ℝ) 1 → ENNReal.ofReal t ^ J = ENNReal.ofReal (t ^ J) :=
    fun t ht => (ENNReal.ofReal_pow ht.1.le J).symm
  rw [setLIntegral_congr_fun measurableSet_Ioc this]
  rw [lint_Ioc_ofReal (fun t => t ^ J) (continuous_pow J) (fun t ht _ => pow_nonneg ht J)]
  rw [integral_pow]
  norm_num

lemma integral_lin_pow (p : ℝ) (hp : 0 < p) (j : ℕ) :
    ∫ t in (0:ℝ)..1, ((1 - p) + p * t) ^ j = (1 - (1 - p) ^ (j + 1)) / (p * (j + 1)) := by
  have h := intervalIntegral.integral_comp_mul_add (fun x : ℝ => x ^ j) hp.ne' (1 - p)
    (a := 0) (b := 1)
  rw [show (fun t : ℝ => ((1 - p) + p * t) ^ j) = fun t => (p * t + (1 - p)) ^ j by
    funext t; ring_nf]
  rw [h, integral_pow]
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul]
  rw [show p + (1 - p) = 1 by ring]
  field_simp
  ring


/-! ### product-form integrands -/

open Classical in
noncomputable def psi {m : ℕ} (A : Finset (Fin m)) (t : ℝ) (j : Fin m) (y : ℝ) : ENNReal :=
  if j ∈ A then (if y = 1 then ENNReal.ofReal t else 1) else 1

open Classical in
noncomputable def Jc {m : ℕ} (A : Finset (Fin m)) (x : Fin m → ℝ) : ℕ :=
  (A.filter (fun j => x j = 1)).card

lemma prod_psi {m : ℕ} (A : Finset (Fin m)) (t : ℝ) (x : Fin m → ℝ) :
    ∏ j, psi A t j (x j) = ENNReal.ofReal t ^ Jc A x := by
  classical
  unfold psi Jc
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]

lemma psi_meas {m : ℕ} (A : Finset (Fin m)) (t : ℝ) (j : Fin m) : Measurable (psi A t j) := by
  unfold psi
  by_cases hj : j ∈ A
  · simp only [hj, if_true]
    exact Measurable.ite (measurableSet_singleton (1:ℝ)) measurable_const measurable_const
  · simp only [hj, if_false]; exact measurable_const

lemma psi_meas2 {m : ℕ} (A : Finset (Fin m)) (j : Fin m) :
    Measurable (fun p : (Fin m → ℝ) × ℝ => psi A p.2 j (p.1 j)) := by
  unfold psi
  by_cases hj : j ∈ A
  · simp only [hj, if_true]
    exact Measurable.ite ((measurableSet_singleton (1:ℝ)).preimage
      ((measurable_pi_apply j).comp measurable_fst))
      (ENNReal.measurable_ofReal.comp measurable_snd) measurable_const
  · simp only [hj, if_false]; exact measurable_const

lemma lint_psi (n : ℕ) [Fact (2 ≤ n)] {m : ℕ} (A : Finset (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (j : Fin m) :
    ∫⁻ y, psi A t j y ∂(lawN n) =
      if j ∈ A then ENNReal.ofReal (1 - 1 / (n : ℝ) + t / n) else 1 := by
  have hn : 2 ≤ n := Fact.out
  by_cases hj : j ∈ A
  · simp only [hj, if_true]
    rw [lint_lawN]
    simp only [psi, hj, if_true, hi_ne_one n hn, if_false, zero_ne_one, mul_one]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : 0 ≤ 1 - 1 / (n : ℝ) - 1 / (n : ℝ) ^ 3 := by
      have : 1 / (n : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have : 1 / (n : ℝ) ^ 3 ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (8:ℝ) ≤ (n:ℝ)^3 := by
          have := pow_le_pow_left₀ (by norm_num) hn' 3; norm_num at this; linarith
        linarith
      linarith
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) h3]
    congr 1; ring
  · simp only [hj, if_false]
    simp only [psi, hj, if_false]
    rw [lintegral_const, measure_univ, mul_one]


instance iid_prob (n m : ℕ) [Fact (2 ≤ n)] :
    IsProbabilityMeasure (SamuelCahnProphet.IID.iidLaw (lawN n) m) := by
  unfold SamuelCahnProphet.IID.iidLaw; infer_instance

lemma lint_prod_psi (n : ℕ) [Fact (2 ≤ n)] {m : ℕ} (A : Finset (Fin m)) (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ x, ∏ j, psi A t j (x j) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) =
      ENNReal.ofReal (1 - 1 / (n : ℝ) + t / n) ^ A.card := by
  classical
  rw [lint_pi_prod n m _ (fun j => psi_meas A t j)]
  simp_rw [lint_psi n A t ht]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

lemma lint_ind1 (n : ℕ) [Fact (2 ≤ n)] {m : ℕ} (A : Finset (Fin m)) :
    ∫⁻ x, (1 - ∏ j, psi A 0 j (x j)) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) =
      ENNReal.ofReal (1 - (1 - 1 / (n : ℝ)) ^ A.card) := by
  have hn : 2 ≤ n := Fact.out
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hmeas : Measurable (fun x : Fin m → ℝ => ∏ j, psi A 0 j (x j)) :=
    Finset.measurable_prod _ (fun j _ => (psi_meas A 0 j).comp (measurable_pi_apply j))
  rw [lintegral_sub (f := fun _ => (1 : ENNReal)) hmeas]
  · rw [lint_prod_psi n A 0 le_rfl, lintegral_const, measure_univ, mul_one]
    simp only [zero_div, add_zero]
    rw [← ENNReal.ofReal_pow hq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (pow_nonneg hq _)]
  · rw [lint_prod_psi n A 0 le_rfl]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · filter_upwards with x
    rw [prod_psi, ENNReal.ofReal_zero]
    rcases Nat.eq_zero_or_pos (Jc A x) with h | h
    · simp [h]
    · simp [zero_pow h.ne']


open Classical in
noncomputable def Tt (n : ℕ) {m : ℕ} (A : Finset (Fin m)) (i : Fin m) (t : ℝ) (x : Fin m → ℝ) :
    ENNReal :=
  (if x i = hi n then 1 else 0) * ∏ j, psi A t j (x j)

open Classical in
noncomputable def theta (n : ℕ) {m : ℕ} (A : Finset (Fin m)) (i : Fin m) (t : ℝ) (j : Fin m)
    (y : ℝ) : ENNReal :=
  (if j = i then (if y = hi n then 1 else 0) else 1) * psi A t j y

lemma Tt_eq (n : ℕ) {m : ℕ} (A : Finset (Fin m)) (i : Fin m) (t : ℝ) (x : Fin m → ℝ) :
    Tt n A i t x = ∏ j, theta n A i t j (x j) := by
  classical
  unfold Tt theta
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite_eq']
  simp

lemma Tt_meas2 (n : ℕ) {m : ℕ} (A : Finset (Fin m)) (i : Fin m) :
    Measurable (fun p : (Fin m → ℝ) × ℝ => Tt n A i p.2 p.1) := by
  unfold Tt
  refine Measurable.mul ?_ (Finset.measurable_prod _ (fun j _ => psi_meas2 A j))
  exact Measurable.ite ((measurableSet_singleton (hi n)).preimage
      ((measurable_pi_apply i).comp measurable_fst)) measurable_const measurable_const

lemma lint_Tt_le (n : ℕ) [Fact (2 ≤ n)] {m : ℕ} (A : Finset (Fin m)) (i : Fin m) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫⁻ x, Tt n A i t x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 3) * ENNReal.ofReal (1 - 1 / (n : ℝ) + t / n) ^ (A.card - 1) := by
  classical
  have hn : 2 ≤ n := Fact.out
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  simp_rw [Tt_eq]
  have hmeas : ∀ j, Measurable (theta n A i t j) := by
    intro j
    unfold theta
    refine Measurable.mul ?_ (psi_meas A t j)
    by_cases h : j = i
    · simp only [h, if_true]
      exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const
    · simp only [h, if_false]; exact measurable_const
  rw [lint_pi_prod n m _ hmeas]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have h1 : (1:ℝ) ≠ hi n := (hi_ne_one n hn).symm
  have h0 : (0:ℝ) ≠ hi n := (hi_ne_zero n hn).symm
  have hi_int : ∫⁻ y, theta n A i t i y ∂(lawN n) = ENNReal.ofReal (1 / (n : ℝ) ^ 3) := by
    rw [lint_lawN]; simp [theta, psi, hi_ne_one n hn, h1, h0]
  rw [hi_int]
  gcongr
  have : ∀ j ∈ Finset.univ.erase i, ∫⁻ y, theta n A i t j y ∂(lawN n) =
      if j ∈ A then ENNReal.ofReal (1 - 1 / (n : ℝ) + t / n) else 1 := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp only [theta, hji, if_false, one_mul]
    exact lint_psi n A t ht0 j
  rw [Finset.prod_congr rfl this, Finset.prod_ite_mem, Finset.prod_const]
  apply pow_le_pow_right_of_le_one'
  · rw [ENNReal.ofReal_le_one]
    have : t / (n : ℝ) ≤ 1 / n := div_le_div_of_nonneg_right ht1 (by positivity)
    linarith
  · calc A.card - 1 ≤ (A.erase i).card := Finset.pred_card_le_card_erase
      _ ≤ _ := Finset.card_le_card (fun j hj => by
        simp only [Finset.mem_erase, Finset.mem_inter, Finset.mem_univ, and_true] at hj ⊢
        exact hj)

end CorreaIIDTightAux


open MeasureTheory CorreaThreshold.Tight

namespace CorreaIIDTightAux

open Classical in
noncomputable def accS {m : ℕ} (τ : Fin m → ENNReal) (x : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => τ i < ENNReal.ofReal (x i))

lemma ratioS_eq {m : ℕ} (τ : Fin m → ENNReal) (x : Fin m → ℝ) :
    ratioS τ x = (∑ i ∈ accS τ x, x i) / ((accS τ x).card : ℝ) := by
  unfold ratioS accS
  congr

open Classical in
noncomputable def Aset {m : ℕ} (τ : Fin m → ENNReal) : Finset (Fin m) :=
  Finset.univ.filter (fun i => τ i < 1)

open Classical in
noncomputable def ind (n : ℕ) (y : ℝ) : ENNReal := if y = hi n then 1 else 0

noncomputable def B0 {m : ℕ} (A : Finset (Fin m)) (x : Fin m → ℝ) : ENNReal :=
  1 - ∏ j, psi A 0 j (x j)

noncomputable def B1 (n : ℕ) {m : ℕ} (A : Finset (Fin m)) (x : Fin m → ℝ) : ENNReal :=
  ∑ i, (ind n (x i) + ENNReal.ofReal (hi n) * ∫⁻ t in Set.Ioc (0:ℝ) 1, Tt n A i t x)

noncomputable def B2 (n : ℕ) {m : ℕ} (x : Fin m → ℝ) : ENNReal :=
  ENNReal.ofReal (hi n) * ∑ i, ∑ j, if j = i then 0 else ind n (x i) * ind n (x j)

lemma avg_le {m : ℕ} (s : Finset (Fin m)) (x : Fin m → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ i ∈ s, x i ≤ M) : (∑ i ∈ s, x i) / (s.card : ℝ) ≤ M := by
  rcases Nat.eq_zero_or_pos s.card with hc | hc
  · simp [hc, hM]
  · rw [div_le_iff₀ (by exact_mod_cast hc)]
    have := Finset.sum_le_card_nsmul s x M h
    simpa [nsmul_eq_mul, mul_comm] using this

lemma pointwise (n : ℕ) (hn : 2 ≤ n) {m : ℕ} (τ : Fin m → ENNReal) (x : Fin m → ℝ)
    (hx : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = hi n) :
    ENNReal.ofReal (ratioS τ x) ≤ B0 (Aset τ) x + B1 n (Aset τ) x + B2 n x := by
  classical
  have hhi1 : (1:ℝ) < hi n := by
    have := hi_gt n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hhi0 : (0:ℝ) ≤ hi n := by linarith
  set A := Aset τ with hA
  set S := accS τ x with hS
  have F1 : ∀ i ∈ S, 0 < x i := by
    intro i hi'
    simp only [hS, accS, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
    have : (0:ENNReal) < ENNReal.ofReal (x i) := lt_of_le_of_lt (zero_le) hi'
    exact ENNReal.ofReal_pos.1 this
  have F2 : ∀ i ∈ S, x i ≠ hi n → x i = 1 ∧ i ∈ A := by
    intro i hi' hne
    have hpos := F1 i hi'
    have h1 : x i = 1 := by
      rcases hx i with h | h | h
      · linarith
      · exact h
      · exact absurd h hne
    refine ⟨h1, ?_⟩
    simp only [hS, accS, Finset.mem_filter, Finset.mem_univ, true_and, h1,
      ENNReal.ofReal_one] at hi'
    simp [hA, Aset, hi']
  have F3 : ∀ i ∈ A, x i = 1 → i ∈ S := by
    intro i hiA h1
    simp only [hA, Aset, Finset.mem_filter, Finset.mem_univ, true_and] at hiA
    simp [hS, accS, h1, hiA]
  have F4 : ∀ i, x i ≤ hi n := by
    intro i; rcases hx i with h | h | h <;> rw [h] <;> linarith
  rw [ratioS_eq]
  by_cases hH : ∃ i j, i ≠ j ∧ x i = hi n ∧ x j = hi n
  · -- K ≥ 2
    obtain ⟨i, j, hij, hi_, hj_⟩ := hH
    have hr : (∑ i ∈ S, x i) / (S.card : ℝ) ≤ hi n := avg_le S x _ hhi0 (fun i _ => F4 i)
    calc ENNReal.ofReal ((∑ i ∈ S, x i) / (S.card : ℝ)) ≤ ENNReal.ofReal (hi n) :=
          ENNReal.ofReal_le_ofReal hr
      _ ≤ B2 n x := by
          unfold B2
          conv_lhs => rw [← mul_one (ENNReal.ofReal (hi n))]
          gcongr
          have hterm : (1:ENNReal) = (fun j' => if j' = i then 0 else ind n (x i) * ind n (x j')) j := by
            simp [Ne.symm hij, ind, hi_, hj_]
          calc (1:ENNReal) ≤ ∑ j', (if j' = i then 0 else ind n (x i) * ind n (x j')) := by
                rw [hterm]; exact Finset.single_le_sum (f := fun j' => if j' = i then (0:ENNReal) else ind n (x i) * ind n (x j')) (fun _ _ => zero_le) (Finset.mem_univ j)
            _ ≤ ∑ i', ∑ j', (if j' = i' then 0 else ind n (x i') * ind n (x j')) :=
                Finset.single_le_sum (f := fun i' => ∑ j', (if j' = i' then 0 else
                  ind n (x i') * ind n (x j'))) (fun _ _ => zero_le) (Finset.mem_univ i)
      _ ≤ _ := le_add_left le_rfl
  push Not at hH
  by_cases h0 : ∃ i0, x i0 = hi n
  · obtain ⟨i0, hi0⟩ := h0
    have huniq : ∀ i, i ≠ i0 → x i ≠ hi n := fun i hne h => hH i i0 hne h hi0
    -- the term i0 of B1
    have hTt : ∀ t, Tt n A i0 t x = ENNReal.ofReal t ^ Jc A x := by
      intro t; unfold Tt; rw [if_pos hi0, one_mul, prod_psi]
    have hterm : ind n (x i0) + ENNReal.ofReal (hi n) *
        ∫⁻ t in Set.Ioc (0:ℝ) 1, Tt n A i0 t x =
        1 + ENNReal.ofReal (hi n) * ENNReal.ofReal (1 / ((Jc A x : ℝ) + 1)) := by
      simp_rw [hTt]; rw [lint_tpow]; simp [ind, hi0]
    have hle : ind n (x i0) + ENNReal.ofReal (hi n) *
        ∫⁻ t in Set.Ioc (0:ℝ) 1, Tt n A i0 t x ≤ B1 n A x := by
      unfold B1
      exact Finset.single_le_sum (f := fun i => ind n (x i) + ENNReal.ofReal (hi n) *
        ∫⁻ t in Set.Ioc (0:ℝ) 1, Tt n A i t x) (fun _ _ => zero_le) (Finset.mem_univ i0)
    rw [hterm] at hle
    have hJ : (0:ℝ) ≤ Jc A x := Nat.cast_nonneg _
    by_cases hin : i0 ∈ S
    · have hSeq : S = insert i0 (A.filter (fun j => x j = 1)) := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_filter]
        constructor
        · intro hj
          by_cases hji : j = i0
          · exact Or.inl hji
          · exact Or.inr ⟨(F2 j hj (huniq j hji)).2, (F2 j hj (huniq j hji)).1⟩
        · rintro (h | ⟨hjA, hj1⟩)
          · exact h ▸ hin
          · exact F3 j hjA hj1
      have hnot : i0 ∉ A.filter (fun j => x j = 1) := by
        simp only [Finset.mem_filter, not_and]
        intro _ h; rw [hi0] at h; linarith
      have hsum : ∑ i ∈ S, x i = hi n + (Jc A x : ℝ) := by
        rw [hSeq, Finset.sum_insert hnot, hi0]
        congr 1
        rw [Finset.sum_congr rfl (fun j hj => (Finset.mem_filter.1 hj).2)]
        simp [Jc]
      have hcard : (S.card : ℝ) = (Jc A x : ℝ) + 1 := by
        rw [hSeq, Finset.card_insert_of_notMem hnot]
        push_cast; simp [Jc]
      rw [hsum, hcard]
      have hreal : (hi n + (Jc A x : ℝ)) / ((Jc A x : ℝ) + 1) ≤
          1 + hi n * (1 / ((Jc A x : ℝ) + 1)) := by
        have h1 : (Jc A x : ℝ) / ((Jc A x : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        rw [add_div, mul_one_div]
        linarith
      calc ENNReal.ofReal ((hi n + (Jc A x : ℝ)) / ((Jc A x : ℝ) + 1))
          ≤ ENNReal.ofReal (1 + hi n * (1 / ((Jc A x : ℝ) + 1))) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = 1 + ENNReal.ofReal (hi n) * ENNReal.ofReal (1 / ((Jc A x : ℝ) + 1)) := by
            rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
              ENNReal.ofReal_mul hhi0]
        _ ≤ B1 n A x := hle
        _ ≤ _ := by
            rw [add_comm (B0 A x)]
            exact le_add_right (le_add_right le_rfl)
    · have hr : (∑ i ∈ S, x i) / (S.card : ℝ) ≤ 1 := by
        refine avg_le S x 1 zero_le_one (fun i hi' => ?_)
        have hne : i ≠ i0 := fun h => hin (h ▸ hi')
        exact le_of_eq (F2 i hi' (huniq i hne)).1
      calc ENNReal.ofReal ((∑ i ∈ S, x i) / (S.card : ℝ)) ≤ 1 := by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
        _ ≤ 1 + ENNReal.ofReal (hi n) * ENNReal.ofReal (1 / ((Jc A x : ℝ) + 1)) := le_self_add
        _ ≤ B1 n A x := hle
        _ ≤ _ := by
            rw [add_comm (B0 A x)]
            exact le_add_right (le_add_right le_rfl)
  · push Not at h0
    rcases S.eq_empty_or_nonempty with hSe | ⟨j, hj⟩
    · rw [← hS, hSe]; simp
    · have hr : (∑ i ∈ S, x i) / (S.card : ℝ) ≤ 1 :=
        avg_le S x 1 zero_le_one (fun i hi' => le_of_eq (F2 i hi' (h0 i)).1)
      have hJpos : 0 < Jc A x := by
        unfold Jc
        apply Finset.card_pos.2
        exact ⟨j, Finset.mem_filter.2 ⟨(F2 j hj (h0 j)).2, (F2 j hj (h0 j)).1⟩⟩
      have hB0 : B0 A x = 1 := by
        unfold B0; rw [prod_psi, ENNReal.ofReal_zero, zero_pow hJpos.ne', tsub_zero]
      calc ENNReal.ofReal ((∑ i ∈ S, x i) / (S.card : ℝ)) ≤ 1 := by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
        _ = B0 A x := hB0.symm
        _ ≤ _ := le_add_right (le_add_right le_rfl)

end CorreaIIDTightAux


open MeasureTheory CorreaThreshold.Tight

namespace CorreaIIDTightAux

lemma ae_lawN (n : ℕ) : ∀ᵐ y ∂(lawN n), y = 0 ∨ y = 1 ∨ y = hi n := by
  unfold lawN
  rw [ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩, Measure.ae_smul_measure ?_ _⟩ <;>
    rw [ae_dirac_eq] <;> simp

lemma ae_support (n m : ℕ) [Fact (2 ≤ n)] :
    ∀ᵐ x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m), ∀ i, x i = 0 ∨ x i = 1 ∨ x i = hi n := by
  rw [ae_all_iff]
  intro i
  unfold SamuelCahnProphet.IID.iidLaw
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => lawN n) (i := i)).eventually (ae_lawN n)

lemma ind_meas (n : ℕ) : Measurable (ind n) := by
  unfold ind
  exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const

lemma lint_ind (n : ℕ) [Fact (2 ≤ n)] {m : ℕ} (i : Fin m) :
    ∫⁻ x, ind n (x i) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) =
      ENNReal.ofReal (1 / (n : ℝ) ^ 3) := by
  have hn : 2 ≤ n := Fact.out
  unfold SamuelCahnProphet.IID.iidLaw
  rw [(measurePreserving_eval (fun _ : Fin m => lawN n) i).lintegral_comp (ind_meas n)]
  rw [lint_lawN]
  have h1 : (1:ℝ) ≠ hi n := (hi_ne_one n hn).symm
  have h0 : (0:ℝ) ≠ hi n := (hi_ne_zero n hn).symm
  simp [ind, h1, h0]

lemma lint_ind2 (n : ℕ) [Fact (2 ≤ n)] {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ∫⁻ x, ind n (x i) * ind n (x j) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) =
      ENNReal.ofReal (1 / (n : ℝ) ^ 3) * ENNReal.ofReal (1 / (n : ℝ) ^ 3) := by
  classical
  let f : Fin m → ℝ → ENNReal := fun k y => if k = i then ind n y else if k = j then ind n y else 1
  have hf : ∀ k, Measurable (f k) := by
    intro k; simp only [f]
    split_ifs
    · exact ind_meas n
    · exact ind_meas n
    · exact measurable_const
  have hprod : ∀ x : Fin m → ℝ, ∏ k, f k (x k) = ind n (x i) * ind n (x j) := by
    intro x
    rw [Finset.prod_eq_mul i j hij]
    · simp [f, Ne.symm hij]
    · intro c _ hc; simp [f, hc.1, hc.2]
    · simp
    · simp
  simp_rw [← hprod]
  rw [lint_pi_prod n m f hf]
  rw [Finset.prod_eq_mul i j hij]
  · have hn : 2 ≤ n := Fact.out
    have hh : ∫⁻ y, ind n y ∂(lawN n) = ENNReal.ofReal (1 / (n : ℝ) ^ 3) := by
      rw [lint_lawN]
      have h1 : (1:ℝ) ≠ hi n := (hi_ne_one n hn).symm
      have h0 : (0:ℝ) ≠ hi n := (hi_ne_zero n hn).symm
      simp [ind, h1, h0]
    simp [f, Ne.symm hij, hh]
  · intro c _ hc; simp [f, hc.1, hc.2]
  · simp
  · simp

lemma B0_meas {m : ℕ} (A : Finset (Fin m)) : Measurable (B0 A) := by
  unfold B0
  exact measurable_const.sub
    (Finset.measurable_prod _ (fun j _ => (psi_meas A 0 j).comp (measurable_pi_apply j)))

lemma B2_meas (n : ℕ) (m : ℕ) : Measurable (fun x : Fin m → ℝ => B2 n x) := by
  unfold B2
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  by_cases h : j = i
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]
    exact ((ind_meas n).comp (measurable_pi_apply i)).mul ((ind_meas n).comp (measurable_pi_apply j))

lemma G_meas (n : ℕ) {m : ℕ} (A : Finset (Fin m)) (i : Fin m) :
    Measurable (fun x : Fin m → ℝ => ∫⁻ t in Set.Ioc (0:ℝ) 1, Tt n A i t x) :=
  (Tt_meas2 n A i).lintegral_prod_right'

lemma lint_B2_le (n : ℕ) [Fact (2 ≤ n)] (m : ℕ) :
    ∫⁻ x, B2 n x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) ≤
      ENNReal.ofReal (hi n * ((m : ℝ) * ((m : ℝ) * (1 / (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 3))))) := by
  classical
  have hn : 2 ≤ n := Fact.out
  have hhi0 : 0 ≤ hi n := by have := hi_gt n hn; linarith [(by positivity : (0:ℝ) ≤ n)]
  unfold B2
  rw [lintegral_const_mul _ (by
    refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
    by_cases h : j = i
    · simp only [h, if_true]; exact measurable_const
    · simp only [h, if_false]
      exact ((ind_meas n).comp (measurable_pi_apply i)).mul
        ((ind_meas n).comp (measurable_pi_apply j)))]
  rw [ENNReal.ofReal_mul hhi0]
  gcongr
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun j _ => by
    by_cases h : j = i
    · simp only [h, if_true]; exact measurable_const
    · simp only [h, if_false]
      exact ((ind_meas n).comp (measurable_pi_apply i)).mul
        ((ind_meas n).comp (measurable_pi_apply j))))]
  have key : ∀ i : Fin m, ∫⁻ x, (∑ j, if j = i then 0 else ind n (x i) * ind n (x j))
      ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) ≤
      ENNReal.ofReal ((m : ℝ) * (1 / (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 3))) := by
    intro i
    rw [lintegral_finsetSum _ (fun j _ => by
      by_cases h : j = i
      · simp only [h, if_true]; exact measurable_const
      · simp only [h, if_false]
        exact ((ind_meas n).comp (measurable_pi_apply i)).mul
          ((ind_meas n).comp (measurable_pi_apply j)))]
    have : ∀ j ∈ (Finset.univ : Finset (Fin m)), ∫⁻ x, (if j = i then 0 else ind n (x i) * ind n (x j))
        ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 3)) := by
      intro j _
      by_cases h : j = i
      · simp [h]
      · simp only [h, if_false]
        rw [lint_ind2 n i j (Ne.symm h), ← ENNReal.ofReal_mul (by positivity)]
    refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity)]
  refine (Finset.sum_le_card_nsmul _ _ _ (fun i _ => key i)).trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e1 : ENNReal.ofReal ((m : ℝ) * (1 / (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 3))) =
      (m : ENNReal) * ENNReal.ofReal (1 / (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 3)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have e2 : ENNReal.ofReal ((m : ℝ) * ((m : ℝ) * (1 / (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 3)))) =
      (m : ENNReal) * ENNReal.ofReal ((m : ℝ) * (1 / (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 3))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [e2]

end CorreaIIDTightAux


open MeasureTheory CorreaThreshold.Tight

namespace CorreaIIDTightAux

noncomputable def Ireal (n : ℕ) (a : ℕ) : ℝ :=
  (1 - (1 - 1 / (n : ℝ)) ^ ((a - 1) + 1)) / ((1 / (n : ℝ)) * (((a - 1 : ℕ) : ℝ) + 1))

lemma base_nonneg (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 1 - 1 / (n : ℝ) + t / n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : 1 / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have : 0 ≤ t / (n : ℝ) := by positivity
  linarith

lemma Ireal_nonneg (n : ℕ) (hn : 2 ≤ n) (a : ℕ) : 0 ≤ Ireal n a := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold Ireal
  apply div_nonneg
  · have h0 : 0 ≤ 1 - 1 / (n : ℝ) := by have := base_nonneg n hn 0 le_rfl; simpa using this
    have h1 : 1 - 1 / (n : ℝ) ≤ 1 := by have : 0 ≤ 1 / (n : ℝ) := by positivity
                                        linarith
    have := pow_le_one₀ h0 h1 (n := (a - 1) + 1)
    linarith
  · positivity

lemma lint_t_pow (n : ℕ) (hn : 2 ≤ n) (a : ℕ) :
    ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (1 - 1 / (n : ℝ) + t / n) ^ (a - 1) =
      ENNReal.ofReal (Ireal n a) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : ∀ t : ℝ, t ∈ Set.Ioc (0:ℝ) 1 → ENNReal.ofReal (1 - 1 / (n : ℝ) + t / n) ^ (a - 1) =
      ENNReal.ofReal ((1 - 1 / (n : ℝ) + t / n) ^ (a - 1)) :=
    fun t ht => (ENNReal.ofReal_pow (base_nonneg n hn t ht.1.le) _).symm
  rw [setLIntegral_congr_fun measurableSet_Ioc this]
  rw [lint_Ioc_ofReal (fun t => (1 - 1 / (n : ℝ) + t / n) ^ (a - 1)) (by fun_prop)
    (fun t ht _ => pow_nonneg (base_nonneg n hn t ht) _)]
  congr 1
  have hp : (0:ℝ) < 1 / n := by positivity
  rw [show (fun t : ℝ => (1 - 1 / (n : ℝ) + t / n) ^ (a - 1)) =
      fun t => ((1 - 1 / (n : ℝ)) + (1 / n) * t) ^ (a - 1) by funext t; ring_nf]
  rw [integral_lin_pow (1 / n) hp (a - 1)]
  rfl

lemma lint_B1_le (n : ℕ) [Fact (2 ≤ n)] (m : ℕ) (A : Finset (Fin m)) :
    ∫⁻ x, B1 n A x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) ≤
      ENNReal.ofReal ((m : ℝ) * (1 / (n : ℝ) ^ 3 * (1 + hi n * Ireal n A.card))) := by
  classical
  have hn : 2 ≤ n := Fact.out
  have hhi0 : 0 ≤ hi n := by have := hi_gt n hn; linarith [(by positivity : (0:ℝ) ≤ n)]
  have hI := Ireal_nonneg n hn A.card
  unfold B1
  have hmeas : ∀ i : Fin m, Measurable (fun x : Fin m → ℝ => ind n (x i) +
      ENNReal.ofReal (hi n) * ∫⁻ t in Set.Ioc (0:ℝ) 1, Tt n A i t x) := fun i =>
    ((ind_meas n).comp (measurable_pi_apply i)).add ((G_meas n A i).const_mul _)
  rw [lintegral_finsetSum _ (fun i _ => hmeas i)]
  have key : ∀ i : Fin m, ∫⁻ x, (ind n (x i) +
      ENNReal.ofReal (hi n) * ∫⁻ t in Set.Ioc (0:ℝ) 1, Tt n A i t x)
      ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 3 * (1 + hi n * Ireal n A.card)) := by
    intro i
    rw [lintegral_add_left (show Measurable (fun x : Fin m → ℝ => ind n (x i)) from
      (ind_meas n).comp (measurable_pi_apply i)), lint_ind,
      lintegral_const_mul _ (G_meas n A i)]
    rw [lintegral_lintegral_swap (f := fun x t => Tt n A i t x) (Tt_meas2 n A i).aemeasurable]
    have h2 : ∫⁻ t in Set.Ioc (0:ℝ) 1, ∫⁻ x, Tt n A i t x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m)
        ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (1 / (n : ℝ) ^ 3) *
          ENNReal.ofReal (1 - 1 / (n : ℝ) + t / n) ^ (A.card - 1) := by
      apply setLIntegral_mono
      · fun_prop
      · intro t ht
        exact lint_Tt_le n A i t ht.1.le ht.2
    rw [lintegral_const_mul _ (show Measurable (fun t : ℝ =>
      ENNReal.ofReal (1 - 1 / (n : ℝ) + t / n) ^ (A.card - 1)) by fun_prop),
      lint_t_pow n hn] at h2
    calc ENNReal.ofReal (1 / (n : ℝ) ^ 3) + ENNReal.ofReal (hi n) *
          ∫⁻ t in Set.Ioc (0:ℝ) 1, ∫⁻ x, Tt n A i t x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m)
        ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 3) + ENNReal.ofReal (hi n) *
          (ENNReal.ofReal (1 / (n : ℝ) ^ 3) * ENNReal.ofReal (Ireal n A.card)) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hhi0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
  refine (Finset.sum_le_card_nsmul _ _ _ (fun i _ => key i)).trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e2 : ENNReal.ofReal ((m : ℝ) * (1 / (n : ℝ) ^ 3 * (1 + hi n * Ireal n A.card))) =
      (m : ENNReal) * ENNReal.ofReal (1 / (n : ℝ) ^ 3 * (1 + hi n * Ireal n A.card)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [e2]

lemma lint_B0 (n : ℕ) [Fact (2 ≤ n)] (m : ℕ) (A : Finset (Fin m)) :
    ∫⁻ x, B0 A x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) =
      ENNReal.ofReal (1 - (1 - 1 / (n : ℝ)) ^ A.card) := lint_ind1 n A

noncomputable def Vreal (n : ℕ) (a : ℕ) : ℝ :=
  (1 - (1 - 1 / (n : ℝ)) ^ a) + ((n : ℝ) ^ 2) * (1 / (n : ℝ) ^ 3 * (1 + hi n * Ireal n a)) +
    hi n * (((n : ℝ) ^ 2) * (((n : ℝ) ^ 2) * (1 / (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 3))))

lemma value_le (n : ℕ) (hn : 2 ≤ n) (τ : Fin (n ^ 2) → ENNReal) :
    value n τ ≤ ENNReal.ofReal (Vreal n (Aset τ).card) := by
  have : Fact (2 ≤ n) := ⟨hn⟩
  have hhi0 : 0 ≤ hi n := by have := hi_gt n hn; linarith [(by positivity : (0:ℝ) ≤ n)]
  have hI := Ireal_nonneg n hn (Aset τ).card
  have hq : 0 ≤ 1 - (1 - 1 / (n : ℝ)) ^ (Aset τ).card := by
    have h0 : 0 ≤ 1 - 1 / (n : ℝ) := by have := base_nonneg n hn 0 le_rfl; simpa using this
    have h1 : 1 - 1 / (n : ℝ) ≤ 1 := by have : 0 ≤ 1 / (n : ℝ) := by positivity
                                        linarith
    have := pow_le_one₀ h0 h1 (n := (Aset τ).card)
    linarith
  unfold value
  calc ∫⁻ x, ENNReal.ofReal (ratioS τ x) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2))
      ≤ ∫⁻ x, (B0 (Aset τ) x + B1 n (Aset τ) x + B2 n x)
          ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_support n (n ^ 2)] with x hx
        exact pointwise n hn τ x hx
    _ = ∫⁻ x, B0 (Aset τ) x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2)) +
        ∫⁻ x, B1 n (Aset τ) x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2)) +
        ∫⁻ x, B2 n x ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2)) := by
        rw [lintegral_add_right _ (B2_meas n _), lintegral_add_left (B0_meas _)]
    _ ≤ _ := by
        rw [lint_B0]
        refine (add_le_add (add_le_add le_rfl (lint_B1_le n _ _)) (lint_B2_le n _)).trans
          (le_of_eq ?_)
        rw [← ENNReal.ofReal_add hq (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        unfold Vreal
        push_cast
        rfl

end CorreaIIDTightAux


open MeasureTheory CorreaThreshold.Tight

namespace CorreaIIDTightAux

/-! ### prophet lower bound -/

open Classical in
noncomputable def phiv (v : ℝ) (y : ℝ) : ENNReal := if y = v then 0 else 1

lemma phiv_meas (v : ℝ) : Measurable (phiv v) := by
  unfold phiv
  exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const

lemma lint_one_sub_prod (n : ℕ) [Fact (2 ≤ n)] (m : ℕ) (v : ℝ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : ∫⁻ y, phiv v y ∂(lawN n) = ENNReal.ofReal r) :
    ∫⁻ x, (1 - ∏ j, phiv v (x j)) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) =
      ENNReal.ofReal (1 - r ^ m) := by
  have hmeas : Measurable (fun x : Fin m → ℝ => ∏ j, phiv v (x j)) :=
    Finset.measurable_prod _ (fun j _ => (phiv_meas v).comp (measurable_pi_apply j))
  have hprod : ∫⁻ x, ∏ j, phiv v (x j) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) m) =
      ENNReal.ofReal r ^ m := by
    rw [lint_pi_prod n m (fun _ => phiv v) (fun _ => phiv_meas v), hv, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [lintegral_sub (f := fun _ => (1 : ENNReal)) hmeas]
  · rw [hprod, lintegral_const, measure_univ, mul_one]
    rw [← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (pow_nonneg hr0 _)]
  · rw [hprod]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · filter_upwards with x
    apply Finset.prod_le_one' (fun j _ => ?_)
    unfold phiv; split_ifs <;> simp

lemma prod_phiv_eq_zero {m : ℕ} (v : ℝ) (x : Fin m → ℝ) (j : Fin m) (hj : x j = v) :
    ∏ k, phiv v (x k) = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ j) (by simp [phiv, hj])

lemma prod_phiv_eq_one {m : ℕ} (v : ℝ) (x : Fin m → ℝ) (h : ∀ j, x j ≠ v) :
    ∏ k, phiv v (x k) = 1 :=
  Finset.prod_eq_one (fun j _ => by simp [phiv, h j])

lemma prophet_pointwise (n : ℕ) (hn : 2 ≤ n) (x : Fin (n ^ 2) → ℝ) [NeZero (n ^ 2)] :
    (1 - ∏ j, phiv 1 (x j)) + ENNReal.ofReal (hi n - 1) * (1 - ∏ j, phiv (hi n) (x j)) ≤
      ENNReal.ofReal (SamuelCahnProphet.IID.maxV x) := by
  have hhi1 : (1:ℝ) < hi n := by
    have := hi_gt n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmax : ∀ j, x j ≤ SamuelCahnProphet.IID.maxV x := fun j =>
    Finset.le_sup' x (Finset.mem_univ j)
  have hfirst : 1 - ∏ j, phiv 1 (x j) ≤ 1 := tsub_le_self
  by_cases hH : ∃ j, x j = hi n
  · obtain ⟨j, hj⟩ := hH
    rw [prod_phiv_eq_zero (hi n) x j hj, tsub_zero, mul_one]
    calc (1 - ∏ j, phiv 1 (x j)) + ENNReal.ofReal (hi n - 1) ≤ 1 + ENNReal.ofReal (hi n - 1) := by
          gcongr
      _ = ENNReal.ofReal (hi n) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]; congr 1; ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hj ▸ hmax j)
  · push Not at hH
    rw [prod_phiv_eq_one (hi n) x hH, tsub_self, mul_zero, add_zero]
    by_cases h1 : ∃ j, x j = 1
    · obtain ⟨j, hj⟩ := h1
      calc 1 - ∏ j, phiv 1 (x j) ≤ 1 := hfirst
        _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hj ▸ hmax j)
    · push Not at h1
      rw [prod_phiv_eq_one 1 x h1, tsub_self]
      exact zero_le

noncomputable def Preal (n : ℕ) : ℝ :=
  (1 - (1 - 1 / (n : ℝ)) ^ (n ^ 2)) + (hi n - 1) * (1 - (1 - 1 / (n : ℝ) ^ 3) ^ (n ^ 2))

lemma prophet_ge (n : ℕ) (hn : 2 ≤ n) : ENNReal.ofReal (Preal n) ≤ prophet n := by
  have : Fact (2 ≤ n) := ⟨hn⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hhi1 : (1:ℝ) < hi n := by have := hi_gt n hn; linarith
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero (n ^ 2) := ⟨by positivity⟩
  have hp : 1 / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hp3 : 1 / (n : ℝ) ^ 3 ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (8:ℝ) ≤ (n:ℝ)^3 := by
      have := pow_le_pow_left₀ (by norm_num) hn' 3; norm_num at this; linarith
    linarith
  have hp0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hp30 : 0 ≤ 1 / (n : ℝ) ^ 3 := by positivity
  have h3 : 0 ≤ 1 - 1 / (n : ℝ) - 1 / (n : ℝ) ^ 3 := by linarith
  have hv1 : ∫⁻ y, phiv 1 y ∂(lawN n) = ENNReal.ofReal (1 - 1 / (n : ℝ)) := by
    rw [lint_lawN]
    have : hi n ≠ 1 := hi_ne_one n hn
    simp only [phiv, this, if_false, if_true, (zero_ne_one : (0:ℝ) ≠ 1), mul_one, mul_zero,
      add_zero]
    rw [← ENNReal.ofReal_add hp30 h3]; congr 1; ring
  have hvh : ∫⁻ y, phiv (hi n) y ∂(lawN n) = ENNReal.ofReal (1 - 1 / (n : ℝ) ^ 3) := by
    rw [lint_lawN]
    have h1 : (1:ℝ) ≠ hi n := (hi_ne_one n hn).symm
    have h0 : (0:ℝ) ≠ hi n := (hi_ne_zero n hn).symm
    simp only [phiv, h1, h0, if_false, if_true, mul_one, mul_zero, zero_add]
    rw [← ENNReal.ofReal_add hp0 h3]; congr 1; ring
  unfold prophet
  rw [dif_neg hn0]
  unfold SamuelCahnProphet.IID.Emax
  have hmeas1 : Measurable (fun x : Fin (n ^ 2) → ℝ => 1 - ∏ j, phiv 1 (x j)) :=
    measurable_const.sub
      (Finset.measurable_prod _ (fun j _ => (phiv_meas 1).comp (measurable_pi_apply j)))
  have hmeas2 : Measurable (fun x : Fin (n ^ 2) → ℝ => 1 - ∏ j, phiv (hi n) (x j)) :=
    measurable_const.sub
      (Finset.measurable_prod _ (fun j _ => (phiv_meas (hi n)).comp (measurable_pi_apply j)))
  calc ENNReal.ofReal (Preal n)
      = ∫⁻ x, ((1 - ∏ j, phiv 1 (x j)) + ENNReal.ofReal (hi n - 1) *
          (1 - ∏ j, phiv (hi n) (x j))) ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2)) := by
        rw [lintegral_add_left hmeas1, lintegral_const_mul _ hmeas2,
          lint_one_sub_prod n _ 1 _ (by linarith) (by linarith) hv1,
          lint_one_sub_prod n _ (hi n) _ (by linarith) (by linarith) hvh]
        have hq1 : 0 ≤ 1 - (1 - 1 / (n : ℝ)) ^ (n ^ 2) := by
          have := pow_le_one₀ (n := n ^ 2) (by linarith : (0:ℝ) ≤ 1 - 1 / (n : ℝ)) (by linarith)
          linarith
        have hq2 : 0 ≤ 1 - (1 - 1 / (n : ℝ) ^ 3) ^ (n ^ 2) := by
          have := pow_le_one₀ (n := n ^ 2) (by linarith : (0:ℝ) ≤ 1 - 1 / (n : ℝ) ^ 3) (by linarith)
          linarith
        unfold Preal
        rw [ENNReal.ofReal_add hq1 (mul_nonneg (by linarith) hq2), ENNReal.ofReal_mul (by linarith)]
    _ ≤ _ := lintegral_mono (fun x => prophet_pointwise n hn x)

end CorreaIIDTightAux


open MeasureTheory CorreaThreshold.Tight

namespace CorreaIIDTightAux

/-- `(1 - u)^m ≤ 1 / (1 + m u)` for `0 ≤ u ≤ 1`. -/
lemma one_sub_pow_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (m : ℕ) :
    (1 - u) ^ m ≤ 1 / (1 + m * u) := by
  have hpos : 0 < 1 + (m : ℝ) * u := by positivity
  rw [le_div_iff₀ hpos]
  have h1 : 1 + (m : ℝ) * u ≤ (1 + u) ^ m := one_add_mul_le_pow (by linarith) m
  have h2 : (1 - u) ^ m * (1 + u) ^ m ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : 0 ≤ (1 - u) ^ m := pow_nonneg (by linarith) m
  nlinarith

lemma Preal_ge (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) - 1 + hi n) / ((n : ℝ) + 1) ≤ Preal n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hhi1 : (1:ℝ) < hi n := by have := hi_gt n hn; linarith
  have hp : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hp3 : 1 / (n : ℝ) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by linarith)
  have hA := one_sub_pow_le (1 / (n : ℝ)) (by positivity) hp (n ^ 2)
  have hB := one_sub_pow_le (1 / (n : ℝ) ^ 3) (by positivity) hp3 (n ^ 2)
  have eA : 1 / (1 + ((n ^ 2 : ℕ) : ℝ) * (1 / (n : ℝ))) = 1 / ((n : ℝ) + 1) := by
    push_cast; field_simp; ring
  have eB : 1 / (1 + ((n ^ 2 : ℕ) : ℝ) * (1 / (n : ℝ) ^ 3)) = (n : ℝ) / ((n : ℝ) + 1) := by
    push_cast; field_simp
  rw [eA] at hA
  rw [eB] at hB
  unfold Preal
  have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have : ((n : ℝ) - 1 + hi n) / ((n : ℝ) + 1) =
      (1 - 1 / ((n : ℝ) + 1)) + (hi n - 1) * (1 - (n : ℝ) / ((n : ℝ) + 1)) := by
    field_simp; ring
  rw [this]
  have := mul_le_mul_of_nonneg_left (by linarith : 1 - (n : ℝ) / ((n : ℝ) + 1) ≤
    1 - (1 - 1 / (n : ℝ) ^ 3) ^ (n ^ 2)) (by linarith : (0:ℝ) ≤ hi n - 1)
  linarith

lemma e_facts : 2.718281828 < Real.exp 1 ∧ Real.exp 1 < 2.7182818286 := by
  constructor
  · linarith [Real.exp_one_gt_d9]
  · exact Real.exp_one_lt_d9

/-- `q + q n/(a c) ≤ n/(n-1) L` for `a ≥ 1`. -/
lemma key_real (n : ℕ) (hn : 2 ≤ n) (a : ℕ) (ha : 1 ≤ a) :
    (1 - (1 - 1 / (n : ℝ)) ^ a) * (1 + (n : ℝ) / (a * (Real.exp 1 - 2))) ≤
      (n : ℝ) / ((n : ℝ) - 1) *
        ((1 - Real.exp (-1)) * (1 / (Real.exp 1 - 2) + 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hc : 0 < Real.exp 1 - 2 := c_pos
  set c := Real.exp 1 - 2 with hcdef
  set u := 1 / (n : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u < 1 := by rw [hu, div_lt_one (by positivity)]; linarith
  set ℓ := -Real.log (1 - u) with hℓ
  have hlog1 : Real.log (1 - u) ≤ -u := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 - u); linarith
  have hlog2 : -(1 / ((n : ℝ) - 1)) ≤ Real.log (1 - u) := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0:ℝ) < 1 - u)
    have e : 1 - (1 - u)⁻¹ = -(1 / ((n : ℝ) - 1)) := by
      rw [hu]; field_simp
      have : (n : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    linarith
  have hℓpos : 0 < ℓ := by linarith
  have hℓle : ℓ * ((n : ℝ) - 1) ≤ 1 := by
    have : ℓ ≤ 1 / ((n : ℝ) - 1) := by linarith
    rw [le_div_iff₀ (by linarith)] at this; linarith
  set y := (a : ℝ) * ℓ with hy
  have hypos : 0 < y := by positivity
  have hpow : (1 - u) ^ a = Real.exp (-y) := by
    rw [hy, hℓ, neg_mul_eq_mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log (by linarith)]
  rw [hpow]
  have hf := prop_A_3 y hypos
  have hq0 : 0 ≤ 1 - Real.exp (-y) := by
    have := Real.exp_le_one_iff.2 (by linarith : -y ≤ 0); linarith
  have hfac : 1 + (n : ℝ) / (a * c) ≤ (n : ℝ) / ((n : ℝ) - 1) * (1 / (y * c) + 1) := by
    have hd : 0 < (n : ℝ) - 1 := by linarith
    have h1 : (1:ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) := by rw [le_div_iff₀ hd]; linarith
    have h2 : (n : ℝ) / (a * c) ≤ (n : ℝ) / ((n : ℝ) - 1) * (1 / (y * c)) := by
      rw [div_mul_div_comm, mul_one]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [hy]
      have : ((n : ℝ) - 1) * ((a : ℝ) * ℓ * c) = (a : ℝ) * c * (ℓ * ((n : ℝ) - 1)) := by ring
      rw [this]
      have : 0 < (a : ℝ) * c := by positivity
      nlinarith
    nlinarith
  calc (1 - Real.exp (-y)) * (1 + (n : ℝ) / (a * c))
      ≤ (1 - Real.exp (-y)) * ((n : ℝ) / ((n : ℝ) - 1) * (1 / (y * c) + 1)) :=
        mul_le_mul_of_nonneg_left hfac hq0
    _ = (n : ℝ) / ((n : ℝ) - 1) * ((1 - Real.exp (-y)) * (1 / (y * c) + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by
          have : 0 < (n : ℝ) - 1 := by linarith
          positivity)

lemma Vreal_le (n : ℕ) (hn : 2 ≤ n) (a : ℕ) :
    Vreal n a ≤ (n : ℝ) / ((n : ℝ) - 1) * ((1 - Real.exp (-1)) * (1 / (Real.exp 1 - 2) + 1)) +
      1 / (n : ℝ) + 1 / ((n : ℝ) * (Real.exp 1 - 2)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : 0 < Real.exp 1 - 2 := c_pos
  have hnpos : (0 : ℝ) < n := by linarith
  have hV : Vreal n a = (1 - (1 - 1 / (n : ℝ)) ^ a) + Ireal n a / (Real.exp 1 - 2) +
      1 / (n : ℝ) + 1 / ((n : ℝ) * (Real.exp 1 - 2)) := by
    unfold Vreal hi
    field_simp
    ring
  rw [hV]
  suffices h : (1 - (1 - 1 / (n : ℝ)) ^ a) + Ireal n a / (Real.exp 1 - 2) ≤
      (n : ℝ) / ((n : ℝ) - 1) * ((1 - Real.exp (-1)) * (1 / (Real.exp 1 - 2) + 1)) by linarith
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    have hI : Ireal n 0 = 1 := by
      unfold Ireal; simp; field_simp
    rw [hI, pow_zero, sub_self, zero_add]
    obtain ⟨e1, e2⟩ := e_facts
    have hs : 0.632 < 1 - Real.exp (-1) := by
      rw [Real.exp_neg]
      have : (Real.exp 1)⁻¹ < 0.368 := by
        rw [inv_lt_comm₀ (by positivity) (by norm_num)]; norm_num; linarith
      linarith
    have hw : 1 / (Real.exp 1 - 2) ≤ (1 - Real.exp (-1)) * (1 / (Real.exp 1 - 2) + 1) := by
      have hw1 : 1 / (Real.exp 1 - 2) < 1.4 := by
        rw [div_lt_iff₀ hc]; linarith
      have hw0 : 0 < 1 / (Real.exp 1 - 2) := by positivity
      nlinarith
    have hd : 0 < (n : ℝ) - 1 := by linarith
    have h1 : (1:ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) := by rw [le_div_iff₀ hd]; linarith
    have hL0 : 0 ≤ (1 - Real.exp (-1)) * (1 / (Real.exp 1 - 2) + 1) := by
      have : 0 < 1 / (Real.exp 1 - 2) := by positivity
      nlinarith
    nlinarith
  · have hI : Ireal n a = (1 - (1 - 1 / (n : ℝ)) ^ a) * (n : ℝ) / a := by
      unfold Ireal
      rw [Nat.sub_add_cancel hpos, Nat.cast_sub hpos]
      push_cast
      rw [sub_add_cancel]
      have : (a : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hI]
    have := key_real n hn a hpos
    have e : (1 - (1 - 1 / (n : ℝ)) ^ a) + (1 - (1 - 1 / (n : ℝ)) ^ a) * (n : ℝ) / a /
        (Real.exp 1 - 2) = (1 - (1 - 1 / (n : ℝ)) ^ a) * (1 + (n : ℝ) / (a * (Real.exp 1 - 2))) := by
      have : (a : ℝ) ≠ 0 := by positivity
      field_simp
    rw [e]; exact this

end CorreaIIDTightAux


open MeasureTheory CorreaThreshold.Tight

namespace CorreaIIDTightAux

lemma prophet_le (n : ℕ) (hn : 2 ≤ n) :
    prophet n ≤ ENNReal.ofReal ((Real.exp 1 - 1) / (Real.exp 1 - 2)) := by
  have : Fact (2 ≤ n) := ⟨hn⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hhi1 : (1:ℝ) < hi n := by have := hi_gt n hn; linarith
  have hc : 0 < Real.exp 1 - 2 := c_pos
  have hn0 : n ≠ 0 := by omega
  have : NeZero (n ^ 2) := ⟨by positivity⟩
  unfold prophet
  rw [dif_neg hn0]
  unfold SamuelCahnProphet.IID.Emax
  have hmeas : Measurable (fun x : Fin (n ^ 2) → ℝ => ∑ i, ind n (x i)) :=
    Finset.measurable_sum _ (fun i _ => (ind_meas n).comp (measurable_pi_apply i))
  calc ∫⁻ x, ENNReal.ofReal (SamuelCahnProphet.IID.maxV x)
        ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2))
      ≤ ∫⁻ x, (1 + ENNReal.ofReal (hi n) * ∑ i, ind n (x i))
        ∂(SamuelCahnProphet.IID.iidLaw (lawN n) (n ^ 2)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_support n (n ^ 2)] with x hx
        obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (n ^ 2))) x
        unfold SamuelCahnProphet.IID.maxV
        rw [hj]
        rcases hx j with h | h | h
        · rw [h, ENNReal.ofReal_zero]; exact zero_le
        · rw [h, ENNReal.ofReal_one]; exact le_self_add
        · have : (1 : ENNReal) ≤ ∑ i, ind n (x i) := by
            have h1 : ind n (x j) = 1 := by simp [ind, h]
            rw [← h1]
            exact Finset.single_le_sum (f := fun i => ind n (x i)) (fun _ _ => zero_le)
              (Finset.mem_univ j)
          rw [h]
          calc ENNReal.ofReal (hi n) = ENNReal.ofReal (hi n) * 1 := (mul_one _).symm
            _ ≤ ENNReal.ofReal (hi n) * ∑ i, ind n (x i) := by gcongr
            _ ≤ _ := le_add_left le_rfl
    _ = ENNReal.ofReal ((Real.exp 1 - 1) / (Real.exp 1 - 2)) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hmeas,
          lintegral_finsetSum _ (fun i _ => (show Measurable (fun x : Fin (n ^ 2) → ℝ => ind n (x i))
            from (ind_meas n).comp (measurable_pi_apply i)))]
        simp_rw [lint_ind]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (by positivity)]
        congr 1
        unfold hi
        push_cast
        field_simp
        ring

end CorreaIIDTightAux

open CorreaIIDTightAux in
theorem solution :
    Filter.Tendsto CorreaThreshold.Tight.prophet Filter.atTop
      (nhds (ENNReal.ofReal ((Real.exp 1 - 1) / (Real.exp 1 - 2)))) := by
  have hc : 0 < Real.exp 1 - 2 := c_pos
  have hlow : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (((n : ℝ) - 1 + hi n) / ((n : ℝ) + 1)))
      Filter.atTop (nhds (ENNReal.ofReal ((Real.exp 1 - 1) / (Real.exp 1 - 2)))) := by
    apply ENNReal.tendsto_ofReal
    have e : ∀ n : ℕ, ((n : ℝ) - 1 + hi n) / ((n : ℝ) + 1) =
        (Real.exp 1 - 1) / (Real.exp 1 - 2) -
          ((Real.exp 1 - 1) / (Real.exp 1 - 2) + 1) * (1 / ((n : ℝ) + 1)) := by
      intro n
      unfold hi
      have : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    simp_rw [e]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul
      ((Real.exp 1 - 1) / (Real.exp 1 - 2) + 1)
    rw [mul_zero] at this
    simpa using (tendsto_const_nhds (x := (Real.exp 1 - 1) / (Real.exp 1 - 2))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact (ENNReal.ofReal_le_ofReal (Preal_ge n hn)).trans (prophet_ge n hn)
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact prophet_le n hn
