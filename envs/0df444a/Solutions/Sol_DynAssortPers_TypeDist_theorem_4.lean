-- Prove2me | solution 1 for DynAssortPers.TypeDist.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:50:57.559066+00:00
-- url     : https://prove2.me/submissions/de0fd996-81f8-4c13-8d99-dda80af40703

import Mathlib
import Definitions.Def_DynAssortPers_TypeDist_IIDSampling
import Definitions.Def_DynAssortPers_TypeDist_Estimator

namespace RRAux_DAP

open MeasureTheory ProbabilityTheory Finset DynAssortPers.TypeDist
open scoped ENNReal
open Classical

noncomputable def nu {m : ℕ} (μ : Fin m → ℝ) : Measure (Fin m) :=
  ∑ j, ENNReal.ofReal (μ j) • Measure.dirac j

lemma nu_apply {m : ℕ} (μ : Fin m → ℝ) (S : Set (Fin m)) :
    nu μ S = ∑ j, ENNReal.ofReal (μ j) * S.indicator 1 j := by
  simp [nu]

lemma nu_singleton {m : ℕ} (μ : Fin m → ℝ) (i : Fin m) : nu μ {i} = ENNReal.ofReal (μ i) := by
  rw [nu_apply]
  simp [Set.indicator_apply]

lemma nu_prob {m : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m)) :
    IsProbabilityMeasure (nu μ) := by
  constructor
  rw [nu_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hμ.1 j), hμ.2, ENNReal.ofReal_one]

lemma bridge {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (E : (Fin N → Fin m) → Prop) :
    (Measure.pi (fun _ : Fin N => nu μ)).real {x | E x} = iidProb μ E := by
  classical
  haveI := nu_prob μ hμ
  have hs : {x | E x} = ((univ.filter E : Finset (Fin N → Fin m)) : Set (Fin N → Fin m)) := by
    ext x; simp
  rw [measureReal_def, hs, ← sum_measure_singleton, iidProb]
  rw [ENNReal.toReal_sum (fun x _ => measure_ne_top _ _)]
  apply Finset.sum_congr (by congr 1)  -- decidable instance issue maybe
  intro x _
  rw [Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro t _
  rw [nu_singleton, ENNReal.toReal_ofReal (hμ.1 _)]

lemma integral_coord {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (φ : Fin m → ℝ) (t : Fin N) :
    ∫ x, φ (x t) ∂(Measure.pi (fun _ : Fin N => nu μ)) = ∑ j, μ j * φ j := by
  haveI := nu_prob μ hμ
  have hmp := measurePreserving_eval (fun _ : Fin N => nu μ) t
  have hm : ∫ y, φ y ∂(nu μ) = ∫ x, φ (x t) ∂(Measure.pi (fun _ : Fin N => nu μ)) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable
      ((Measurable.of_discrete (f := φ)).aestronglyMeasurable)
  rw [← hm, integral_fintype (Integrable.of_finite (μ := nu μ) (f := φ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [measureReal_def, nu_singleton, ENNReal.toReal_ofReal (hμ.1 _), smul_eq_mul]

lemma iid_eq {m N : ℕ} (μ : Fin m → ℝ) (E : (Fin N → Fin m) → Prop) :
    iidProb μ E = ∑ x, if E x then ∏ t, μ (x t) else 0 := by
  classical
  simp only [iidProb]
  rw [Finset.sum_filter]

lemma iid_total {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m)) :
    ∑ x : Fin N → Fin m, ∏ t, μ (x t) = 1 := by
  have := (Finset.prod_univ_sum (fun (_ : Fin N) => (univ : Finset (Fin m)))
    (fun _ j => μ j)).symm
  rw [Fintype.piFinset_univ] at this
  rw [this, hμ.2]; simp

lemma iid_compl {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (E : (Fin N → Fin m) → Prop) : iidProb μ E + iidProb μ (fun x => ¬ E x) = 1 := by
  classical
  rw [iid_eq, iid_eq, ← Finset.sum_add_distrib, ← iid_total μ hμ]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x <;> simp [h]

lemma iid_mono {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (E F : (Fin N → Fin m) → Prop) (h : ∀ x, E x → F x) : iidProb μ E ≤ iidProb μ F := by
  classical
  rw [iid_eq, iid_eq]
  apply Finset.sum_le_sum
  intro x _
  have hw : 0 ≤ ∏ t, μ (x t) := Finset.prod_nonneg (fun t _ => hμ.1 _)
  by_cases hE : E x
  · simp [hE, h x hE]
  · simp only [hE, if_false]; split_ifs <;> linarith

lemma iid_union {m N : ℕ} {ι : Type*} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (s : Finset ι) (E : ι → (Fin N → Fin m) → Prop) :
    iidProb μ (fun x => ∃ k ∈ s, E k x) ≤ ∑ k ∈ s, iidProb μ (E k) := by
  classical
  simp only [iid_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hw : 0 ≤ ∏ t, μ (x t) := Finset.prod_nonneg (fun t _ => hμ.1 _)
  have hnn : ∀ k ∈ s, 0 ≤ (if E k x then ∏ t, μ (x t) else 0) := by
    intro k _; split_ifs <;> linarith
  split_ifs with hex
  · obtain ⟨k, hk, hEk⟩ := hex
    have := Finset.single_le_sum hnn hk
    simp only [hEk, if_true] at this
    exact this
  · exact Finset.sum_nonneg hnn

lemma lq_le_l1 {m : ℕ} (q : ℝ≥0∞) (hq : 1 ≤ q) (v : Fin m → ℝ) :
    lqNorm q v ≤ ∑ i, |v i| := by
  haveI : Fact (1 ≤ q) := ⟨hq⟩
  unfold lqNorm
  have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  conv_lhs => rw [hv, WithLp.toLp_sum]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro i _
  rw [PiLp.norm_toLp_single, Real.norm_eq_abs]

lemma lq_le_sup {m : ℕ} (q : ℝ≥0∞) (hq : 1 ≤ q) (v : Fin m → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ i, |v i| ≤ δ) : lqNorm q v ≤ (m : ℝ) ^ invQ q * δ := by
  haveI : Fact (1 ≤ q) := ⟨hq⟩
  unfold lqNorm
  have h0 : WithLp.toLp q (0 : Fin m → ℝ) = 0 := rfl
  have hsup : ‖v‖ ≤ δ := (pi_norm_le_iff_of_nonneg hδ).2 (fun i => by rw [Real.norm_eq_abs]; exact hv i)
  have hK : (((Fintype.card (Fin m) : NNReal) ^ (1 / q).toReal : NNReal) : ℝ) = (m : ℝ) ^ invQ q := by
    rw [NNReal.coe_rpow, Fintype.card_fin, NNReal.coe_natCast]
    congr 1
    unfold invQ
    split_ifs with h
    · simp [h]
    · rw [one_div, ENNReal.toReal_inv, one_div]
  have hL := (PiLp.lipschitzWith_toLp q (fun _ : Fin m => ℝ)).dist_le_mul v 0
  rw [h0, dist_zero_right, dist_zero_right, hK] at hL
  calc _ ≤ _ := hL
    _ ≤ _ := mul_le_mul_of_nonneg_left hsup (by positivity)


lemma hoeff {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m)) (φ : Fin m → ℝ)
    (a b : ℝ) (hab : ∀ j, φ j ∈ Set.Icc a b) (ε : ℝ) (hε : 0 ≤ ε) :
    iidProb μ (fun x : Fin N → Fin m => ε ≤ ∑ t, (φ (x t) - ∑ j, μ j * φ j)) ≤
      Real.exp (-ε ^ 2 / (2 * (N * ((b - a) / 2) ^ 2))) := by
  haveI := nu_prob μ hμ
  rw [← bridge μ hμ]
  have hind : iIndepFun (fun (t : Fin N) (x : Fin N → Fin m) => φ (x t) - ∑ j, μ j * φ j)
      (Measure.pi (fun _ : Fin N => nu μ)) :=
    iIndepFun_pi (X := fun (_ : Fin N) (j : Fin m) => φ j - ∑ j, μ j * φ j)
      (fun _ => Measurable.of_discrete.aemeasurable)
  have hsub : ∀ t ∈ (univ : Finset (Fin N)), HasSubgaussianMGF
      (fun x : Fin N → Fin m => φ (x t) - ∑ j, μ j * φ j) ((‖b - a‖₊ / 2) ^ 2)
      (Measure.pi (fun _ : Fin N => nu μ)) := by
    intro t _
    have := hasSubgaussianMGF_of_mem_Icc (μ := Measure.pi (fun _ : Fin N => nu μ))
      (X := fun x : Fin N → Fin m => φ (x t)) (a := a) (b := b)
      Measurable.of_discrete.aemeasurable (ae_of_all _ (fun x => hab (x t)))
    rwa [integral_coord μ hμ φ t] at this
  have H := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub hε
  refine H.trans (le_of_eq ?_)
  congr 3
  push_cast
  simp [Finset.sum_const, div_pow, sq_abs]

lemma sumL {m N : ℕ} (μ : Fin m → ℝ) (hN : 0 < N) (g : Fin m → ℝ) (x : Fin N → Fin m) :
    ∑ t, (g (x t) - ∑ j, μ j * g j) = N * ∑ j, g j * (muHat x j - μ j) := by
  have h1 : ∑ t, g (x t) = ∑ j, ((univ.filter (fun t => x t = j)).card : ℝ) * g j := by
    rw [← Finset.sum_fiberwise univ x (fun t => g (x t))]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.1 ht).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_sub_distrib, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  simp only [muHat, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  have hN' : (N:ℝ) ≠ 0 := by positivity
  congr 1
  · apply Finset.sum_congr rfl; intro j _; field_simp
  · apply Finset.sum_congr rfl; intro j _; ring


lemma m_pos {m : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m)) : 1 ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · have := hμ.2; simp at this
  · exact h

lemma fam_bound {m N : ℕ} {K : Type*} [Fintype K] (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (hN : 0 < N) (φ : K → Fin m → ℝ) (a : K → ℝ) (w : ℝ)
    (hab : ∀ k j, φ k j ∈ Set.Icc (a k) (a k + w)) (ε : ℝ) (hε : 0 ≤ ε) :
    iidProb μ (fun x : Fin N → Fin m => ∃ k ∈ (univ : Finset K),
        ε ≤ ∑ j, φ k j * (muHat x j - μ j)) ≤
      Fintype.card K * Real.exp (-((N:ℝ) * ε) ^ 2 / (2 * (N * (w / 2) ^ 2))) := by
  refine (iid_union μ hμ univ _).trans ?_
  calc ∑ k ∈ (univ : Finset K), iidProb μ (fun x : Fin N → Fin m =>
          ε ≤ ∑ j, φ k j * (muHat x j - μ j))
        ≤ ∑ k : K, Real.exp (-((N:ℝ) * ε) ^ 2 / (2 * (N * (w / 2) ^ 2))) := by
          apply Finset.sum_le_sum
          intro k _
          have hb := hoeff (N := N) μ hμ (φ k) (a k) (a k + w) (hab k) (N * ε) (by positivity)
          rw [add_sub_cancel_left] at hb
          refine (iid_mono μ hμ _ _ (fun x hx => ?_)).trans hb
          rw [sumL μ hN]
          exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma finish {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (bad G : (Fin N → Fin m) → Prop) (hG : ∀ x, ¬ bad x → G x) (e : ℝ)
    (hb : iidProb μ bad ≤ e) : 1 - e ≤ iidProb μ G := by
  have h1 := iid_compl μ hμ bad
  have h2 := iid_mono μ hμ _ _ hG
  linarith

lemma num2 (m N : ℕ) (hm : 1 ≤ m) (hN : 0 < N) (τ : ℝ) (hτ : 0 ≤ τ) :
    ((Fintype.card (Fin m × Bool) : ℕ) : ℝ) * Real.exp (-((N:ℝ) * (Real.sqrt ((τ + Real.log (2 * m)) / N)
      / Real.sqrt 2)) ^ 2 / (2 * (N * (1 / 2) ^ 2))) = Real.exp (-τ) := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hsq : (Real.sqrt ((τ + Real.log (2 * m)) / N) / Real.sqrt 2) ^ 2
      = (τ + Real.log (2 * m)) / N / 2 := by
    rw [div_pow, Real.sq_sqrt (div_nonneg (by linarith) hNr.le),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [mul_pow, hsq]
  have : -((N:ℝ) ^ 2 * ((τ + Real.log (2 * m)) / N / 2)) / (2 * (N * (1 / 2) ^ 2))
      = -τ - Real.log (2 * m) := by
    field_simp; ring
  rw [this, Real.exp_sub, Real.exp_log (by linarith)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  push_cast
  field_simp

lemma num1 (m N : ℕ) (hN : 0 < N) (τ : ℝ) (hτ : 0 ≤ τ) :
    ((Fintype.card (Fin m → Bool) : ℕ) : ℝ) * Real.exp (-((N:ℝ) * (8 * Real.sqrt ((τ + m) / N))) ^ 2
      / (2 * (N * (2 / 2) ^ 2))) ≤ Real.exp (-τ) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg (by linarith) hNr.le)]
  have : -((N:ℝ) ^ 2 * (8 ^ 2 * ((τ + m) / N))) / (2 * (N * (2 / 2) ^ 2)) = -(32 * (τ + m)) := by
    field_simp; ring
  rw [this]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  push_cast
  have h2 : (2:ℝ) ^ m ≤ Real.exp m := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1:ℝ)]) m
  calc (2:ℝ) ^ m * Real.exp (-(32 * (τ + m))) ≤ Real.exp m * Real.exp (-(32 * (τ + m))) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (m - 32 * (τ + m)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-τ) := Real.exp_le_exp.2 (by linarith)

lemma bound2 {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (hN : 0 < N) (τ : ℝ) (hτ : 0 ≤ τ) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    1 - Real.exp (-τ) ≤ iidProb μ (fun x : Fin N → Fin m =>
        lqNorm q (fun i => muHat x i - μ i)
          ≤ (m : ℝ) ^ invQ q / Real.sqrt 2 * Real.sqrt ((τ + Real.log (2 * m)) / N)) := by
  have hm := m_pos μ hμ
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  set δ := Real.sqrt ((τ + Real.log (2 * m)) / N) / Real.sqrt 2 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  let φ : Fin m × Bool → Fin m → ℝ := fun k j => if j = k.1 then sgn k.2 else 0
  let a : Fin m × Bool → ℝ := fun k => if k.2 then 0 else -1
  have hab : ∀ k j, φ k j ∈ Set.Icc (a k) (a k + 1) := by
    intro k j
    rcases k with ⟨i, b⟩
    cases b <;> by_cases hj : j = i <;> simp [φ, a, hj, sgn]
  have hF := fam_bound (N := N) μ hμ hN φ a 1 hab δ hδ0
  rw [num2 m N hm hN τ hτ] at hF
  refine finish μ hμ _ _ (fun x hx => ?_) _ hF
  have hv : ∀ i, |muHat x i - μ i| ≤ δ := by
    intro i
    have h1 : ¬ δ ≤ ∑ j, φ (i, true) j * (muHat x j - μ j) := fun h => hx ⟨_, mem_univ _, h⟩
    have h2 : ¬ δ ≤ ∑ j, φ (i, false) j * (muHat x j - μ j) := fun h => hx ⟨_, mem_univ _, h⟩
    simp only [φ, ite_mul, zero_mul, Finset.sum_ite_eq', mem_univ, if_true, sgn,
      Bool.false_eq_true, if_false, not_le] at h1 h2
    rw [abs_le]; constructor <;> linarith
  have := lq_le_sup q hq (fun i => muHat x i - μ i) δ hδ0 hv
  rw [hδ] at this
  calc _ ≤ _ := this
    _ = _ := by ring

lemma bound1 {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (hN : 0 < N) (τ : ℝ) (hτ : 0 ≤ τ) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    1 - Real.exp (-τ) ≤ iidProb μ (fun x : Fin N → Fin m =>
        lqNorm q (fun i => muHat x i - μ i) ≤ 8 * Real.sqrt ((τ + m) / N)) := by
  set ε := 8 * Real.sqrt ((τ + m) / N) with hε
  have hε0 : 0 ≤ ε := by positivity
  let φ : (Fin m → Bool) → Fin m → ℝ := fun k j => sgn (k j)
  have hab : ∀ k j, φ k j ∈ Set.Icc (-1) (-1 + 2) := by
    intro k j
    simp only [φ, sgn]
    split_ifs <;> norm_num
  have hF := fam_bound (N := N) μ hμ hN φ (fun _ => -1) 2 hab ε hε0
  have hF' := hF.trans (num1 m N hN τ hτ)
  refine finish μ hμ _ _ (fun x hx => ?_) _ hF'
  have h1 : ¬ ε ≤ ∑ j, φ (fun j => decide (0 ≤ muHat x j - μ j)) j * (muHat x j - μ j) :=
    fun h => hx ⟨_, mem_univ _, h⟩
  have h2 : ∑ j, φ (fun j => decide (0 ≤ muHat x j - μ j)) j * (muHat x j - μ j)
      = ∑ j, |muHat x j - μ j| := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [φ, sgn]
    by_cases hj : 0 ≤ muHat x j - μ j
    · simp [hj, abs_of_nonneg hj]
    · simp [hj, abs_of_neg (not_le.mp hj)]
  rw [h2] at h1
  exact (lq_le_l1 q hq _).trans (le_of_lt (not_le.mp h1))

end RRAux_DAP

open Finset in
open scoped ENNReal in
open DynAssortPers.TypeDist in
theorem solution {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (hN : 0 < N) (τ : ℝ) (hτ : 0 ≤ τ) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    1 - Real.exp (-τ) ≤
      iidProb μ (fun x : Fin N → Fin m =>
        lqNorm q (fun i => muHat x i - μ i)
          ≤ min (8 * Real.sqrt ((τ + m) / N))
                ((m : ℝ) ^ invQ q / Real.sqrt 2 * Real.sqrt ((τ + Real.log (2 * m)) / N))) := by
  rcases le_total (8 * Real.sqrt ((τ + m) / N))
      ((m : ℝ) ^ invQ q / Real.sqrt 2 * Real.sqrt ((τ + Real.log (2 * m)) / N)) with h | h
  · rw [min_eq_left h]
    exact RRAux_DAP.bound1 μ hμ hN τ hτ q hq
  · rw [min_eq_right h]
    exact RRAux_DAP.bound2 μ hμ hN τ hτ q hq

#print axioms solution
