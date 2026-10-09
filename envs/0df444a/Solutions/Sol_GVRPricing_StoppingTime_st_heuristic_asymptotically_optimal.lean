-- Prove2me | solution 1 for GVRPricing.StoppingTime.st_heuristic_asymptotically_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T21:57:18.966012+00:00
-- url     : https://prove2.me/submissions/f39aa912-bbd5-48f6-a929-886673719595

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_DetLP
import Definitions.Def_GVRPricing_StoppingTime_STHeuristic

set_option autoImplicit false

open Filter Topology MeasureTheory ProbabilityTheory

open GVRPricing.StoppingTime in
lemma st5_exp_Iic : expMeasure 1 (Set.Iic 0) = 0 := by
  have := isProbabilityMeasure_expMeasure (r := 1) one_pos
  have h := cdf_expMeasure_eq (r := 1) one_pos 0
  rw [cdf_eq_real] at h
  simp only [le_refl, if_true, mul_zero, neg_zero, Real.exp_zero, sub_self] at h
  exact (measureReal_eq_zero_iff).1 h

lemma st5_exp_sq : Integrable (fun x : ℝ => x ^ 2) (expMeasure 1) := by
  have hE : expMeasure 1 = volume.withDensity (exponentialPDF 1) := rfl
  rw [hE, integrable_withDensity_iff (f := exponentialPDF 1)
    (by exact (measurable_exponentialPDFReal 1).ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (b := 1) (by norm_num) one_pos one_pos
  have h2 : IntegrableOn (fun x : ℝ => 1 * (x ^ 2 * Real.exp (-(1 * x)))) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine IntegrableOn.congr_fun (h.const_mul 1) (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul, Real.rpow_two]
  refine (h2.integrable_indicator measurableSet_Ici).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [exponentialPDF_eq]
  by_cases hx : 0 ≤ x
  · rw [Set.indicator_of_mem (show x ∈ Set.Ici 0 from hx), if_pos hx,
      ENNReal.toReal_ofReal (mul_pos one_pos (Real.exp_pos _)).le]
    ring
  · rw [Set.indicator_of_notMem (show x ∉ Set.Ici 0 from hx), if_neg hx]
    simp

lemma st5_lintegral_ofReal_exp :
    ∫⁻ s, ENNReal.ofReal s ∂(expMeasure 1) = ENNReal.ofReal (1 / 1) := by
  have hr : (0:ℝ) < 1 := one_pos
  have hE : expMeasure 1 = volume.withDensity (exponentialPDF 1) := rfl
  rw [hE, lintegral_withDensity_eq_lintegral_mul (μ := volume) (f := exponentialPDF 1)
    (measurable_exponentialPDFReal 1).ennreal_ofReal ENNReal.measurable_ofReal]
  have h1 : (exponentialPDF 1 * fun s => ENNReal.ofReal s) = Set.indicator (Set.Ioi 0)
      (fun s => ENNReal.ofReal (1 * (s ^ ((2 : ℝ) - 1) * Real.exp (-(1 * s))))) := by
    funext s
    simp only [Pi.mul_apply, exponentialPDF_eq]
    by_cases hs : 0 < s
    · rw [Set.indicator_of_mem (show s ∈ Set.Ioi 0 from hs), if_pos hs.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num
      ring
    · rw [Set.indicator_of_notMem (show s ∉ Set.Ioi 0 from hs)]
      push_neg at hs
      rw [ENNReal.ofReal_of_nonpos hs]
      simp
  rw [h1, lintegral_indicator measurableSet_Ioi, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr]
    congr 1
    rw [Real.rpow_two, Real.Gamma_two]
    field_simp
  · have h : IntegrableOn (fun x : ℝ => 1 * (x ^ (1 : ℝ) * Real.exp (-1 * x ^ (1 : ℝ))))
        (Set.Ioi 0) := Integrable.const_mul (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1)
          (p := 1) (b := 1) (by norm_num) one_pos hr) 1
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have : (0 : ℝ) < s := hs
    positivity

lemma st5_exp_mean : ∫ x, x ∂(expMeasure 1) = 1 := by
  have hnn : 0 ≤ᵐ[expMeasure 1] fun x : ℝ => x := by
    rw [Filter.EventuallyLE, ae_iff]
    refine measure_mono_null (fun x hx => ?_) st5_exp_Iic
    simp only [Set.mem_setOf_eq, Pi.zero_apply, not_le] at hx
    exact hx.le
  rw [integral_eq_lintegral_of_nonneg_ae hnn measurable_id.aestronglyMeasurable,
    st5_lintegral_ofReal_exp]
  simp

lemma st5_exp_memLp : MemLp (fun x : ℝ => x) 2 (expMeasure 1) :=
  (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 st5_exp_sq

noncomputable def st5V : ℝ := variance (fun x : ℝ => x) (expMeasure 1)

lemma st5V_nonneg : 0 ≤ st5V := variance_nonneg _ _

open GVRPricing.StoppingTime in
lemma st5_cum_meas (n j : ℕ) : Measurable (fun E : Fin n → ℝ => cumClock E j) := by
  unfold cumClock
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

open GVRPricing.StoppingTime in
instance st5_clockLaw_prob (n : ℕ) : IsProbabilityMeasure (clockLaw n) := by
  unfold clockLaw; infer_instance

open GVRPricing.StoppingTime in
lemma st5_cheb (n j : ℕ) (hj : j ≤ n) (a : ℝ) (ha : 0 < a) :
    clockLaw n {E | a ≤ |cumClock E j - j|} ≤ ENNReal.ofReal (n * st5V / a ^ 2) := by
  set X : Fin n → ℝ → ℝ := fun i x => if i.val < j then x else 0 with hXdef
  have hX : ∀ i, MemLp (X i) 2 (expMeasure 1) := by
    intro i
    by_cases h : i.val < j
    · simp only [X, h, if_true]; exact st5_exp_memLp
    · simp only [X, h, if_false]; exact MemLp.zero
  have hS : (fun E : Fin n → ℝ => cumClock E j) = ∑ i, fun E : Fin n → ℝ => X i (E i) := by
    funext E
    rw [Finset.sum_apply]
    unfold cumClock
    rw [Finset.sum_filter]
  have hmem : MemLp (fun E : Fin n → ℝ => cumClock E j) 2 (clockLaw n) := by
    rw [hS]
    exact memLp_finsetSum' _ (fun i _ =>
      (hX i).comp_measurePreserving (measurePreserving_eval (fun _ => expMeasure 1) i))
  have hmean : ∫ E, cumClock E j ∂ clockLaw n = j := by
    have h1 : ∀ i : Fin n, ∫ E : Fin n → ℝ, X i (E i) ∂ clockLaw n = if i.val < j then 1 else 0 := by
      intro i
      unfold clockLaw
      rw [integral_comp_eval (hX i).aestronglyMeasurable]
      by_cases h : i.val < j
      · simp only [X, h, if_true]; exact st5_exp_mean
      · simp [X, h]
    have hpt : ∀ E : Fin n → ℝ, cumClock E j = ∑ i, X i (E i) := fun E => by
      have := congrFun hS E
      simpa only [Finset.sum_apply] using this
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => by
      exact ((hX i).comp_measurePreserving
        (measurePreserving_eval (fun _ => expMeasure 1) i)).integrable one_le_two)]
    simp only [h1]
    rw [Finset.sum_boole]
    simp only [Fin.card_filter_val_lt, Nat.cast_inj]
    simp only [min_eq_right hj]
  have hvar : variance (fun E : Fin n → ℝ => cumClock E j) (clockLaw n) ≤ n * st5V := by
    rw [hS]
    have := variance_sum_pi (μ := fun _ : Fin n => expMeasure 1) (X := X) hX
    unfold clockLaw
    rw [show (∑ i, fun E : Fin n → ℝ => X i (E i)) = (∑ i, fun ω : Fin n → ℝ => X i (ω i)) from rfl,
      this]
    have h2 : ∀ i : Fin n, variance (X i) (expMeasure 1) ≤ st5V := by
      intro i
      by_cases h : i.val < j
      · simp only [X, h, if_true]; exact le_rfl
      · simp only [X, h, if_false]
        rw [show (fun _ : ℝ => (0:ℝ)) = (0 : ℝ → ℝ) from rfl, variance_zero]
        exact st5V_nonneg
    calc ∑ i, variance (X i) (expMeasure 1) ≤ ∑ _i : Fin n, st5V := Finset.sum_le_sum fun i _ => h2 i
      _ = n * st5V := by simp
  have hc := meas_ge_le_variance_div_sq hmem ha
  rw [hmean] at hc
  refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right hvar (by positivity)

open GVRPricing.StoppingTime in
lemma st5_pos_ae (n : ℕ) : ∀ᵐ E ∂(clockLaw n), ∀ i, 0 < E i := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  have h : clockLaw n (Function.eval i ⁻¹' Set.Iic 0) = 0 := by
    unfold clockLaw
    exact Measure.pi_eval_preimage_null _ st5_exp_Iic
  refine measure_mono_null (fun E hE => ?_) h
  simp only [Set.mem_setOf_eq, not_lt] at hE
  exact hE

open GVRPricing.StoppingTime in
lemma st5_menu_facts {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) :
    0 < M.lamN (k+1) ∧ M.lamN (k+1) < M.lamN k ∧ 0 < M.pN k ∧ M.pN k < M.pN (k+1) := by
  have hk0 : k < K := by omega
  have hl0 : M.lamN k = M.lam ⟨k, hk0⟩ := by simp [Menu.lamN, hk0]
  have hl1 : M.lamN (k+1) = M.lam ⟨k+1, hk⟩ := by simp [Menu.lamN, hk]
  have hp0 : M.pN k = M.p ⟨k, hk0⟩ := by simp [Menu.pN, hk0]
  have hp1 : M.pN (k+1) = M.p ⟨k+1, hk⟩ := by simp [Menu.pN, hk]
  have hlt : (⟨k, hk0⟩ : Fin K) < ⟨k+1, hk⟩ := by
    rw [Fin.lt_def]; simp
  have hr : _ := M.r_strictAnti hlt
  simp only at hr
  have hpl := M.p_strictMono hlt
  have hll := M.lam_strictAnti hlt
  have hlpos := M.lam_pos ⟨k+1, hk⟩
  have hl0pos := M.lam_pos ⟨k, hk0⟩
  rw [hl0, hl1, hp0, hp1]
  refine ⟨hlpos, hll, ?_, hpl⟩
  have h1 : 0 < M.p ⟨k+1,hk⟩ * M.lam ⟨k+1,hk⟩ :=
    mul_pos (lt_of_le_of_lt (M.p_nonneg _) hpl) hlpos
  have h2 : 0 < M.p ⟨k,hk0⟩ * M.lam ⟨k,hk0⟩ := lt_trans h1 hr
  by_contra hc
  push_neg at hc
  nlinarith

open GVRPricing.StoppingTime in
lemma st5_r_lt {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) :
    M.pN (k+1) * M.lamN (k+1) < M.pN k * M.lamN k := by
  have hk0 : k < K := by omega
  have hl0 : M.lamN k = M.lam ⟨k, hk0⟩ := by simp [Menu.lamN, hk0]
  have hl1 : M.lamN (k+1) = M.lam ⟨k+1, hk⟩ := by simp [Menu.lamN, hk]
  have hp0 : M.pN k = M.p ⟨k, hk0⟩ := by simp [Menu.pN, hk0]
  have hp1 : M.pN (k+1) = M.p ⟨k+1, hk⟩ := by simp [Menu.pN, hk]
  have hlt : (⟨k, hk0⟩ : Fin K) < ⟨k+1, hk⟩ := by
    rw [Fin.lt_def]; simp
  have hr : _ := M.r_strictAnti hlt
  simp only at hr
  rw [hl0, hl1, hp0, hp1]
  exact hr

open GVRPricing.StoppingTime in
lemma st5_sum_two {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n t : ℝ) (g : Fin K → ℝ) :
    ∑ j, g j * twoPriceAlloc M k n t j =
      g ⟨k, by omega⟩ * ((n - M.lamN (k + 1) * t) / (M.lamN k - M.lamN (k + 1))) +
      g ⟨k+1, hk⟩ * ((M.lamN k * t - n) / (M.lamN k - M.lamN (k + 1))) := by
  rw [Fintype.sum_eq_add (⟨k, by omega⟩ : Fin K) ⟨k+1, hk⟩ (by simp [Fin.ext_iff])]
  · simp [twoPriceAlloc]
  · rintro x ⟨h1, h2⟩
    have h1' : x.val ≠ k := fun h => h1 (Fin.ext h)
    have h2' : x.val ≠ k + 1 := fun h => h2 (Fin.ext h)
    simp [twoPriceAlloc, h1', h2']

open GVRPricing.StoppingTime in
/-- The supporting line of the concave revenue curve through `(λ_{k+1}, r_{k+1})`, `(λ_k, r_k)`. -/
lemma st5_line {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (j : Fin K) :
    M.r j * (M.lamN k - M.lamN (k+1)) ≤
      (M.pN k * M.lamN k - M.pN (k+1) * M.lamN (k+1)) * M.lam j
        + M.lamN k * M.lamN (k+1) * (M.pN (k+1) - M.pN k) := by
  have hk0 : k < K := by omega
  have hl0 : M.lamN k = M.lam ⟨k, hk0⟩ := by simp [Menu.lamN, hk0]
  have hl1 : M.lamN (k+1) = M.lam ⟨k+1, hk⟩ := by simp [Menu.lamN, hk]
  have hp0 : M.pN k = M.p ⟨k, hk0⟩ := by simp [Menu.pN, hk0]
  have hp1 : M.pN (k+1) = M.p ⟨k+1, hk⟩ := by simp [Menu.pN, hk]
  obtain ⟨f, hf, -, hfr⟩ := M.concave
  have hr0 := hfr ⟨k, hk0⟩
  have hr1 := hfr ⟨k+1, hk⟩
  have hrj := hfr j
  rw [← hl0, ← hp0] at hr0
  rw [← hl1, ← hp1] at hr1
  unfold Menu.r
  rw [← hrj]
  obtain ⟨hl1pos, hll, -, -⟩ := st5_menu_facts M k hk
  have hjpos := M.lam_pos j
  set l0 := M.lamN k
  set l1 := M.lamN (k+1)
  set p0 := M.pN k
  set p1 := M.pN (k+1)
  set x := M.lam j
  rcases lt_trichotomy x l1 with hx | hx | hx
  · have h := hf.slope_anti_adjacent (x := x) (y := l1) (z := l0)
      (Set.mem_Ici.2 hjpos.le) (Set.mem_Ici.2 (by linarith)) hx hll
    rw [hr0, hr1, div_le_div_iff₀ (by linarith) (by linarith)] at h
    nlinarith
  · rw [hx, hr1]; ring_nf; nlinarith
  · rcases lt_trichotomy x l0 with hx' | hx' | hx'
    · -- strictly between: impossible since lam is strictly anti on Fin
      exfalso
      rw [hl0] at hx'
      rw [hl1] at hx
      rcases lt_trichotomy j.val k with h | h | h
      · have := M.lam_strictAnti (show j < ⟨k, hk0⟩ from Fin.lt_def.2 h)
        linarith
      · have h2 : M.lam j = M.lam ⟨k, hk0⟩ := congrArg M.lam (Fin.ext h)
        linarith
      · rcases Nat.lt_or_ge (k+1) j.val with h' | h'
        · have := M.lam_strictAnti (show (⟨k+1, hk⟩ : Fin K) < j from Fin.lt_def.2 h')
          linarith
        · have h2 : M.lam j = M.lam ⟨k+1, hk⟩ :=
            congrArg M.lam (Fin.ext (show j.val = k + 1 by omega))
          linarith
    · rw [hx', hr0]; ring_nf; nlinarith
    · have h := hf.slope_anti_adjacent (x := l1) (y := l0) (z := x)
        (Set.mem_Ici.2 hl1pos.le) (Set.mem_Ici.2 hjpos.le) hll hx'
      rw [hr0, hr1, div_le_div_iff₀ (by linarith) (by linarith)] at h
      nlinarith

open GVRPricing.StoppingTime in
lemma st5_detValue {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n t : ℝ)
    (hup : n ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    detValue M n t = M.pN k * (M.lamN k * tK M k n t)
      + M.pN (k+1) * (n - M.lamN k * tK M k n t) := by
  obtain ⟨hl1pos, hll, hp0pos, hpp⟩ := st5_menu_facts M k hk
  have hrr := st5_r_lt M k hk
  have hd : 0 < M.lamN k - M.lamN (k+1) := by linarith
  set A := M.pN k * M.lamN k - M.pN (k+1) * M.lamN (k+1) with hA
  set B := M.lamN k * M.lamN (k+1) * (M.pN (k+1) - M.pN k) with hB
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by
    have : 0 < M.lamN k * M.lamN (k+1) := mul_pos (by linarith) hl1pos
    rw [hB]; exact mul_nonneg this.le (by linarith)
  have hD : M.pN k * (M.lamN k * tK M k n t) + M.pN (k+1) * (n - M.lamN k * tK M k n t)
      = (A * n + B * t) / (M.lamN k - M.lamN (k+1)) := by
    unfold tK
    rw [hA, hB]
    field_simp
    ring
  unfold detValue
  refine IsGreatest.csSup_eq ⟨⟨twoPriceAlloc M k n t, ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro j
    unfold twoPriceAlloc
    split_ifs
    · exact div_nonneg (by linarith) hd.le
    · exact div_nonneg (by linarith) hd.le
    · exact le_rfl
  · have := st5_sum_two M k hk n t (fun _ => 1)
    simp only [one_mul] at this
    rw [this, ← add_div, div_le_iff₀ hd]
    nlinarith
  · have := st5_sum_two M k hk n t M.lam
    rw [this]
    have hk0 : k < K := by omega
    have hl0 : M.lam ⟨k, hk0⟩ = M.lamN k := by simp [Menu.lamN, hk0]
    have hl1 : M.lam ⟨k+1, hk⟩ = M.lamN (k+1) := by simp [Menu.lamN, hk]
    rw [hl0, hl1, mul_div_assoc', mul_div_assoc', ← add_div, div_le_iff₀ hd]
    nlinarith
  · unfold lpRevenue
    rw [st5_sum_two M k hk n t M.r]
    have hk0 : k < K := by omega
    have hl0 : M.r ⟨k, hk0⟩ = M.pN k * M.lamN k := by simp [Menu.r, Menu.lamN, Menu.pN, hk0]
    have hl1 : M.r ⟨k+1, hk⟩ = M.pN (k+1) * M.lamN (k+1) := by
      simp [Menu.r, Menu.lamN, Menu.pN, hk]
    rw [hl0, hl1]
    unfold tK
    field_simp
    ring
  · rintro v ⟨τ, ⟨hτ0, hτt, hτn⟩, rfl⟩
    rw [hD, le_div_iff₀ hd]
    unfold lpRevenue
    rw [Finset.sum_mul]
    calc ∑ j, M.r j * τ j * (M.lamN k - M.lamN (k+1))
        ≤ ∑ j, (A * (M.lam j * τ j) + B * τ j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h := st5_line M k hk j
          have := hτ0 j
          rw [← hA, ← hB] at h
          nlinarith
      _ = A * ∑ j, M.lam j * τ j + B * ∑ j, τ j := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ A * n + B * t := by
          have h1 := mul_le_mul_of_nonneg_left hτn hA0
          have h2 := mul_le_mul_of_nonneg_left hτt hB0
          linarith

open GVRPricing.StoppingTime in
lemma st5_cum_mono {n : ℕ} (E : Fin n → ℝ) (hE : ∀ i, 0 ≤ E i) {a b : ℕ} (hab : a ≤ b) :
    cumClock E a ≤ cumClock E b := by
  unfold cumClock
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  · intro i _ _; exact hE i

open GVRPricing.StoppingTime in
lemma st5_cum_succ {n : ℕ} (E : Fin n → ℝ) (j : ℕ) (hj : j < n) :
    cumClock E (j+1) = cumClock E j + E ⟨j, hj⟩ := by
  unfold cumClock
  rw [show (Finset.univ.filter fun i : Fin n => i.val < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter fun i : Fin n => i.val < j) by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega]
  rw [Finset.sum_insert (by simp)]
  ring

open GVRPricing.StoppingTime in
lemma st5_f_eq {K : ℕ} (M : Menu K) (k n : ℕ) (t : ℝ) (E : Fin n → ℝ) (i : Fin n) :
    (if saleTime M k n t E i ≤ t then salePrice M k n t E i else 0) =
      if cumClock E (i.val+1) ≤ M.lamN k * switchTime M k n t E then
        (if cumClock E (i.val+1) / M.lamN k ≤ t then M.pN k else 0)
      else (if switchTime M k n t E + (cumClock E (i.val+1) - M.lamN k * switchTime M k n t E)
          / M.lamN (k+1) ≤ t then M.pN (k+1) else 0) := by
  simp only [saleTime, salePrice]
  by_cases hc : cumClock E (i.val+1) ≤ M.lamN k * switchTime M k n t E
  · simp only [hc, if_true]
  · simp only [hc, if_false]

open GVRPricing.StoppingTime in
lemma st5_regime {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    M.lamN k * tK M k n t ≤ GVRPricing.StoppingTime.stM M k n t ∧ (GVRPricing.StoppingTime.stM M k n t : ℝ) < M.lamN k * tK M k n t + 1 ∧
    GVRPricing.StoppingTime.stM M k n t ≤ n ∧ 0 < M.lamN k * tK M k n t ∧
    (M.lamN k - M.lamN (k+1)) * tK M k n t = n - M.lamN (k+1) * t ∧
    M.lamN k * tm M k n t = GVRPricing.StoppingTime.stM M k n t := by
  obtain ⟨hl1pos, hll, hp0pos, hpp⟩ := st5_menu_facts M k hk
  have hd : 0 < M.lamN k - M.lamN (k+1) := by linarith
  have hl0 : 0 < M.lamN k := by linarith
  have htK : (M.lamN k - M.lamN (k+1)) * tK M k n t = n - M.lamN (k+1) * t := by
    unfold tK; field_simp
  have hpos : 0 < M.lamN k * tK M k n t := by
    unfold tK; apply mul_pos hl0; apply div_pos _ hd; linarith
  have hle : M.lamN k * tK M k n t ≤ n := by
    unfold tK
    rw [← mul_div_assoc, div_le_iff₀ hd]
    nlinarith
  refine ⟨by unfold GVRPricing.StoppingTime.stM; exact Nat.le_ceil _, by unfold GVRPricing.StoppingTime.stM; exact Nat.ceil_lt_add_one hpos.le,
    by unfold GVRPricing.StoppingTime.stM; exact Nat.ceil_le.2 hle, hpos, htK, ?_⟩
  unfold tm
  field_simp

open GVRPricing.StoppingTime in
lemma st5_pw {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n)
    (E : Fin n → ℝ) (hE : ∀ i, 0 < E i) (δ : ℝ) (hδ : 0 ≤ δ) :
    stRevenue M k n t E ≤ M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * GVRPricing.StoppingTime.stM M k n t
        + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < GVRPricing.StoppingTime.stM M k n t),
            (if (GVRPricing.StoppingTime.stM M k n t : ℝ) < cumClock E (i.val + 1) then M.pN (k+1) - M.pN k else 0) ∧
    M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * GVRPricing.StoppingTime.stM M k n t ≤ stRevenue M k n t E
        + ∑ i : Fin n, (if (1 - δ) * n < cumClock E (i.val + 1) then M.pN (k+1) else 0)
        + ∑ _i : Fin n, (if cumClock E (GVRPricing.StoppingTime.stM M k n t) < GVRPricing.StoppingTime.stM M k n t - δ * n then M.pN (k+1) else 0) := by
  obtain ⟨hl1pos, hll, hp0pos, hpp⟩ := st5_menu_facts M k hk
  obtain ⟨hmge, hmlt, hmn, hapos, htK, htm⟩ := st5_regime M k hk n t hup hlow
  have hl0 : 0 < M.lamN k := by linarith
  have hd : 0 < M.lamN k - M.lamN (k+1) := by linarith
  have hE0 : ∀ i, 0 ≤ E i := fun i => (hE i).le
  have hmnR : (GVRPricing.StoppingTime.stM M k n t : ℝ) ≤ n := by exact_mod_cast hmn
  have hL : M.lamN k * switchTime M k n t E = min (cumClock E (GVRPricing.StoppingTime.stM M k n t)) (GVRPricing.StoppingTime.stM M k n t) := by
    unfold switchTime
    rw [mul_min_of_nonneg _ _ hl0.le, mul_div_cancel₀ _ hl0.ne', htm]
  have hcum0 : 0 ≤ cumClock E (GVRPricing.StoppingTime.stM M k n t) := by
    unfold cumClock; exact Finset.sum_nonneg fun i _ => hE0 i
  have hτ0 : 0 ≤ switchTime M k n t E := by
    have : 0 ≤ M.lamN k * switchTime M k n t E := by
      rw [hL]; exact le_min hcum0 (Nat.cast_nonneg _)
    by_contra hc
    push_neg at hc
    nlinarith
  have hτt : switchTime M k n t E ≤ t := by
    have h1 : M.lamN k * switchTime M k n t E ≤ M.lamN k * t := by
      rw [hL]; exact (min_le_right _ _).trans (hmnR.trans hup)
    exact le_of_mul_le_mul_left h1 hl0
  have hc : ∀ i : Fin n, cumClock E (i.val+1) ≤ M.lamN k * switchTime M k n t E →
      i.val < GVRPricing.StoppingTime.stM M k n t := by
    intro i hi
    by_contra hne
    push_neg at hne
    have hlt : GVRPricing.StoppingTime.stM M k n t < n := lt_of_le_of_lt hne i.isLt
    have h1 : cumClock E (GVRPricing.StoppingTime.stM M k n t + 1) ≤ cumClock E (i.val + 1) :=
      st5_cum_mono E hE0 (by omega)
    have h2 := st5_cum_succ E (GVRPricing.StoppingTime.stM M k n t) hlt
    have h3 : M.lamN k * switchTime M k n t E ≤ cumClock E (GVRPricing.StoppingTime.stM M k n t) := by
      rw [hL]; exact min_le_left _ _
    have := hE ⟨GVRPricing.StoppingTime.stM M k n t, hlt⟩
    linarith
  have hsold1 : ∀ i : Fin n, cumClock E (i.val+1) ≤ M.lamN k * switchTime M k n t E →
      cumClock E (i.val+1) / M.lamN k ≤ t := by
    intro i hi
    rw [div_le_iff₀ hl0]; nlinarith
  have hsold2 : ∀ i : Fin n,
      cumClock E (i.val+1) ≤ M.lamN k * switchTime M k n t E
        + M.lamN (k+1) * (t - switchTime M k n t E) →
      switchTime M k n t E + (cumClock E (i.val+1) - M.lamN k * switchTime M k n t E)
        / M.lamN (k+1) ≤ t := by
    intro i hi
    have : (cumClock E (i.val+1) - M.lamN k * switchTime M k n t E) / M.lamN (k+1)
        ≤ t - switchTime M k n t E := by
      rw [div_le_iff₀ hl1pos]; linarith
    linarith
  have hp0le : M.pN k ≤ M.pN (k+1) := hpp.le
  -- sums of the constant parts
  have e1 : ∑ i : Fin n, (if i.val < GVRPricing.StoppingTime.stM M k n t then M.pN (k+1) - M.pN k else 0)
      = (M.pN (k+1) - M.pN k) * GVRPricing.StoppingTime.stM M k n t := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      Fin.card_filter_val_lt, min_eq_right hmn, nsmul_eq_mul]
    ring
  have e3 : ∑ _i : Fin n, M.pN (k+1) = M.pN (k+1) * n := by
    simp [Finset.sum_const]; ring
  constructor
  · have hper : ∀ i : Fin n, (if saleTime M k n t E i ≤ t then salePrice M k n t E i else 0)
        + (if i.val < GVRPricing.StoppingTime.stM M k n t then M.pN (k+1) - M.pN k else 0)
        ≤ M.pN (k+1) + (if i.val < GVRPricing.StoppingTime.stM M k n t then
            (if (GVRPricing.StoppingTime.stM M k n t : ℝ) < cumClock E (i.val + 1) then M.pN (k+1) - M.pN k else 0)
            else 0) := by
      intro i
      rw [st5_f_eq]
      by_cases him : i.val < GVRPricing.StoppingTime.stM M k n t
      · by_cases hS : (GVRPricing.StoppingTime.stM M k n t : ℝ) < cumClock E (i.val + 1)
        · simp only [him, hS, if_true]
          split_ifs <;> linarith
        · simp only [him, hS, if_true, if_false]
          have hle : cumClock E (i.val+1) ≤ M.lamN k * switchTime M k n t E := by
            rw [hL]
            exact le_min (st5_cum_mono E hE0 (by omega)) (not_lt.1 hS)
          rw [if_pos hle, if_pos (hsold1 i hle)]
          linarith
      · simp only [him, if_false]
        split_ifs <;> linarith
    unfold stRevenue
    rw [Finset.sum_filter]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hper i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e3] at hsum
    linarith
  · have hper : ∀ i : Fin n, M.pN (k+1) ≤
        (if saleTime M k n t E i ≤ t then salePrice M k n t E i else 0)
        + (if i.val < GVRPricing.StoppingTime.stM M k n t then M.pN (k+1) - M.pN k else 0)
        + (if (1 - δ) * n < cumClock E (i.val + 1) then M.pN (k+1) else 0)
        + (if cumClock E (GVRPricing.StoppingTime.stM M k n t) < GVRPricing.StoppingTime.stM M k n t - δ * n then M.pN (k+1) else 0) := by
      intro i
      rw [st5_f_eq]
      by_cases h1 : (1 - δ) * n < cumClock E (i.val + 1)
      · simp only [h1, if_true]
        split_ifs <;> linarith
      by_cases h2 : cumClock E (GVRPricing.StoppingTime.stM M k n t) < GVRPricing.StoppingTime.stM M k n t - δ * n
      · simp only [h2, if_true]
        split_ifs <;> linarith
      simp only [h1, h2, if_false, add_zero]
      push_neg at h1 h2
      have hu : (GVRPricing.StoppingTime.stM M k n t : ℝ) - δ * n ≤ M.lamN k * switchTime M k n t E := by
        rw [hL]
        refine le_min h2 ?_
        nlinarith [mul_nonneg hδ (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have k1 := mul_le_mul_of_nonneg_right hu hd.le
      have k2 := mul_le_mul_of_nonneg_right hmge hd.le
      have h3 : M.lamN k * ((M.lamN k - M.lamN (k+1)) * tK M k n t)
          = M.lamN k * (n - M.lamN (k+1) * t) := by rw [htK]
      have h4 : 0 ≤ δ * n * M.lamN (k+1) :=
        mul_nonneg (mul_nonneg hδ (Nat.cast_nonneg n)) hl1pos.le
      have key : M.lamN k * ((1 - δ) * n) ≤ M.lamN k * (M.lamN k * switchTime M k n t E
          + M.lamN (k+1) * (t - switchTime M k n t E)) := by
        nlinarith
      have key' := le_of_mul_le_mul_left key hl0
      by_cases hle : cumClock E (i.val+1) ≤ M.lamN k * switchTime M k n t E
      · rw [if_pos hle, if_pos (hsold1 i hle), if_pos (hc i hle)]
        linarith
      · rw [if_neg hle, if_pos (hsold2 i (h1.trans key'))]
        split_ifs <;> linarith
    unfold stRevenue
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hper i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e3] at hsum
    linarith

lemma st5_card (n N : ℕ) (hN : N ≤ n) (y : ℝ) (hy : y ≤ N) :
    ((Finset.univ.filter (fun i : Fin n => i.val < N ∧ y < ((i.val + 1 : ℕ) : ℝ))).card : ℝ)
      ≤ N - y + 1 := by
  have h1 : (Finset.univ.filter (fun i : Fin n => i.val < N ∧ y < ((i.val + 1 : ℕ) : ℝ))).card ≤
      (Finset.Ico ⌊y⌋₊ N).card := by
    apply Finset.card_le_card_of_injOn (fun i => i.val)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hi
      simp only [Finset.coe_Ico, Finset.mem_coe, Finset.mem_Ico, Set.mem_Ico]
      refine ⟨?_, hi.1⟩
      by_contra hc
      push_neg at hc
      have h3 : i.val + 1 ≤ ⌊y⌋₊ := hc
      have h2 := (Nat.le_floor_iff' (Nat.succ_ne_zero i.val)).1 h3
      linarith [hi.2]
    · intro a _ b _ h
      exact Fin.ext h
  rw [Nat.card_Ico] at h1
  have hfl : ⌊y⌋₊ ≤ N := by
    have := Nat.floor_mono hy
    simpa using this
  have h3 : ((N - ⌊y⌋₊ : ℕ) : ℝ) = N - ⌊y⌋₊ := Nat.cast_sub hfl
  have h4 := Nat.lt_floor_add_one y
  have h5 : ((Finset.univ.filter (fun i : Fin n => i.val < N ∧ y < ((i.val + 1 : ℕ) : ℝ))).card : ℝ)
      ≤ ((N - ⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

open GVRPricing.StoppingTime in
lemma st5_tail (n j : ℕ) (hj : j ≤ n) (hn : 0 < n) (x δ : ℝ) (hδ : 0 < δ) :
    clockLaw n {E | x < cumClock E j} ≤
      ENNReal.ofReal (st5V / (δ ^ 2 * n) + if x - δ * n < (j : ℝ) then 1 else 0) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hV := st5V_nonneg
  have hq : 0 ≤ st5V / (δ ^ 2 * n) := by positivity
  split_ifs with h
  · calc _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  · push_neg at h
    have hsub : {E : Fin n → ℝ | x < cumClock E j} ⊆ {E | δ * n ≤ |cumClock E j - j|} := by
      intro E hE
      simp only [Set.mem_setOf_eq] at hE ⊢
      rw [le_abs]
      left
      linarith
    refine (measure_mono hsub).trans ((st5_cheb n j hj (δ * n) (by positivity)).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    rw [add_zero]
    apply le_of_eq
    field_simp
    try ring

open GVRPricing.StoppingTime in
lemma st5_lowtail (n j : ℕ) (hj : j ≤ n) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    clockLaw n {E | cumClock E j < j - δ * n} ≤ ENNReal.ofReal (st5V / (δ ^ 2 * n)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hsub : {E : Fin n → ℝ | cumClock E j < j - δ * n} ⊆ {E | δ * n ≤ |cumClock E j - j|} := by
    intro E hE
    simp only [Set.mem_setOf_eq] at hE ⊢
    rw [le_abs]
    right
    linarith
  refine (measure_mono hsub).trans ((st5_cheb n j hj (δ * n) (by positivity)).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  field_simp
  try ring

open GVRPricing.StoppingTime in
lemma st5_rev_bounds {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (E : Fin n → ℝ) :
    0 ≤ stRevenue M k n t E ∧ stRevenue M k n t E ≤ n * M.pN (k+1) := by
  obtain ⟨-, -, hp0pos, hpp⟩ := st5_menu_facts M k hk
  unfold stRevenue
  constructor
  · exact Finset.sum_nonneg fun i _ => by unfold salePrice; split_ifs <;> linarith
  · calc _ ≤ ∑ _i : Fin n, M.pN (k+1) :=
          Finset.sum_le_sum fun i _ => by unfold salePrice; split_ifs <;> linarith
      _ = n * M.pN (k+1) := by simp

lemma st5_npos {K : ℕ} (M : GVRPricing.StoppingTime.Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ)
    (t : ℝ) (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) : 0 < n := by
  obtain ⟨hl1pos, hll, -, -⟩ := st5_menu_facts M k hk
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [Nat.cast_zero] at hup hlow
    nlinarith
  · exact h

open GVRPricing.StoppingTime in
lemma st5_upper {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) (δ : ℝ) (hδ : 0 < δ) :
    jST M k n t ≤ M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * GVRPricing.StoppingTime.stM M k n t
      + (M.pN (k+1) - M.pN k) * (st5V / δ ^ 2 + δ * n + 1) := by
  obtain ⟨hl1pos, hll, hp0pos, hpp⟩ := st5_menu_facts M k hk
  obtain ⟨hmge, hmlt, hmn, hapos, htK, htm⟩ := st5_regime M k hk n t hup hlow
  have hnpos := st5_npos M k hk n t hup hlow
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hmnR : (GVRPricing.StoppingTime.stM M k n t : ℝ) ≤ n := by exact_mod_cast hmn
  have hV := st5V_nonneg
  have hc0 : 0 ≤ M.pN (k+1) - M.pN k := by linarith
  have hU0 : 0 ≤ M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * GVRPricing.StoppingTime.stM M k n t := by
    nlinarith
  have hAm : ∀ i : Fin n, MeasurableSet
      {E : Fin n → ℝ | (GVRPricing.StoppingTime.stM M k n t : ℝ) < cumClock E (i.val + 1)} :=
    fun i => measurableSet_lt measurable_const (st5_cum_meas n _)
  have hpw : ∀ᵐ E ∂(clockLaw n), ENNReal.ofReal (stRevenue M k n t E) ≤
      ENNReal.ofReal (M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * GVRPricing.StoppingTime.stM M k n t)
      + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < GVRPricing.StoppingTime.stM M k n t),
        {E : Fin n → ℝ | (GVRPricing.StoppingTime.stM M k n t : ℝ) < cumClock E (i.val + 1)}.indicator
          (fun _ => ENNReal.ofReal (M.pN (k+1) - M.pN k)) E := by
    filter_upwards [st5_pos_ae n] with E hE
    have h := (st5_pw M k hk n t hup hlow E hE 1 zero_le_one).1
    refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add hU0 (Finset.sum_nonneg fun i _ => by split_ifs <;> linarith),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> linarith)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> simp
  have hint : ∫⁻ E, ENNReal.ofReal (stRevenue M k n t E) ∂(clockLaw n) ≤
      ENNReal.ofReal (M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * GVRPricing.StoppingTime.stM M k n t)
      + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < GVRPricing.StoppingTime.stM M k n t),
        ENNReal.ofReal (M.pN (k+1) - M.pN k) *
          clockLaw n {E : Fin n → ℝ | (GVRPricing.StoppingTime.stM M k n t : ℝ) < cumClock E (i.val + 1)} := by
    refine (lintegral_mono_ae hpw).trans (le_of_eq ?_)
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_finset_sum _ (fun i _ => (measurable_const.indicator (hAm i)))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_indicator_const (hAm i)]
  have hb : ∀ i ∈ Finset.univ.filter (fun i : Fin n => i.val < GVRPricing.StoppingTime.stM M k n t),
      ENNReal.ofReal (M.pN (k+1) - M.pN k) *
          clockLaw n {E : Fin n → ℝ | (GVRPricing.StoppingTime.stM M k n t : ℝ) < cumClock E (i.val + 1)}
        ≤ ENNReal.ofReal ((M.pN (k+1) - M.pN k) * (st5V / (δ ^ 2 * n)
          + if (GVRPricing.StoppingTime.stM M k n t : ℝ) - δ * n < ((i.val + 1 : ℕ) : ℝ) then 1 else 0)) := by
    intro i hi
    have hi' : i.val < GVRPricing.StoppingTime.stM M k n t := (Finset.mem_filter.1 hi).2
    rw [ENNReal.ofReal_mul hc0]
    gcongr
    exact st5_tail n (i.val+1) (by omega) hnpos _ δ hδ
  have hsumb := Finset.sum_le_sum hb
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hc0
    (add_nonneg (by positivity) (by split_ifs <;> norm_num)))] at hsumb
  have hreal : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < GVRPricing.StoppingTime.stM M k n t),
      (M.pN (k+1) - M.pN k) * (st5V / (δ ^ 2 * n)
          + if (GVRPricing.StoppingTime.stM M k n t : ℝ) - δ * n < ((i.val + 1 : ℕ) : ℝ) then 1 else 0)
      ≤ (M.pN (k+1) - M.pN k) * (st5V / δ ^ 2 + δ * n + 1) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Fin.card_filter_val_lt,
      min_eq_right hmn, nsmul_eq_mul, Finset.sum_boole, Finset.filter_filter]
    apply mul_le_mul_of_nonneg_left _ hc0
    have hcard := st5_card n (GVRPricing.StoppingTime.stM M k n t) hmn
      ((GVRPricing.StoppingTime.stM M k n t : ℝ) - δ * n) (by nlinarith)
    have h6 : (GVRPricing.StoppingTime.stM M k n t : ℝ) * (st5V / (δ ^ 2 * n)) ≤ st5V / δ ^ 2 := by
      rw [show st5V / (δ ^ 2 * n) = (st5V / δ ^ 2) / n by rw [div_div]]
      rw [mul_div_assoc', div_le_iff₀ hnR]
      have : 0 ≤ st5V / δ ^ 2 := by positivity
      nlinarith
    linarith
  have htot : ∫⁻ E, ENNReal.ofReal (stRevenue M k n t E) ∂(clockLaw n) ≤
      ENNReal.ofReal (M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * GVRPricing.StoppingTime.stM M k n t
        + (M.pN (k+1) - M.pN k) * (st5V / δ ^ 2 + δ * n + 1)) := by
    refine hint.trans ?_
    rw [ENNReal.ofReal_add hU0 (mul_nonneg hc0 (by positivity))]
    gcongr
    exact hsumb.trans (ENNReal.ofReal_le_ofReal hreal)
  unfold jST
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg hU0 (mul_nonneg hc0 (by positivity))) htot

open GVRPricing.StoppingTime in
lemma st5_lower {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) (δ : ℝ) (hδ : 0 < δ) :
    M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * GVRPricing.StoppingTime.stM M k n t ≤ jST M k n t
      + M.pN (k+1) * (2 * st5V / δ ^ 2 + 2 * δ * n + 1) := by
  obtain ⟨hl1pos, hll, hp0pos, hpp⟩ := st5_menu_facts M k hk
  obtain ⟨hmge, hmlt, hmn, hapos, htK, htm⟩ := st5_regime M k hk n t hup hlow
  have hnpos := st5_npos M k hk n t hup hlow
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hmnR : (GVRPricing.StoppingTime.stM M k n t : ℝ) ≤ n := by exact_mod_cast hmn
  have hV := st5V_nonneg
  have hp1 : 0 ≤ M.pN (k+1) := by linarith
  set m := GVRPricing.StoppingTime.stM M k n t with hm
  have hU0 : 0 ≤ M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * m := by nlinarith
  have hAm : ∀ i : Fin n, MeasurableSet {E : Fin n → ℝ | (1 - δ) * n < cumClock E (i.val + 1)} :=
    fun i => measurableSet_lt measurable_const (st5_cum_meas n _)
  have hBm : MeasurableSet {E : Fin n → ℝ | cumClock E m < m - δ * n} :=
    measurableSet_lt (st5_cum_meas n _) measurable_const
  set g : (Fin n → ℝ) → ENNReal := fun E =>
    ∑ i : Fin n, {E : Fin n → ℝ | (1 - δ) * n < cumClock E (i.val + 1)}.indicator
        (fun _ => ENNReal.ofReal (M.pN (k+1))) E
      + ∑ _i : Fin n, {E : Fin n → ℝ | cumClock E m < m - δ * n}.indicator
        (fun _ => ENNReal.ofReal (M.pN (k+1))) E with hg
  have hgm : Measurable g := by
    refine Measurable.add (Finset.measurable_sum _ fun i _ => measurable_const.indicator (hAm i))
      (Finset.measurable_sum _ fun i _ => measurable_const.indicator hBm)
  have hpw : ∀ᵐ E ∂(clockLaw n), ENNReal.ofReal (M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * m) ≤
      ENNReal.ofReal (stRevenue M k n t E) + g E := by
    filter_upwards [st5_pos_ae n] with E hE
    have h := (st5_pw M k hk n t hup hlow E hE δ hδ.le).2
    have hr0 := (st5_rev_bounds M k hk n t E).1
    refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
    have hs1 : 0 ≤ ∑ i : Fin n, (if (1 - δ) * n < cumClock E (i.val + 1) then M.pN (k+1) else 0) :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> linarith
    have hs2 : 0 ≤ ∑ _i : Fin n, (if cumClock E m < m - δ * n then M.pN (k+1) else 0) :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> linarith
    rw [add_assoc, ENNReal.ofReal_add hr0 (add_nonneg hs1 hs2), ENNReal.ofReal_add hs1 hs2,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> linarith),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> linarith)]
    simp only [hg]
    congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs <;> simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs <;> simp
  have hint : ENNReal.ofReal (M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * m) ≤
      ∫⁻ E, ENNReal.ofReal (stRevenue M k n t E) ∂(clockLaw n)
      + (∑ i : Fin n, ENNReal.ofReal (M.pN (k+1)) *
          clockLaw n {E : Fin n → ℝ | (1 - δ) * n < cumClock E (i.val + 1)}
        + ∑ _i : Fin n, ENNReal.ofReal (M.pN (k+1)) *
          clockLaw n {E : Fin n → ℝ | cumClock E m < m - δ * n}) := by
    calc _ = ∫⁻ _E, ENNReal.ofReal (M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * m) ∂(clockLaw n) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ E, (ENNReal.ofReal (stRevenue M k n t E) + g E) ∂(clockLaw n) := lintegral_mono_ae hpw
      _ = _ := by
          rw [lintegral_add_right _ hgm]
          congr 1
          simp only [hg]
          rw [lintegral_add_left (Finset.measurable_sum _ fun i _ => measurable_const.indicator (hAm i)),
            lintegral_finset_sum _ (fun i _ => measurable_const.indicator (hAm i)),
            lintegral_finset_sum _ (fun i _ => measurable_const.indicator hBm)]
          congr 1
          · exact Finset.sum_congr rfl fun i _ => lintegral_indicator_const (hAm i) _
          · exact Finset.sum_congr rfl fun i _ => lintegral_indicator_const hBm _
  -- bounds on the error sums
  have hb1 : ∀ i ∈ (Finset.univ : Finset (Fin n)), ENNReal.ofReal (M.pN (k+1)) *
        clockLaw n {E : Fin n → ℝ | (1 - δ) * n < cumClock E (i.val + 1)}
      ≤ ENNReal.ofReal (M.pN (k+1) * (st5V / (δ ^ 2 * n)
          + if (1 - δ) * n - δ * n < ((i.val + 1 : ℕ) : ℝ) then 1 else 0)) := by
    intro i _
    rw [ENNReal.ofReal_mul hp1]
    gcongr
    exact st5_tail n (i.val+1) (by omega) hnpos _ δ hδ
  have hsum1 := Finset.sum_le_sum hb1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hp1
    (add_nonneg (by positivity) (by split_ifs <;> norm_num)))] at hsum1
  have hreal1 : ∑ i : Fin n, M.pN (k+1) * (st5V / (δ ^ 2 * n)
          + if (1 - δ) * n - δ * n < ((i.val + 1 : ℕ) : ℝ) then 1 else 0)
      ≤ M.pN (k+1) * (st5V / δ ^ 2 + 2 * δ * n + 1) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.sum_boole]
    apply mul_le_mul_of_nonneg_left _ hp1
    have hcard := st5_card n n le_rfl ((1 - δ) * n - δ * n) (by nlinarith)
    have hceq : (Finset.univ.filter (fun i : Fin n => (1 - δ) * n - δ * n < ((i.val + 1 : ℕ) : ℝ)))
        = Finset.univ.filter (fun i : Fin n => i.val < n ∧ (1 - δ) * n - δ * n < ((i.val + 1 : ℕ) : ℝ)) :=
      Finset.filter_congr (fun i _ => ⟨fun h => ⟨i.isLt, h⟩, fun h => h.2⟩)
    rw [hceq]
    have h6 : (n : ℝ) * (st5V / (δ ^ 2 * n)) = st5V / δ ^ 2 := by
      field_simp
    linarith
  have hb2 : ∑ _i : Fin n, ENNReal.ofReal (M.pN (k+1)) *
        clockLaw n {E : Fin n → ℝ | cumClock E m < m - δ * n}
      ≤ ENNReal.ofReal (M.pN (k+1) * (st5V / δ ^ 2)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (n : ENNReal) * (ENNReal.ofReal (M.pN (k+1)) * clockLaw n {E : Fin n → ℝ | cumClock E m < m - δ * n})
        ≤ ENNReal.ofReal n * (ENNReal.ofReal (M.pN (k+1)) * ENNReal.ofReal (st5V / (δ ^ 2 * n))) := by
          rw [ENNReal.ofReal_natCast]
          gcongr
          exact st5_lowtail n m hmn hnpos δ hδ
      _ = ENNReal.ofReal (M.pN (k+1) * (st5V / δ ^ 2)) := by
          rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_mul hnR.le]
          congr 1
          field_simp
  have hfin : ∫⁻ E, ENNReal.ofReal (stRevenue M k n t E) ∂(clockLaw n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _E, ENNReal.ofReal (n * M.pN (k+1)) ∂(clockLaw n)) ?_ ?_
    · rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
    · exact lintegral_mono fun E => ENNReal.ofReal_le_ofReal (st5_rev_bounds M k hk n t E).2
  have htot : ENNReal.ofReal (M.pN (k+1) * n - (M.pN (k+1) - M.pN k) * m) ≤
      ∫⁻ E, ENNReal.ofReal (stRevenue M k n t E) ∂(clockLaw n)
      + ENNReal.ofReal (M.pN (k+1) * (2 * st5V / δ ^ 2 + 2 * δ * n + 1)) := by
    refine hint.trans ?_
    gcongr
    have hr : M.pN (k+1) * (st5V / δ ^ 2 + 2 * δ * n + 1) + M.pN (k+1) * (st5V / δ ^ 2)
        = M.pN (k+1) * (2 * st5V / δ ^ 2 + 2 * δ * n + 1) := by ring
    rw [← hr, ENNReal.ofReal_add (mul_nonneg hp1 (by positivity)) (mul_nonneg hp1 (by positivity))]
    exact add_le_add (hsum1.trans (ENNReal.ofReal_le_ofReal hreal1)) hb2
  have h2 := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩)).1 htot
  rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg hp1 (by positivity))] at h2
  unfold jST
  exact h2

open GVRPricing.StoppingTime Filter Topology in
theorem solution {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K)
    (n : ℕ → ℕ) (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hreg : ∀ j, (n j : ℝ) ≤ M.lamN k * t j ∧ M.lamN (k + 1) * t j < n j) :
    Tendsto (fun j => jST M k (n j) (t j) / detValue M (n j) (t j)) atTop (𝓝 1) := by
  obtain ⟨hl1pos, hll, hp0pos, hpp⟩ := st5_menu_facts M k hk
  have hp1 : 0 < M.pN (k+1) := by linarith
  have hV := st5V_nonneg
  have hkey : ∀ δ > 0, ∀ j, |jST M k (n j) (t j) - detValue M (n j) (t j)|
      ≤ 2 * M.pN (k+1) * δ * n j + M.pN (k+1) * (2 * st5V / δ ^ 2 + 2) := by
    intro δ hδ j
    obtain ⟨hup, hlow⟩ := hreg j
    obtain ⟨hmge, hmlt, hmn, hapos, htK, htm⟩ := st5_regime M k hk (n j) (t j) hup hlow
    have hU := st5_upper M k hk (n j) (t j) hup hlow δ hδ
    have hL := st5_lower M k hk (n j) (t j) hup hlow δ hδ
    have hD := st5_detValue M k hk (n j) (t j) hup hlow
    have hc0 : 0 ≤ M.pN (k+1) - M.pN k := by linarith
    have k1 := mul_le_mul_of_nonneg_left hmge hc0
    have k2 := mul_le_mul_of_nonneg_left hmlt.le hc0
    have hq : 0 ≤ st5V / δ ^ 2 := by positivity
    have hq2 : 2 * st5V / δ ^ 2 = 2 * (st5V / δ ^ 2) := by ring
    have hnj : (0:ℝ) ≤ n j := Nat.cast_nonneg _
    rw [abs_sub_le_iff]
    constructor
    · rw [hD]
      have k3 : (M.pN (k+1) - M.pN k) * (st5V / δ ^ 2 + δ * n j + 1)
          ≤ M.pN (k+1) * (st5V / δ ^ 2 + δ * n j + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith
    · rw [hD]
      nlinarith
  have hD : ∀ j, M.pN k * n j ≤ detValue M (n j) (t j) := by
    intro j
    obtain ⟨hup, hlow⟩ := hreg j
    obtain ⟨hmge, hmlt, hmn, hapos, htK, htm⟩ := st5_regime M k hk (n j) (t j) hup hlow
    rw [st5_detValue M k hk (n j) (t j) hup hlow]
    have hmnR : (GVRPricing.StoppingTime.stM M k (n j) (t j) : ℝ) ≤ n j := by exact_mod_cast hmn
    nlinarith
  have hn : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun j => (hreg j).2.le) (ht.const_mul_atTop hl1pos)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε * M.pN k / (4 * M.pN (k+1)) with hδdef
  have hδ : 0 < δ := by positivity
  set C := M.pN (k+1) * (2 * st5V / δ ^ 2 + 2) with hCdef
  have hC : 0 ≤ C := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_atTop.1 hn) (2 * C / (ε * M.pN k) + 1))
  refine ⟨N, fun j hj => ?_⟩
  have hnj := hN j hj
  have hnpos : 0 < (n j : ℝ) := by
    have : 0 ≤ 2 * C / (ε * M.pN k) := by positivity
    linarith
  have hDpos : 0 < detValue M (n j) (t j) := lt_of_lt_of_le (by positivity) (hD j)
  rw [Real.dist_eq, div_sub_one hDpos.ne', abs_div, abs_of_pos hDpos, div_lt_iff₀ hDpos]
  have e : 2 * M.pN (k+1) * δ * n j = ε * M.pN k * n j / 2 := by
    rw [hδdef]; field_simp; ring
  have hC2 : C < ε * M.pN k * n j / 2 := by
    have h1 : 2 * C / (ε * M.pN k) < n j := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  have h3 := hkey δ hδ j
  have h4 := mul_le_mul_of_nonneg_left (hD j) hε.le
  nlinarith
