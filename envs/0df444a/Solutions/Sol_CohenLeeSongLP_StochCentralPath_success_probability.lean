-- Prove2me | solution 1 for CohenLeeSongLP.StochCentralPath.success_probability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T04:15:08.45367+00:00
-- url     : https://prove2.me/submissions/49541c41-ed1d-474a-b24c-1613493acdc5

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_StochasticStep

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace CohenLeeSongLP.StochCentralPath.L47

lemma coordLaw_univ (p a : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) : coordLaw p a Set.univ = 1 := by
  simp only [coordLaw, Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_def,
    smul_eq_mul, mul_one]
  rw [← ENNReal.coe_add, ← Real.toNNReal_add hp0.le (by linarith)]
  simp

lemma coordLaw_isProb (p a : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (coordLaw p a) := ⟨coordLaw_univ p a hp0 hp1⟩

lemma integral_coordLaw (p a : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (f : ℝ → ℝ) :
    ∫ y, f y ∂(coordLaw p a) = p * f (a / p) + (1 - p) * f 0 := by
  unfold coordLaw
  rw [integral_add_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_dirac, integral_dirac]
  · simp [NNReal.smul_def, Real.coe_toNNReal _ hp0.le, Real.coe_toNNReal _ (by linarith : 0 ≤ 1 - p)]
  · exact (integrable_dirac enorm_lt_top).smul_measure_nnreal
  · exact (integrable_dirac enorm_lt_top).smul_measure_nnreal

lemma coordLaw_dev (p a B : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hB : 0 ≤ B)
    (hpB : p < 1 → |a| / p ≤ B) :
    coordLaw p a {y | B < |y - (if p = 1 then a else 0)|} = 0 := by
  unfold coordLaw
  have hm : MeasurableSet {y : ℝ | B < |y - (if p = 1 then a else 0)|} :=
    measurableSet_lt measurable_const
      (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hm,
    Measure.dirac_apply' _ hm]
  rcases eq_or_lt_of_le hp1 with h1 | h1
  · subst h1
    have hA : a / 1 ∉ {y : ℝ | B < |y - (if (1:ℝ) = 1 then a else 0)|} := by
      intro h; simp at h; linarith
    rw [Set.indicator_of_notMem hA]; simp
  · have hne : p ≠ 1 := h1.ne
    have hA : a / p ∉ {y : ℝ | B < |y - (if p = 1 then a else 0)|} := by
      simp only [Set.mem_setOf_eq, if_neg hne, sub_zero, not_lt, abs_div, abs_of_pos hp0]
      exact hpB h1
    have hZ : (0:ℝ) ∉ {y : ℝ | B < |y - (if p = 1 then a else 0)|} := by
      simp only [Set.mem_setOf_eq, if_neg hne, sub_zero, abs_zero, not_lt]; exact hB
    rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hZ]; simp

lemma integral_coord {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ δ, f (δ i) ∂(Measure.pi μs) = ∫ y, f y ∂(μs i) := by
  have := integral_map (μ := Measure.pi μs) (measurable_pi_apply i).aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [(measurePreserving_eval μs i).map_eq] at this
  exact this.symm

lemma ae_coord_dev {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (B m : ℝ) (h : μs i {y | B < |y - m|} = 0) :
    ∀ᵐ δ ∂(Measure.pi μs), |δ i - m| ≤ B := by
  rw [ae_iff]
  have hm : MeasurableSet {y : ℝ | B < |y - m|} :=
    measurableSet_lt measurable_const
      (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
  have := (measurePreserving_eval μs i).measure_preimage hm.nullMeasurableSet
  simp only [not_le]
  rw [show {a : Fin n → ℝ | B < |a i - m|} = Function.eval i ⁻¹' {y | B < |y - m|} from rfl,
    this, h]

lemma subG_mono {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}
    {c c' : NNReal} (h : HasSubgaussianMGF X c μ) (hc : c ≤ c') : HasSubgaussianMGF X c' μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.2 (by
    have : (c:ℝ) ≤ c' := by exact_mod_cast hc
    gcongr))

/-- Hoeffding for a linear functional of the product of two-point laws. -/
lemma hoeffding_lin {n : ℕ} (p a : Fin n → ℝ) (hp0 : ∀ j, 0 < p j) (hp1 : ∀ j, p j ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (hpB : ∀ j, p j < 1 → |a j| / p j ≤ B)
    (c : Fin n → ℝ) (C : ℝ) (hC : B ^ 2 * ∑ j, c j ^ 2 ≤ C) (lam : ℝ) (hlam : 0 ≤ lam) :
    (Measure.pi fun j => coordLaw (p j) (a j)).real
      {δ | lam ≤ ∑ j, c j * δ j - ∑ j, c j * a j} ≤ Real.exp (-lam ^ 2 / (2 * C)) := by
  haveI : ∀ j, IsProbabilityMeasure (coordLaw (p j) (a j)) :=
    fun j => coordLaw_isProb _ _ (hp0 j) (hp1 j)
  set μs : Fin n → Measure ℝ := fun j => coordLaw (p j) (a j) with hμs
  let m : Fin n → ℝ := fun j => if p j = 1 then a j else 0
  let g : Fin n → ℝ → ℝ := fun j y => c j * (y - a j)
  have hgm : ∀ j, Measurable (g j) := fun j => by fun_prop
  have hind : iIndepFun (fun j (δ : Fin n → ℝ) => g j (δ j)) (Measure.pi μs) :=
    iIndepFun_pi (fun j => (hgm j).aemeasurable)
  have hsub : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (fun δ : Fin n → ℝ => g j (δ j))
        ((‖(c j * (m j - a j) + |c j| * B) - (c j * (m j - a j) - |c j| * B)‖₊ / 2) ^ 2)
        (Measure.pi μs) := by
    intro j _
    apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    · exact ((hgm j).comp (measurable_pi_apply j)).aemeasurable
    · have h := ae_coord_dev μs j B (m j)
        (coordLaw_dev (p j) (a j) B (hp0 j) (hp1 j) hB (hpB j))
      filter_upwards [h] with δ hδ
      have h2 : |c j * (δ j - m j)| ≤ |c j| * B := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
      rw [abs_le] at h2
      have e : g j (δ j) = c j * (δ j - m j) + c j * (m j - a j) := by simp only [g]; ring
      rw [e]
      constructor <;> linarith [h2.1, h2.2]
    · rw [integral_coord μs j (g j) (hgm j), hμs]
      dsimp only
      rw [integral_coordLaw _ _ (hp0 j) (hp1 j)]
      simp only [g]
      have := (hp0 j).ne'
      field_simp
      ring
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind hsub
  have hval : ∀ j, (((‖(c j * (m j - a j) + |c j| * B) - (c j * (m j - a j) - |c j| * B)‖₊ / 2)
      ^ 2 : NNReal) : ℝ) = c j ^ 2 * B ^ 2 := by
    intro j
    push_cast
    rw [Real.norm_eq_abs,
      show c j * (m j - a j) + |c j| * B - (c j * (m j - a j) - |c j| * B) = 2 * (|c j| * B) by
        ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_mul, abs_abs, abs_of_nonneg hB]
    rw [show 2 * (|c j| * B) / 2 = |c j| * B by ring, mul_pow, sq_abs]
  have hC0 : 0 ≤ C := le_trans (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)) hC
  have hle : ∑ j ∈ (Finset.univ : Finset (Fin n)),
      ((‖(c j * (m j - a j) + |c j| * B) - (c j * (m j - a j) - |c j| * B)‖₊ / 2) ^ 2)
      ≤ C.toNNReal := by
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, Real.coe_toNNReal _ hC0]
    simp_rw [hval]
    calc ∑ j, c j ^ 2 * B ^ 2 = B ^ 2 * ∑ j, c j ^ 2 := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ C := hC
  have hfin := (subG_mono hsum hle).measure_ge_le hlam
  rw [Real.coe_toNNReal _ hC0] at hfin
  have hset : {δ : Fin n → ℝ | lam ≤ ∑ j, c j * δ j - ∑ j, c j * a j} =
      {ω | lam ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)), g j (ω j)} := by
    ext δ
    simp only [Set.mem_setOf_eq, g, mul_sub, Finset.sum_sub_distrib]
  rw [hset]
  exact hfin


lemma one_lt_log {n : ℕ} (hn : 10 ≤ n) : 1 < Real.log n := by
  have h10 : (10:ℝ) ≤ n := by exact_mod_cast hn
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log n := Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

lemma abs_sum_mul_le {n : ℕ} (g w : Fin n → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∑ i, w i ^ 2 ≤ W ^ 2) : |∑ i, g i * w i| ≤ norm2 g * W := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g w
  have h1 : (∑ i, g i * w i) ^ 2 ≤ (∑ i, g i ^ 2) * W ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_left hw (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have h2 := Real.abs_le_sqrt h1
  rwa [Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _), Real.sqrt_sq hW] at h2

lemma sampleProb_pos {n : ℕ} (hn : 0 < n) (k : ℝ) (hk : 0 < k) (δμ : Fin n → ℝ) (i : Fin n) :
    0 < sampleProb k δμ i ∧ sampleProb k δμ i ≤ 1 := by
  unfold sampleProb
  refine ⟨lt_min one_pos ?_, min_le_left _ _⟩
  have : 0 ≤ δμ i ^ 2 / ∑ l, δμ l ^ 2 :=
    div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun l _ => sq_nonneg _)
  have : (0:ℝ) < 1 / (n : ℝ) := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  positivity

lemma inv_mul_mul_inv {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : M⁻¹ * M * M⁻¹ = M⁻¹ := by
  by_cases h : IsUnit M.det
  · rw [Matrix.nonsing_inv_mul M h, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit M h]; simp

lemma proj_idem {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin d) (Fin d) ℝ)
    (hCt : C.transpose = C) (hCMC : C * (B * B.transpose) * C = C) :
    (B.transpose * C * B).transpose * (B.transpose * C * B) = B.transpose * C * B := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hCt]
  calc B.transpose * (C * B) * (B.transpose * C * B)
      = B.transpose * (C * (B * B.transpose) * C) * B := by simp only [Matrix.mul_assoc]
    _ = B.transpose * C * B := by rw [hCMC]

/-- Rows of `P̄` and of `I - P̄` have squared Euclidean norm at most `1`. -/
lemma proj_rows {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (xb sb : Fin n → ℝ)
    (hx : ∀ i, 0 < xb i) (hs : ∀ i, 0 < sb i) (i : Fin n) :
    ∑ j, projBar A xb sb i j ^ 2 ≤ 1 ∧
      ∑ j, ((1 : Matrix (Fin n) (Fin n) ℝ) i j - projBar A xb sb i j) ^ 2 ≤ 1 := by
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin n) ℝ,
      D = Matrix.diagonal (fun i => Real.sqrt (xb i / sb i)) := ⟨_, rfl⟩
  have hDt : D.transpose = D := by rw [hD]; exact Matrix.diagonal_transpose _
  have hW : Matrix.diagonal (fun i => xb i / sb i) = D * D := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [Real.mul_self_sqrt (div_pos (hx i) (hs i)).le]
  have hP : projBar A xb sb = (A * D).transpose * ((A * D) * (A * D).transpose)⁻¹ * (A * D) := by
    unfold projBar
    rw [hW, ← hD, Matrix.transpose_mul, hDt]
    simp only [Matrix.mul_assoc]
  have hCt : (((A * D) * (A * D).transpose)⁻¹).transpose = ((A * D) * (A * D).transpose)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPP : (projBar A xb sb).transpose * projBar A xb sb = projBar A xb sb := by
    rw [hP]; exact proj_idem _ _ hCt (inv_mul_mul_inv _)
  obtain ⟨P, hPdef⟩ : ∃ P, P = projBar A xb sb := ⟨_, rfl⟩
  rw [← hPdef] at hPP ⊢
  have hsym : P.transpose = P := by
    conv_lhs => rw [← hPP]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hPP]
  have hrow : ∑ j, P i j ^ 2 = P i i := by
    have := congrFun (congrFun hPP i) i
    rw [Matrix.mul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 := congrFun (congrFun hsym j) i
    rw [Matrix.transpose_apply] at h2 ⊢
    rw [sq, ← h2]
  have h0 : 0 ≤ P i i := by rw [← hrow]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hii : P i i ≤ 1 := by
    have h1 : P i i ^ 2 ≤ ∑ j, P i j ^ 2 :=
      Finset.single_le_sum (f := fun j => P i j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hrow] at h1
    nlinarith [sq_nonneg (P i i)]
  refine ⟨hrow ▸ hii, ?_⟩
  have hsplit : ∑ j, ((1 : Matrix (Fin n) (Fin n) ℝ) i j - P i j) ^ 2 =
      ∑ j, P i j ^ 2 + ∑ j, (if i = j then 1 - 2 * P i j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.one_apply]
    split_ifs <;> ring
  rw [hsplit, hrow, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  linarith

/-- `|a_j|/p_j ≤ ‖a‖ √n /(2k)` when `p_j < 1`. -/
lemma ratio_bound {n : ℕ} (hn : 0 < n) (k : ℝ) (hk : 0 < k) (a : Fin n → ℝ) (N : ℝ)
    (hN : norm2 a ≤ N) (j : Fin n) (hp : sampleProb k a j < 1) :
    |a j| / sampleProb k a j ≤ N * Real.sqrt n / (2 * k) := by
  have hpos := (sampleProb_pos hn k hk a j).1
  have hpeq : sampleProb k a j = k * (a j ^ 2 / ∑ l, a l ^ 2 + 1 / (n:ℝ)) := by
    unfold sampleProb at hp ⊢
    rcases min_lt_iff.1 hp with h | h
    · exact absurd h (lt_irrefl 1)
    · exact min_eq_right h.le
  have hS0 : 0 ≤ ∑ l, a l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hG2 : norm2 a ^ 2 = ∑ l, a l ^ 2 := by unfold norm2; exact Real.sq_sqrt hS0
  have hG0 : 0 ≤ norm2 a := Real.sqrt_nonneg _
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hnR
  have hq2 : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
  rw [div_le_div_iff₀ hpos (by positivity), hpeq]
  set G := norm2 a with hG
  set q := Real.sqrt (n:ℝ) with hq
  set S := ∑ l, a l ^ 2 with hS
  have hN0 : 0 ≤ N := hG0.trans hN
  rcases eq_or_lt_of_le hG0 with hG00 | hGpos
  · have hS00 : S = 0 := by rw [← hG2, ← hG00]; ring
    have haj : a j = 0 := by
      have : a j ^ 2 ≤ S := Finset.single_le_sum (f := fun l => a l ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ j)
      rw [hS00] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
    rw [haj, abs_zero, zero_mul]
    have : 0 ≤ (0:ℝ) ^ 2 / S + 1 / (n:ℝ) := by positivity
    positivity
  · have key : 2 * |a j| ≤ (a j ^ 2 / S + 1 / (n:ℝ)) * G * q := by
      rw [← hG2, ← hq2]
      have e : (a j ^ 2 / G ^ 2 + 1 / q ^ 2) * G * q = (a j ^ 2 * q ^ 2 + G ^ 2) / (G * q) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|a j| * q - G), sq_abs (a j)]
    have hu : 0 ≤ (a j ^ 2 / S + 1 / (n:ℝ)) * q := by positivity
    have h2 : (a j ^ 2 / S + 1 / (n:ℝ)) * G * q ≤ (a j ^ 2 / S + 1 / (n:ℝ)) * N * q := by
      have := mul_le_mul_of_nonneg_left hN hu
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (key.trans h2) hk.le]

lemma xbar_sbar {n : ℕ} (x s v δμ : Fin n → ℝ) (t k ε εmp : ℝ)
    (hAs : Assumption41 x s t v δμ k ε εmp) :
    (∀ i, 0 < xbar x s v i) ∧ (∀ i, 0 < sbar x s v i) ∧
      ∀ i, xbar x s v i * sbar x s v i = x i * s i := by
  obtain ⟨hx, hs, -, -, hεmp, -, hw, -, -, -, -, -⟩ := hAs
  have hxs : ∀ i, 0 < x i / s i := fun i => div_pos (hx i) (hs i)
  have hv : ∀ i, 0 < v i := fun i => by
    have h1 := (hw i).2
    dsimp only at h1
    by_contra hcon
    push Not at hcon
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 1 + εmp) hcon
    linarith [hxs i]
  refine ⟨fun i => mul_pos (hx i) (Real.sqrt_pos.2 (div_pos (hv i) (hxs i))),
    fun i => mul_pos (hs i) (Real.sqrt_pos.2 (div_pos (hxs i) (hv i))), fun i => ?_⟩
  unfold xbar sbar
  have h1 := div_pos (hv i) (hxs i)
  rw [show x i * Real.sqrt (v i / (x i / s i)) * (s i * Real.sqrt (x i / s i / v i)) =
    x i * s i * (Real.sqrt (v i / (x i / s i)) * Real.sqrt (x i / s i / v i)) by ring,
    ← Real.sqrt_mul h1.le]
  have h3 : v i / (x i / s i) * (x i / s i / v i) = 1 := by
    have := (hv i).ne'; have := (hxs i).ne'; have := (hx i).ne'; have := (hs i).ne'
    field_simp
  rw [h3, Real.sqrt_one, mul_one]

/-- `s̄/s ≤ 2` and `x̄/x ≤ 2`. -/
lemma bar_ratio {n : ℕ} (x s v δμ : Fin n → ℝ) (t k ε εmp : ℝ)
    (hAs : Assumption41 x s t v δμ k ε εmp) (i : Fin n) :
    sbar x s v i / s i ≤ 2 ∧ xbar x s v i / x i ≤ 2 := by
  obtain ⟨hx, hs, -, -, hεmp, hεmp1, hw, -, -, -, -, -⟩ := hAs
  have hw0 : 0 < x i / s i := div_pos (hx i) (hs i)
  obtain ⟨h1, h2⟩ := hw i
  have hv : 0 < v i := by nlinarith
  have hsq : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  constructor
  · unfold sbar
    rw [show s i * Real.sqrt (x i / s i / v i) / s i = Real.sqrt (x i / s i / v i) by
      have := (hs i).ne'; field_simp]
    have : x i / s i / v i ≤ 4 := by
      rw [div_le_iff₀ hv]; nlinarith
    calc Real.sqrt (x i / s i / v i) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt this
      _ = 2 := hsq
  · unfold xbar
    rw [show x i * Real.sqrt (v i / (x i / s i)) / x i = Real.sqrt (v i / (x i / s i)) by
      have := (hx i).ne'; field_simp]
    have : v i / (x i / s i) ≤ 4 := by
      rw [div_le_iff₀ hw0]; nlinarith
    calc Real.sqrt (v i / (x i / s i)) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt this
      _ = 2 := hsq

lemma scale_bound (a b c u : ℝ) (hb : 0 < b) (hc : 0 < c) (h1 : |a / b| ≤ u)
    (h2 : b / c ≤ 2) : |a / c| ≤ 2 * u := by
  have e : a / c = a / b * (b / c) := by field_simp
  rw [e, abs_mul, abs_of_pos (div_pos hb hc)]
  have := abs_nonneg (a / b)
  nlinarith

lemma stepS_lin {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ)
    (hxb : ∀ i, 0 < xbar x s v i) (hsb : ∀ i, 0 < sbar x s v i) (i : Fin n) :
    stepS A x s v δ i / sbar x s v i = ∑ j, projBar A (xbar x s v) (sbar x s v) i j /
      (Real.sqrt (xbar x s v j * sbar x s v j) * Real.sqrt (xbar x s v i * sbar x s v i)) * δ j := by
  have hR : ∀ j, 0 < Real.sqrt (xbar x s v j * sbar x s v j) :=
    fun j => Real.sqrt_pos.2 (mul_pos (hxb j) (hsb j))
  unfold stepS pMu
  rw [Matrix.mulVec, dotProduct]
  have := (hsb i).ne'
  have := (hR i).ne'
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := (hR j).ne'
  field_simp

lemma stepX_lin {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ)
    (hxb : ∀ i, 0 < xbar x s v i) (hsb : ∀ i, 0 < sbar x s v i) (i : Fin n) :
    stepX A x s v δ i / xbar x s v i = ∑ j, ((1 : Matrix (Fin n) (Fin n) ℝ) i j -
      projBar A (xbar x s v) (sbar x s v) i j) /
      (Real.sqrt (xbar x s v j * sbar x s v j) * Real.sqrt (xbar x s v i * sbar x s v i)) * δ j := by
  have hR : ∀ j, 0 < Real.sqrt (xbar x s v j * sbar x s v j) :=
    fun j => Real.sqrt_pos.2 (mul_pos (hxb j) (hsb j))
  have hS := stepS_lin A x s v δ hxb hsb i
  have hsplit : ∀ j, ((1 : Matrix (Fin n) (Fin n) ℝ) i j -
      projBar A (xbar x s v) (sbar x s v) i j) /
      (Real.sqrt (xbar x s v j * sbar x s v j) * Real.sqrt (xbar x s v i * sbar x s v i)) * δ j =
      (if i = j then δ j / (Real.sqrt (xbar x s v j * sbar x s v j) *
        Real.sqrt (xbar x s v i * sbar x s v i)) else 0) -
      projBar A (xbar x s v) (sbar x s v) i j /
      (Real.sqrt (xbar x s v j * sbar x s v j) * Real.sqrt (xbar x s v i * sbar x s v i)) * δ j := by
    intro j
    rw [Matrix.one_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_sub_distrib, ← hS, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  have hii : Real.sqrt (xbar x s v i * sbar x s v i) * Real.sqrt (xbar x s v i * sbar x s v i) =
      xbar x s v i * sbar x s v i := Real.mul_self_sqrt (mul_pos (hxb i) (hsb i)).le
  rw [hii]
  unfold stepX stepS
  have := (hsb i).ne'
  have := (hxb i).ne'
  have := (hR i).ne'
  field_simp

lemma step_sum {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ)
    (hxb : ∀ i, 0 < xbar x s v i) (hsb : ∀ i, 0 < sbar x s v i) (i : Fin n) :
    δ i / (xbar x s v i * sbar x s v i) =
      stepX A x s v δ i / xbar x s v i + stepS A x s v δ i / sbar x s v i := by
  have hR : 0 < Real.sqrt (xbar x s v i * sbar x s v i) :=
    Real.sqrt_pos.2 (mul_pos (hxb i) (hsb i))
  unfold stepX stepS
  have := (hsb i).ne'
  have := (hxb i).ne'
  have := hR.ne'
  field_simp
  ring

lemma coef_bound {n : ℕ} (q R : Fin n → ℝ) (Ri t : ℝ) (ht : 0 < t)
    (hR : ∀ j, 0.9 * t ≤ R j ^ 2) (hRi : 0.9 * t ≤ Ri ^ 2) (hq : ∑ j, q j ^ 2 ≤ 1) :
    ∑ j, (q j / (R j * Ri)) ^ 2 ≤ (1 / (0.9 * t)) ^ 2 := by
  have h9 : 0 < 0.9 * t := by positivity
  calc ∑ j, (q j / (R j * Ri)) ^ 2 ≤ ∑ j, q j ^ 2 / (0.9 * t * (0.9 * t)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [div_pow, mul_pow]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (mul_le_mul (hR j) hRi h9.le (sq_nonneg _))
    _ = (∑ j, q j ^ 2) / (0.9 * t * (0.9 * t)) := by rw [Finset.sum_div]
    _ ≤ 1 / (0.9 * t * (0.9 * t)) := div_le_div_of_nonneg_right hq (by positivity)
    _ = (1 / (0.9 * t)) ^ 2 := by ring

lemma final_real (Y : ℝ) (hY : 100 ≤ Y) (n : ℝ) (hn : 0 ≤ n) :
    4 * n * Real.exp (-(0.00013122 * Y ^ 2)) ≤ 2 * n * Real.exp (-(0.003 * Y)) := by
  have h1 : 2 * Real.exp (-(0.00013122 * Y ^ 2)) ≤ Real.exp (-(0.003 * Y)) := by
    have h2 : 2 * Real.exp (-(0.00013122 * Y ^ 2)) ≤
        Real.exp 1 * Real.exp (-(0.00013122 * Y ^ 2)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_gt_d9]) (Real.exp_pos _).le
    rw [← Real.exp_add] at h2
    exact h2.trans (Real.exp_le_exp.2 (by nlinarith))
  nlinarith [mul_le_mul_of_nonneg_left h1 hn]

lemma prob_ge {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (G Bad : Set α) (h : ∀ δ, δ ∉ Bad → δ ∈ G) (r : ℝ) (hr : 0 ≤ r)
    (hB : μ Bad ≤ ENNReal.ofReal r) (y : ℝ) (hy : r ≤ y) : ENNReal.ofReal (1 - y) ≤ μ G := by
  have h1 : (1 : ENNReal) ≤ μ G + μ Bad := by
    rw [← measure_univ (μ := μ)]
    calc μ Set.univ ≤ μ (G ∪ Bad) := measure_mono (fun δ _ => by
          by_cases hd : δ ∈ Bad
          · exact Or.inr hd
          · exact Or.inl (h δ hd))
      _ ≤ μ G + μ Bad := measure_union_le _ _
  calc ENNReal.ofReal (1 - y) ≤ ENNReal.ofReal (1 - r) := ENNReal.ofReal_le_ofReal (by linarith)
    _ = 1 - ENNReal.ofReal r := by rw [ENNReal.ofReal_sub _ hr, ENNReal.ofReal_one]
    _ ≤ 1 - μ Bad := tsub_le_tsub_left hB _
    _ ≤ μ G := tsub_le_iff_right.2 h1

end CohenLeeSongLP.StochCentralPath.L47

open CohenLeeSongLP.StochCentralPath MeasureTheory ProbabilityTheory in
theorem solution {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : A.rank = d) (x s v δμ : Fin n → ℝ) (t kSamp ε εmp : ℝ)
    (hAs : Assumption41 x s t v δμ kSamp ε εmp) :
    IsProbabilityMeasure (sampleLaw kSamp δμ) ∧
    ENNReal.ofReal (1 - 2 * n * Real.exp (-(0.003 * kSamp / (ε * Real.sqrt n * Real.log n))))
      ≤ sampleLaw kSamp δμ {δ | ∀ i,
          |stepS A x s v δ i / sbar x s v i| ≤ 0.01 / Real.log n ∧
          |stepS A x s v δ i / s i| ≤ 0.02 / Real.log n ∧
          |stepX A x s v δ i / xbar x s v i| ≤ 0.01 / Real.log n ∧
          |stepX A x s v δ i / x i| ≤ 0.02 / Real.log n ∧
          |δ i / (x i * s i)| ≤ 0.02 / Real.log n} := by
  have hAs' := hAs
  obtain ⟨hx, hs, ht, hxsA, hεmp0, hεmp1, hw, hε0, hεle, hδn, hk0, hkge⟩ := hAs'
  have hn0 : 0 < n := by omega
  have hP := L47.sampleProb_pos hn0 kSamp hk0 δμ
  haveI : ∀ j, IsProbabilityMeasure (coordLaw (sampleProb kSamp δμ j) (δμ j)) :=
    fun j => L47.coordLaw_isProb _ _ (hP j).1 (hP j).2
  have hprob : IsProbabilityMeasure (sampleLaw kSamp δμ) := by unfold sampleLaw; infer_instance
  refine ⟨hprob, ?_⟩
  obtain ⟨hxb, hsb, hprod⟩ := L47.xbar_sbar x s v δμ t kSamp ε εmp hAs
  have hL : 1 < Real.log n := L47.one_lt_log hn
  set L := Real.log (n:ℝ) with hLdef
  have hL0 : 0 < L := by linarith
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  set q := Real.sqrt (n:ℝ) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hnR
  set P := projBar A (xbar x s v) (sbar x s v) with hPdef
  set R : Fin n → ℝ := fun j => Real.sqrt (xbar x s v j * sbar x s v j) with hRdef
  have hRlow : ∀ j, 0.9 * t ≤ R j ^ 2 := by
    intro j
    simp only [hRdef]
    rw [Real.sq_sqrt (mul_pos (hxb j) (hsb j)).le, hprod j]
    have := (hxsA j).1
    linarith
  let cS : Fin n → Fin n → ℝ := fun i j => P i j / (R j * R i)
  let cX : Fin n → Fin n → ℝ := fun i j =>
    ((1 : Matrix (Fin n) (Fin n) ℝ) i j - P i j) / (R j * R i)
  have hW0 : 0 ≤ 1 / (0.9 * t) := div_nonneg zero_le_one (by linarith)
  have bS : ∀ i, ∑ j, cS i j ^ 2 ≤ (1 / (0.9 * t)) ^ 2 := fun i =>
    L47.coef_bound (fun j => P i j) R (R i) t ht hRlow (hRlow i) (L47.proj_rows A _ _ hxb hsb i).1
  have bX : ∀ i, ∑ j, cX i j ^ 2 ≤ (1 / (0.9 * t)) ^ 2 := fun i =>
    L47.coef_bound (fun j => (1 : Matrix (Fin n) (Fin n) ℝ) i j - P i j) R (R i) t ht hRlow
      (hRlow i) (L47.proj_rows A _ _ hxb hsb i).2
  have hmean : ∀ c : Fin n → ℝ, ∑ j, c j ^ 2 ≤ (1 / (0.9 * t)) ^ 2 →
      |∑ j, c j * δμ j| ≤ 0.001 / L := by
    intro c hc
    have h1 := L47.abs_sum_mul_le δμ c (1 / (0.9 * t)) hW0 hc
    rw [show ∑ j, c j * δμ j = ∑ j, δμ j * c j from Finset.sum_congr rfl fun j _ => mul_comm _ _]
    refine h1.trans ?_
    have h2 : norm2 δμ * (1 / (0.9 * t)) ≤ ε * t * (1 / (0.9 * t)) :=
      mul_le_mul_of_nonneg_right hδn hW0
    have h3 : ε * t * (1 / (0.9 * t)) = ε / 0.9 := by field_simp
    have h4 : ε / 0.9 ≤ 0.001 / L := by
      rw [div_le_div_iff₀ (by norm_num) hL0]
      have : ε * (40000 * L) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hεle
      nlinarith
    linarith
  set B := ε * t * q / (2 * kSamp) with hBdef
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg (mul_nonneg hε0.le ht.le) hq0.le) (by linarith)
  set C := ε ^ 2 * q ^ 2 / (3.24 * kSamp ^ 2) with hCdef
  have hBC : ∀ c : Fin n → ℝ, ∑ j, c j ^ 2 ≤ (1 / (0.9 * t)) ^ 2 →
      B ^ 2 * ∑ j, c j ^ 2 ≤ C := by
    intro c hc
    have ht0 := ht.ne'
    have hk0' := hk0.ne'
    calc B ^ 2 * ∑ j, c j ^ 2 ≤ B ^ 2 * (1 / (0.9 * t)) ^ 2 :=
          mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      _ = C := by rw [hBdef, hCdef]; field_simp; ring
  have hpB : ∀ j, sampleProb kSamp δμ j < 1 → |δμ j| / sampleProb kSamp δμ j ≤ B :=
    fun j hj => L47.ratio_bound hn0 kSamp hk0 δμ (ε * t) hδn j hj
  set lam := 0.009 / L with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (by norm_num) hL0.le
  set e := Real.exp (-lam ^ 2 / (2 * C)) with he
  have hoe : ∀ c : Fin n → ℝ, ∑ j, c j ^ 2 ≤ (1 / (0.9 * t)) ^ 2 →
      sampleLaw kSamp δμ {δ | lam ≤ ∑ j, c j * δ j - ∑ j, c j * δμ j} ≤ ENNReal.ofReal e := by
    intro c hc
    have h := L47.hoeffding_lin (fun j => sampleProb kSamp δμ j) δμ (fun j => (hP j).1)
      (fun j => (hP j).2) B hB0 hpB c C (hBC c hc) lam hlam0
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h
  have hneg : ∀ c : Fin n → ℝ, ∑ j, c j ^ 2 ≤ (1 / (0.9 * t)) ^ 2 →
      ∑ j, (fun j => -c j) j ^ 2 ≤ (1 / (0.9 * t)) ^ 2 := by
    intro c hc; simpa only [neg_sq] using hc
  let U : Fin n → Set (Fin n → ℝ) := fun i =>
    ({δ | lam ≤ ∑ j, cS i j * δ j - ∑ j, cS i j * δμ j} ∪
      {δ | lam ≤ ∑ j, (fun j => -cS i j) j * δ j - ∑ j, (fun j => -cS i j) j * δμ j}) ∪
    ({δ | lam ≤ ∑ j, cX i j * δ j - ∑ j, cX i j * δμ j} ∪
      {δ | lam ≤ ∑ j, (fun j => -cX i j) j * δ j - ∑ j, (fun j => -cX i j) j * δμ j})
  have hU : ∀ i, sampleLaw kSamp δμ (U i) ≤ 4 * ENNReal.ofReal e := by
    intro i
    calc sampleLaw kSamp δμ (U i) ≤ (ENNReal.ofReal e + ENNReal.ofReal e) +
          (ENNReal.ofReal e + ENNReal.ofReal e) :=
        (measure_union_le _ _).trans (add_le_add
          ((measure_union_le _ _).trans (add_le_add (hoe _ (bS i)) (hoe _ (hneg _ (bS i)))))
          ((measure_union_le _ _).trans (add_le_add (hoe _ (bX i)) (hoe _ (hneg _ (bX i))))))
      _ = 4 * ENNReal.ofReal e := by ring
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hBad : sampleLaw kSamp δμ (⋃ i, U i) ≤ ENNReal.ofReal (4 * n * e) := by
    calc sampleLaw kSamp δμ (⋃ i, U i) ≤ ∑ i, sampleLaw kSamp δμ (U i) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin n, 4 * ENNReal.ofReal e := Finset.sum_le_sum fun i _ => hU i
      _ = ENNReal.ofReal (4 * n * e) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
        ring
  have hK : 0 < ε * q * L := by positivity
  set Y := kSamp / (ε * q * L) with hYdef
  have hY : 100 ≤ Y := by
    rw [hYdef, le_div_iff₀ hK]
    have : 100 * (ε * q * L) ≤ 1000 * ε * q * L ^ 2 / εmp := by
      rw [le_div_iff₀ hεmp0]
      nlinarith [mul_le_mul_of_nonneg_left hεmp1 hK.le, mul_pos hK (by linarith : (0:ℝ) < L - 1)]
    linarith
  have hexp : -lam ^ 2 / (2 * C) = -(0.00013122 * Y ^ 2) := by
    have hq2 : q ≠ 0 := hq0.ne'
    have hL2 : L ≠ 0 := hL0.ne'
    have hε2 : ε ≠ 0 := hε0.ne'
    have hk2 : kSamp ≠ 0 := hk0.ne'
    rw [hlam, hCdef, hYdef]
    field_simp
    ring
  refine L47.prob_ge (sampleLaw kSamp δμ) _ (⋃ i, U i) ?_ (4 * n * e) (by positivity) hBad _ ?_
  · intro δ hδ
    simp only [U, Set.mem_iUnion, not_exists, Set.mem_union, Set.mem_setOf_eq, not_or,
      not_le] at hδ
    intro i
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hδ i
    simp only [neg_mul, Finset.sum_neg_distrib] at h2 h4
    have eS : stepS A x s v δ i / sbar x s v i = ∑ j, cS i j * δ j :=
      L47.stepS_lin A x s v δ hxb hsb i
    have eX : stepX A x s v δ i / xbar x s v i = ∑ j, cX i j * δ j :=
      L47.stepX_lin A x s v δ hxb hsb i
    have hm1 := abs_le.1 (hmean (cS i) (bS i))
    have hm2 := abs_le.1 (hmean (cX i) (bX i))
    have hsplit : (0.01:ℝ) / L = 0.009 / L + 0.001 / L := by ring
    have bS1 : |stepS A x s v δ i / sbar x s v i| ≤ 0.01 / L := by
      rw [eS, abs_le, hsplit]
      constructor <;> linarith [hm1.1, hm1.2]
    have bX1 : |stepX A x s v δ i / xbar x s v i| ≤ 0.01 / L := by
      rw [eX, abs_le, hsplit]
      constructor <;> linarith [hm2.1, hm2.2]
    have hbr := L47.bar_ratio x s v δμ t kSamp ε εmp hAs i
    have h02 : (0.02:ℝ) / L = 2 * (0.01 / L) := by ring
    have bS2 : |stepS A x s v δ i / s i| ≤ 0.02 / L := by
      rw [h02]
      exact L47.scale_bound _ _ _ _ (hsb i) (hs i) bS1 hbr.1
    have bX2 : |stepX A x s v δ i / x i| ≤ 0.02 / L := by
      rw [h02]
      exact L47.scale_bound _ _ _ _ (hxb i) (hx i) bX1 hbr.2
    have b5 : |δ i / (x i * s i)| ≤ 0.02 / L := by
      rw [← hprod i, L47.step_sum A x s v δ hxb hsb i, h02]
      rw [abs_le] at bS1 bX1 ⊢
      constructor <;> linarith [bS1.1, bS1.2, bX1.1, bX1.2]
    exact ⟨bS1, bS2, bX1, bX2, b5⟩
  · rw [he, hexp, show 0.003 * kSamp / (ε * q * L) = 0.003 * Y by rw [hYdef]; ring]
    exact L47.final_real Y hY n hnR.le
