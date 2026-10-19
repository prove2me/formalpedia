-- Prove2me | solution 2 for CohenLeeSongLP.StochCentralPath.potential_expected_decrease
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T13:51:12.008207+00:00
-- url     : https://prove2.me/submissions/4839dc9f-62ef-4cf7-afb2-63fccfe9ae68

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_Main

set_option autoImplicit false

open MeasureTheory ProbabilityTheory



namespace CohenLeeSongLP.StochCentralPath.L412

open CohenLeeSongLP.StochCentralPath

theorem L412_cosh_add_le (y u : ℝ) (hu : |u| ≤ 1) :
    Real.cosh (y + u) ≤ Real.cosh y + Real.sinh y * u + Real.cosh y * u ^ 2 := by
  have h1 : Real.exp u ≤ 1 + u + u ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le hu
    have := (abs_le.mp this).2
    linarith
  have h2 : Real.exp (-u) ≤ 1 - u + u ^ 2 := by
    have hu' : |-u| ≤ 1 := by rwa [abs_neg]
    have := Real.abs_exp_sub_one_sub_id_le hu'
    have := (abs_le.mp this).2
    nlinarith
  have hy1 : 0 < Real.exp y := Real.exp_pos y
  have hy2 : 0 < Real.exp (-y) := Real.exp_pos (-y)
  rw [Real.cosh_eq, Real.cosh_eq, Real.sinh_eq, show -(y + u) = -y + -u by ring,
    Real.exp_add, Real.exp_add]
  nlinarith [mul_le_mul_of_nonneg_left h1 hy1.le, mul_le_mul_of_nonneg_left h2 hy2.le]

theorem L412_cosh_sub_one_le (y : ℝ) : Real.cosh y - 1 ≤ |Real.sinh y| := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr h), Real.cosh_eq, Real.sinh_eq]
    have : Real.exp (-y) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [abs_of_nonpos (Real.sinh_nonpos_iff.mpr h), Real.cosh_eq, Real.sinh_eq]
    have : Real.exp y ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    linarith

end CohenLeeSongLP.StochCentralPath.L412

open CohenLeeSongLP.StochCentralPath in
theorem L412_pbp_main {n : ℕ} (hn : 10 ≤ n) (lam : ℝ) (hlam : 0 < lam)
    (r : Fin n → ℝ) :
    (∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1 / lam) →
      potential lam (fun i => r i + v i) ≤
        potential lam r + ∑ i, potentialGrad lam r i * v i + 2 * hessNormSq lam r v) ∧
    lam / Real.sqrt n * (potential lam r - n) ≤ norm2 (potentialGrad lam r) ∧
    Real.sqrt (∑ i, lam ^ 2 * Real.cosh (lam * r i) ^ 2) ≤
      lam * Real.sqrt n + norm2 (potentialGrad lam r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    unfold potential potentialGrad hessNormSq
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hu : |lam * v i| ≤ 1 := by
      rw [abs_mul, abs_of_pos hlam]
      calc lam * |v i| ≤ lam * (1 / lam) := by gcongr; exact hv i
        _ = 1 := by field_simp
    have h := CohenLeeSongLP.StochCentralPath.L412.L412_cosh_add_le (lam * r i) (lam * v i) hu
    have hc : 0 ≤ Real.cosh (lam * r i) * (lam * v i) ^ 2 :=
      mul_nonneg (Real.cosh_pos _).le (sq_nonneg _)
    have e : lam * (r i + v i) = lam * r i + lam * v i := by ring
    rw [e]
    nlinarith [h, hc]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hsum : potential lam r - n ≤ ∑ i, |Real.sinh (lam * r i)| := by
      unfold potential
      have : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      rw [this, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun i _ => CohenLeeSongLP.StochCentralPath.L412.L412_cosh_sub_one_le _
    have hcs : (∑ i, |Real.sinh (lam * r i)|) ≤
        Real.sqrt n * Real.sqrt (∑ i, Real.sinh (lam * r i) ^ 2) := by
      rw [← Real.sqrt_mul hnpos.le]
      apply Real.le_sqrt_of_sq_le
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => |Real.sinh (lam * r i)|)
      simpa [sq_abs] using this
    have hnorm : norm2 (potentialGrad lam r) = lam * Real.sqrt (∑ i, Real.sinh (lam * r i) ^ 2) := by
      unfold norm2 potentialGrad
      have : ∑ i, (lam * Real.sinh (lam * r i)) ^ 2 = lam ^ 2 * ∑ i, Real.sinh (lam * r i) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlam.le]
    rw [hnorm, div_mul_eq_mul_div, div_le_iff₀ hs]
    calc lam * (potential lam r - n) ≤ lam * (Real.sqrt n * Real.sqrt (∑ i, Real.sinh (lam * r i) ^ 2)) := by
          gcongr; exact hsum.trans hcs
      _ = _ := by ring
  · have hnorm : norm2 (potentialGrad lam r) = Real.sqrt (∑ i, (lam * Real.sinh (lam * r i)) ^ 2) := rfl
    have e : ∑ i, lam ^ 2 * Real.cosh (lam * r i) ^ 2 =
        (n : ℝ) * lam ^ 2 + ∑ i, (lam * Real.sinh (lam * r i)) ^ 2 := by
      rw [show (n : ℝ) * lam ^ 2 = ∑ _i : Fin n, lam ^ 2 by simp, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := Real.cosh_sq (lam * r i)
      nlinarith [this]
    rw [e, hnorm]
    have h1 : Real.sqrt ((n : ℝ) * lam ^ 2) = lam * Real.sqrt n := by
      rw [mul_comm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlam.le]
    rw [← h1]
    have ha : 0 ≤ (n : ℝ) * lam ^ 2 := by positivity
    have hb : 0 ≤ ∑ i, (lam * Real.sinh (lam * r i)) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg ((n : ℝ) * lam ^ 2)) (Real.sqrt_nonneg (∑ i, (lam * Real.sinh (lam * r i)) ^ 2))]





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
theorem L47_sp_main {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
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


namespace CohenLeeSongLP.StochCentralPath.L413

lemma one_lt_log {n : ℕ} (hn : 10 ≤ n) : 1 < Real.log n := by
  have h10 : (10:ℝ) ≤ n := by exact_mod_cast hn
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log n := Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

lemma sum_mul_div_norm2 {n : ℕ} (g : Fin n → ℝ) :
    ∑ i, g i * (g i / norm2 g) = norm2 g := by
  unfold norm2
  set G := Real.sqrt (∑ i, g i ^ 2) with hG
  have hsq : G ^ 2 = ∑ i, g i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases h0 : G = 0
  · rw [h0]; simp
  · have : ∑ i, g i * (g i / G) = (∑ i, g i ^ 2) / G := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← hsq]; field_simp

lemma sum_sq_div_norm2_le {n : ℕ} (g : Fin n → ℝ) :
    ∑ i, (g i / norm2 g) ^ 2 ≤ 1 := by
  unfold norm2
  set G := Real.sqrt (∑ i, g i ^ 2) with hG
  have hsq : G ^ 2 = ∑ i, g i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases h0 : G = 0
  · rw [h0]; simp
  · have : ∑ i, (g i / G) ^ 2 = (∑ i, g i ^ 2) / G ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← hsq, div_self (pow_ne_zero 2 h0)]

lemma abs_sum_mul_le {n : ℕ} (g w : Fin n → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∑ i, w i ^ 2 ≤ W ^ 2) : |∑ i, g i * w i| ≤ norm2 g * W := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g w
  have h1 : (∑ i, g i * w i) ^ 2 ≤ (∑ i, g i ^ 2) * W ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_left hw (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have h2 := Real.abs_le_sqrt h1
  rwa [Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _), Real.sqrt_sq hW] at h2

/-- The final real inequality of the proof of Lemma 4.13. -/
lemma final_ineq {n : ℕ} (hn : 10 ≤ n) (ε k Φ G M : ℝ) (hε : 0 < ε)
    (hεle : ε ≤ 1 / (40000 * Real.log n)) (hk : 40000000 * ε * Real.sqrt n * Real.log n ^ 2 ≤ k)
    (hΦn : (n : ℝ) ≤ Φ) (hG0 : 0 ≤ G) (hG : lam n / Real.sqrt n * (Φ - n) ≤ G)
    (hM : M ≤ lam n * Real.sqrt n + G)
    (S1 S2 Sh : ℝ) (hS1 : S1 ≤ -(ε / 2) * G + 0.02 * ε * G)
    (hS2 : S2 ≤ 72 * ε ^ 2 / k * Sh + lam n * M * (ε ^ 2 / 2 + 0.0008 * ε ^ 2))
    (hSh : Sh = lam n ^ 2 * Φ) :
    Φ + S1 + 2 * S2 ≤ Φ - lam n * ε / (15 * Real.sqrt n) * (Φ - 10 * n) := by
  have hL := one_lt_log hn
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
  have hlam : lam n = 40 * Real.log n := rfl
  have hlampos : 0 < lam n := by rw [hlam]; linarith
  have hle : lam n * ε ≤ 1 / 1000 := by
    rw [hlam]
    have : ε * (40000 * Real.log n) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hεle; linarith
    nlinarith
  have hkpos : 0 < k := lt_of_lt_of_le (by positivity) hk
  -- the variance term
  have hV : 72 * ε ^ 2 / k * Sh ≤ 0.00288 * (ε / Real.sqrt n) * Φ := by
    rw [hSh, div_mul_eq_mul_div, div_le_iff₀ hkpos]
    have hΦ0 : 0 ≤ Φ := by linarith
    have e1 : 72 * ε ^ 2 * (lam n ^ 2 * Φ) = 72 * 1600 * (ε * Real.log n ^ 2) * ε * Φ := by
      rw [hlam]; ring
    have e2 : 0.00288 * (ε / Real.sqrt n) * Φ * (40000000 * ε * Real.sqrt n * Real.log n ^ 2)
        = 72 * 1600 * (ε * Real.log n ^ 2) * ε * Φ := by
      field_simp; ring
    calc 72 * ε ^ 2 * (lam n ^ 2 * Φ) = 0.00288 * (ε / Real.sqrt n) * Φ *
          (40000000 * ε * Real.sqrt n * Real.log n ^ 2) := by rw [e1, e2]
      _ ≤ 0.00288 * (ε / Real.sqrt n) * Φ * k :=
          mul_le_mul_of_nonneg_left hk (by positivity)
  -- the Hessian term
  have hH : lam n * M * (ε ^ 2 / 2 + 0.0008 * ε ^ 2) ≤
      0.0005008 * (ε / Real.sqrt n) * lam n * n + 0.0005008 * ε * G := by
    have hM' : lam n * M ≤ lam n * (lam n * Real.sqrt n + G) :=
      mul_le_mul_of_nonneg_left hM hlampos.le
    have e : ε ^ 2 / 2 + 0.0008 * ε ^ 2 = 0.5008 * ε ^ 2 := by ring
    rw [e]
    have h1 : lam n * M * (0.5008 * ε ^ 2) ≤ lam n * (lam n * Real.sqrt n + G) * (0.5008 * ε ^ 2) :=
      mul_le_mul_of_nonneg_right hM' (by positivity)
    have e2 : lam n * (lam n * Real.sqrt n + G) * (0.5008 * ε ^ 2) =
        0.5008 * (lam n * ε) * (ε / Real.sqrt n) * lam n * n + 0.5008 * (lam n * ε) * ε * G := by
      have e3 : 0.5008 * (lam n * ε) * (ε / Real.sqrt n) * lam n * (Real.sqrt n * Real.sqrt n) +
          0.5008 * (lam n * ε) * ε * G = lam n * (lam n * Real.sqrt n + G) * (0.5008 * ε ^ 2) := by
        field_simp
      rw [hsn] at e3; exact e3.symm
    have h3 : 0.5008 * (lam n * ε) * (ε / Real.sqrt n) * lam n * n ≤
        0.5008 * (1 / 1000) * (ε / Real.sqrt n) * lam n * n := by
      have : 0 ≤ (ε / Real.sqrt n) * lam n * n := by positivity
      nlinarith
    have h4 : 0.5008 * (lam n * ε) * ε * G ≤ 0.5008 * (1 / 1000) * ε * G := by
      have : 0 ≤ ε * G := by positivity
      nlinarith
    linarith
  -- the gradient term, via Lemma 4.12 part 2
  have hGK : (ε / Real.sqrt n) * lam n * (Φ - n) ≤ ε * G := by
    have := mul_le_mul_of_nonneg_left hG hε.le
    calc (ε / Real.sqrt n) * lam n * (Φ - n) = ε * (lam n / Real.sqrt n * (Φ - n)) := by ring
      _ ≤ ε * G := this
  set K := ε / Real.sqrt n with hK
  have hKpos : 0 < K := by positivity
  have hT : lam n * ε / (15 * Real.sqrt n) * (Φ - 10 * n) = K * lam n * (Φ - 10 * n) / 15 := by
    rw [hK]; field_simp
  rw [hT]
  have hu : 0 ≤ Φ - n := by linarith
  have p1 : 0 ≤ K * (lam n - 1) * (Φ - n) := by
    have : 0 ≤ lam n - 1 := by rw [hlam]; linarith
    positivity
  have p2 : 0 ≤ K * (lam n - 1) * n := by
    have : 0 ≤ lam n - 1 := by rw [hlam]; linarith
    positivity
  have p3 : 0 ≤ K * n := by positivity
  have p4 : 0 ≤ K * (Φ - n) := by positivity
  nlinarith

lemma sq_sum_le {a b : ℝ} : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]

lemma w_bound {n : ℕ} (b e μ : Fin n → ℝ) (t ε q : ℝ) (ht : 0 < t) (hε : 0 < ε)
    (hq0 : 0.99999 ≤ q) (hq1 : q ≤ 1) (hμ : ∀ i, 0.9 * t ≤ μ i ∧ μ i ≤ 1.1 * t)
    (hb : ∑ i, b i ^ 2 ≤ (0.01 * ε * t) ^ 2) (he : ∑ i, e i ^ 2 ≤ (ε / 200) ^ 2) :
    ∑ i, ((b i + μ i * e i) / (q * t)) ^ 2 ≤ (0.02 * ε) ^ 2 := by
  have ht' : 0 < q * t := by nlinarith
  have hterm : ∀ i, (q * t) ^ 2 * ((b i + μ i * e i) / (q * t)) ^ 2 ≤
      2 * b i ^ 2 + 2.42 * t ^ 2 * e i ^ 2 := by
    intro i
    have e1 : (q * t) ^ 2 * ((b i + μ i * e i) / (q * t)) ^ 2 = (b i + μ i * e i) ^ 2 := by
      field_simp
    rw [e1]
    have hμ2 : μ i ^ 2 ≤ 1.21 * t ^ 2 := by nlinarith [(hμ i).1, (hμ i).2]
    have h2 := sq_sum_le (a := b i) (b := μ i * e i)
    have h3 : (μ i * e i) ^ 2 ≤ 1.21 * t ^ 2 * e i ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right hμ2 (sq_nonneg _)
    linarith
  set W := ∑ i, ((b i + μ i * e i) / (q * t)) ^ 2 with hW
  have hsum : (q * t) ^ 2 * W ≤ 2 * ∑ i, b i ^ 2 + 2.42 * t ^ 2 * ∑ i, e i ^ 2 := by
    rw [hW, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hterm i
  have ht'2 : 0.99998 * t ^ 2 ≤ (q * t) ^ 2 := by
    have hq2 : 0.99998 ≤ q ^ 2 := by nlinarith
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hq2 (sq_nonneg t)
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h0 := mul_le_mul_of_nonneg_right ht'2 hW0
  have h1 : t ^ 2 * (0.99998 * W) ≤ t ^ 2 * (0.0002606 * ε ^ 2) := by
    have e2 : 2 * (0.01 * ε * t) ^ 2 + 2.42 * t ^ 2 * (ε / 200) ^ 2 =
        t ^ 2 * (0.0002 * ε ^ 2 + 2.42 / 40000 * ε ^ 2) := by ring
    have h3 : 2 * ∑ i, b i ^ 2 + 2.42 * t ^ 2 * ∑ i, e i ^ 2 ≤
        2 * (0.01 * ε * t) ^ 2 + 2.42 * t ^ 2 * (ε / 200) ^ 2 := by
      have := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ 2.42 * t ^ 2 by positivity)
      linarith
    have h4 : t ^ 2 * (0.0002 * ε ^ 2 + 2.42 / 40000 * ε ^ 2) ≤ t ^ 2 * (0.0002606 * ε ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ε]) (sq_nonneg t)
    have e3 : 0.99998 * t ^ 2 * W = t ^ 2 * (0.99998 * W) := by ring
    linarith
  have h2 := le_of_mul_le_mul_left h1 (by positivity)
  nlinarith [sq_nonneg ε]

lemma sums_bound {n : ℕ} (g m w h s2 : Fin n → ℝ) (G M ε k lamv : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (hG : G = norm2 g) (hmean : ∀ i, m i = -(ε / 2) * (g i / G) + w i)
    (hw2 : ∑ i, w i ^ 2 ≤ (0.02 * ε) ^ 2) (hhnn : ∀ i, 0 ≤ h i) (hhM : ∀ i, h i ≤ lamv * M)
    (hlM : 0 ≤ lamv * M) (hs2b : ∀ i, s2 i ≤ 72 * ε ^ 2 / k + m i ^ 2) :
    ∑ i, g i * m i ≤ -(ε / 2) * G + 0.02 * ε * G ∧
    ∑ i, h i * s2 i ≤ 72 * ε ^ 2 / k * ∑ i, h i + lamv * M * (ε ^ 2 / 2 + 0.0008 * ε ^ 2) := by
  constructor
  · have e : ∑ i, g i * m i = -(ε / 2) * ∑ i, g i * (g i / G) + ∑ i, g i * w i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hmean i]; ring
    have h1 := sum_mul_div_norm2 g
    rw [← hG] at h1
    have hcs := abs_sum_mul_le g w (0.02 * ε) (by positivity) hw2
    rw [← hG] at hcs
    rw [e, h1]
    have := le_abs_self (∑ i, g i * w i)
    linarith
  · have hm2 : ∀ i, m i ^ 2 ≤ ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2 := by
      intro i
      rw [hmean i]
      have := sq_sum_le (a := -(ε / 2) * (g i / G)) (b := w i)
      have e : 2 * (-(ε / 2) * (g i / G)) ^ 2 = ε ^ 2 / 2 * (g i / G) ^ 2 := by ring
      linarith
    have step1 : ∑ i, h i * s2 i ≤ ∑ i, (72 * ε ^ 2 / k * h i +
        lamv * M * (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2)) := by
      apply Finset.sum_le_sum; intro i _
      have h1 : h i * s2 i ≤ h i * (72 * ε ^ 2 / k + (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith [hm2 i, hs2b i]) (hhnn i)
      have h2 : h i * (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2) ≤
          lamv * M * (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2) :=
        mul_le_mul_of_nonneg_right (hhM i) (by positivity)
      have e : h i * (72 * ε ^ 2 / k + (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2)) =
          72 * ε ^ 2 / k * h i + h i * (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2) := by ring
      linarith
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at step1
    have hg2 := sum_sq_div_norm2_le g
    rw [← hG] at hg2
    have h3 : ∑ i, (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2) ≤ ε ^ 2 / 2 + 0.0008 * ε ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have := mul_le_mul_of_nonneg_left hg2 (show (0:ℝ) ≤ ε ^ 2 / 2 by positivity)
      nlinarith [hw2]
    have := mul_le_mul_of_nonneg_left h3 hlM
    linarith

/-- Lemma 4.13 from the bounds of Lemma 4.8, Lemma 4.12 and a bound on the conditioning bias,
for an abstract probability law `P` of the sample and an abstract `μ^new = Mn`. -/
lemma core {n : ℕ} (hn : 10 ≤ n) (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (Mn : (Fin n → ℝ) → Fin n → ℝ) (hMn : ∀ i, Continuous fun δ => Mn δ i)
    (μ δμ : Fin n → ℝ) (t ε εmp k : ℝ) (ht : 0 < t) (hε : 0 < ε)
    (hεle : ε ≤ 1 / (40000 * Real.log n)) (hεmp : 0 < εmp) (hεmp' : εmp ≤ 1 / 40000)
    (hk : 1000 * ε * Real.sqrt n * Real.log n ^ 2 / εmp ≤ k)
    (hμ : ∀ i, 0.9 * t ≤ μ i ∧ μ i ≤ 1.1 * t)
    (hδμ : ∀ i, δμ i = ((1 - ε / (3 * Real.sqrt n)) * t / t - 1) * μ i -
        ε / 2 * ((1 - ε / (3 * Real.sqrt n)) * t) *
        (potentialGrad (lam n) (fun l => μ l / t - 1) i /
          norm2 (potentialGrad (lam n) (fun l => μ l / t - 1))))
    (hsup : ∀ᵐ δ ∂P, ∀ i, |(Mn δ i - μ i) / μ i| ≤ 0.021 / Real.log n)
    (B : ℝ) (hδbd : ∀ᵐ δ ∂P, ∀ i, |δ i| ≤ B)
    (he : norm2 (fun i => ∫ δ, (Mn δ i - μ i - δ i) / μ i ∂P) ≤ ε / 200)
    (hvar : ∀ i, variance (fun δ => Mn δ i / μ i) P ≤ 50 * ε ^ 2 / k)
    (hb : ∑ i, (∫ δ, δ i ∂P - δμ i) ^ 2 ≤ (0.01 * ε * t) ^ 2) :
    ∫ δ, potential (lam n) (fun i => Mn δ i / ((1 - ε / (3 * Real.sqrt n)) * t) - 1) ∂P
      ≤ potential (lam n) (fun i => μ i / t - 1) -
        lam n * ε / (15 * Real.sqrt n) * (potential (lam n) (fun i => μ i / t - 1) - 10 * n) := by
  have hL := one_lt_log hn
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hsq3 : 3 ≤ Real.sqrt n := by
    rw [show (3:ℝ) = Real.sqrt 9 by
      rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : 0 < Real.sqrt n := by linarith
  have hεL : ε * Real.log n ≤ 1 / 40000 := by
    rw [le_div_iff₀ (by positivity)] at hεle; linarith
  have hε1 : ε ≤ 1 / 40000 := by nlinarith
  have hlam : lam n = 40 * Real.log n := rfl
  have hlampos : 0 < lam n := by rw [hlam]; linarith
  set α := ε / (3 * Real.sqrt n) with hα
  have hα0 : 0 < α := by positivity
  have hαle : α ≤ ε / 9 := div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
  have hαL : α * Real.log n ≤ 1 / 360000 := by nlinarith
  have hq0 : 0.99999 ≤ 1 - α := by linarith
  have ht'0 : 0 < (1 - α) * t := by nlinarith
  set t' := (1 - α) * t with ht'
  set r : Fin n → ℝ := fun i => μ i / t - 1 with hr
  set g := potentialGrad (lam n) r with hg
  set G := norm2 g with hG
  have hμpos : ∀ i, 0 < μ i := fun i => by linarith [(hμ i).1]
  have hμt' : ∀ i, μ i / t' ≤ 1.1001 := fun i => by
    rw [div_le_iff₀ ht'0, ht']; nlinarith [(hμ i).2]
  have hμt'0 : ∀ i, 0 < μ i / t' := fun i => div_pos (hμpos i) ht'0
  obtain ⟨V, hV⟩ : ∃ V : Fin n → (Fin n → ℝ) → ℝ, V = fun i δ => Mn δ i / t' - 1 - r i :=
    ⟨_, rfl⟩
  have hVcont : ∀ i, Continuous (V i) := fun i => by
    rw [hV]; exact (((hMn i).div_const _).sub continuous_const).sub continuous_const
  -- a.e. size of the step
  have hVbd : ∀ᵐ δ ∂P, ∀ i, |V i δ| ≤ 1 / lam n := by
    filter_upwards [hsup] with δ hδ i
    have e : V i δ = μ i / t' * ((Mn δ i - μ i) / μ i) + μ i / t' * α := by
      have := (hμpos i).ne'
      rw [hV, hr, ht']; field_simp; ring
    have h1 : |V i δ| ≤ μ i / t' * (0.021 / Real.log n + α) := by
      rw [e]
      calc |μ i / t' * ((Mn δ i - μ i) / μ i) + μ i / t' * α|
          ≤ |μ i / t' * ((Mn δ i - μ i) / μ i)| + |μ i / t' * α| := abs_add_le _ _
        _ = μ i / t' * |(Mn δ i - μ i) / μ i| + μ i / t' * α := by
            rw [abs_mul, abs_mul, abs_of_pos (hμt'0 i), abs_of_pos hα0]
        _ ≤ μ i / t' * (0.021 / Real.log n) + μ i / t' * α := by
            have := mul_le_mul_of_nonneg_left (hδ i) (hμt'0 i).le; linarith
        _ = μ i / t' * (0.021 / Real.log n + α) := by ring
    have h2 : μ i / t' * (0.021 / Real.log n + α) ≤ 1.1001 * (0.021 / Real.log n + α) :=
      mul_le_mul_of_nonneg_right (hμt' i) (by positivity)
    have h3 : 1.1001 * (0.021 / Real.log n + α) ≤ 1 / lam n := by
      rw [hlam]
      have e2 : 1.1001 * (0.021 / Real.log n + α) = 1.1001 * (0.021 + α * Real.log n) / Real.log n := by
        field_simp
      have e3 : (1:ℝ) / (40 * Real.log n) = (1 / 40) / Real.log n := by
        rw [div_div]
      rw [e2, e3]
      apply div_le_div_of_nonneg_right _ (by linarith)
      nlinarith
    linarith
  have hMnbd : ∀ᵐ δ ∂P, ∀ i, |Mn δ i| ≤ 3 * t := by
    filter_upwards [hsup] with δ hδ i
    have e : Mn δ i = μ i * ((Mn δ i - μ i) / μ i) + μ i := by
      field_simp [(hμpos i).ne']; ring
    have h0 : 0.021 / Real.log n ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    rw [e]
    calc |μ i * ((Mn δ i - μ i) / μ i) + μ i| ≤ |μ i * ((Mn δ i - μ i) / μ i)| + |μ i| :=
          abs_add_le _ _
      _ = μ i * |(Mn δ i - μ i) / μ i| + μ i := by
          rw [abs_mul, abs_of_pos (hμpos i)]
      _ ≤ μ i * 1 + μ i := by
          have := mul_le_mul_of_nonneg_left ((hδ i).trans h0) (hμpos i).le; linarith
      _ ≤ 3 * t := by linarith [(hμ i).2]
  -- integrability
  have hMnI : ∀ i, Integrable (fun δ => Mn δ i) P := fun i =>
    Integrable.of_bound (hMn i).aestronglyMeasurable (3 * t)
      (by filter_upwards [hMnbd] with δ hδ; rw [Real.norm_eq_abs]; exact hδ i)
  have hδI : ∀ i, Integrable (fun δ : Fin n → ℝ => δ i) P := fun i =>
    Integrable.of_bound (continuous_apply i).aestronglyMeasurable B
      (by filter_upwards [hδbd] with δ hδ; rw [Real.norm_eq_abs]; exact hδ i)
  have hVI : ∀ i, Integrable (V i) P := fun i =>
    Integrable.of_bound (hVcont i).aestronglyMeasurable (1 / lam n)
      (by filter_upwards [hVbd] with δ hδ; rw [Real.norm_eq_abs]; exact hδ i)
  have hV2I : ∀ i, Integrable (fun δ => V i δ ^ 2) P := fun i =>
    Integrable.of_bound ((hVcont i).pow 2).aestronglyMeasurable ((1 / lam n) ^ 2)
      (by
        filter_upwards [hVbd] with δ hδ
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hδ i) 2)
  have hVL2 : ∀ i, MemLp (V i) 2 P := fun i =>
    MemLp.of_bound (hVcont i).aestronglyMeasurable (1 / lam n)
      (by filter_upwards [hVbd] with δ hδ; rw [Real.norm_eq_abs]; exact hδ i)
  -- Lemma 4.12
  obtain ⟨h412a, h412b, h412c⟩ := L412_pbp_main hn (lam n) hlampos r
  set h : Fin n → ℝ := fun i => lam n ^ 2 * Real.cosh (lam n * r i) with hh
  set Φ0 := potential (lam n) r with hΦ0
  -- the pointwise second-order bound
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℝ) → ℝ, F = fun δ =>
      Φ0 + ∑ i, g i * V i δ + 2 * ∑ i, h i * V i δ ^ 2 := ⟨_, rfl⟩
  have hpt : ∀ᵐ δ ∂P,
      potential (lam n) (fun i => Mn δ i / t' - 1) ≤ F δ := by
    filter_upwards [hVbd] with δ hδ
    have e : (fun i => Mn δ i / t' - 1) = (fun i => r i + (fun j => V j δ) i) := by
      funext i; rw [hV]; ring
    rw [e, hF]
    exact h412a (fun j => V j δ) hδ
  have hFI : Integrable F P := by
    rw [hF]
    refine ((integrable_const Φ0).add ?_).add (Integrable.const_mul ?_ 2)
    · exact integrable_finsetSum _ fun i _ => (hVI i).const_mul (g i)
    · exact integrable_finsetSum _ fun i _ => (hV2I i).const_mul (h i)
  have hΦnew_cont : Continuous fun δ => potential (lam n) (fun i => Mn δ i / t' - 1) := by
    unfold potential
    exact continuous_finset_sum _ fun i _ =>
      Real.continuous_cosh.comp (continuous_const.mul (((hMn i).div_const _).sub continuous_const))
  have hmono : ∫ δ, potential (lam n) (fun i => Mn δ i / t' - 1) ∂P ≤ ∫ δ, F δ ∂P := by
    refine integral_mono_ae ?_ hFI hpt
    refine Integrable.mono' hFI hΦnew_cont.aestronglyMeasurable ?_
    filter_upwards [hpt] with δ hδ
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hδ
    · unfold potential; exact Finset.sum_nonneg fun i _ => (Real.cosh_pos _).le
  set m : Fin n → ℝ := fun i => ∫ δ, V i δ ∂P with hm
  set s2 : Fin n → ℝ := fun i => ∫ δ, V i δ ^ 2 ∂P with hs2
  have hFint : ∫ δ, F δ ∂P = Φ0 + ∑ i, g i * m i + 2 * ∑ i, h i * s2 i := by
    rw [hF, integral_add, integral_add, integral_const, integral_const_mul,
      integral_finset_sum, integral_finset_sum]
    · simp only [probReal_univ, one_smul, hm, hs2, integral_const_mul]
    · exact fun i _ => (hV2I i).const_mul (h i)
    · exact fun i _ => (hVI i).const_mul (g i)
    · exact integrable_const _
    · exact integrable_finsetSum _ fun i _ => (hVI i).const_mul (g i)
    · exact (integrable_const _).add (integrable_finsetSum _ fun i _ => (hVI i).const_mul (g i))
    · exact Integrable.const_mul (integrable_finsetSum _ fun i _ => (hV2I i).const_mul (h i)) 2
  -- the mean of the step
  set e : Fin n → ℝ := fun i => ∫ δ, (Mn δ i - μ i - δ i) / μ i ∂P with he_def
  set b : Fin n → ℝ := fun i => ∫ δ, δ i ∂P - δμ i with hb_def
  set w : Fin n → ℝ := fun i => (b i + μ i * e i) / t' with hw_def
  have hmean : ∀ i, m i = -(ε / 2) * (g i / G) + w i := by
    intro i
    have h1 : m i = (∫ δ, Mn δ i ∂P) / t' - 1 - r i := by
      simp only [hm, hV]
      rw [integral_sub, integral_sub, integral_div, integral_const, integral_const]
      · simp
      · exact (hMnI i).div_const _
      · exact integrable_const _
      · exact ((hMnI i).div_const _).sub (integrable_const _)
      · exact integrable_const _
    have h2 : e i = ((∫ δ, Mn δ i ∂P) - μ i - ∫ δ, δ i ∂P) / μ i := by
      simp only [he_def]
      rw [integral_div, integral_sub, integral_sub, integral_const]
      · simp
      · exact hMnI i
      · exact integrable_const _
      · exact (hMnI i).sub (integrable_const _)
      · exact hδI i
    have h3 : ∫ δ, Mn δ i ∂P = μ i * e i + μ i + ∫ δ, δ i ∂P := by
      rw [h2]; field_simp [(hμpos i).ne']; ring
    have h4 : ∫ δ, δ i ∂P = b i + δμ i := by simp only [hb_def]; ring
    rw [h1, h3, h4, hδμ i]
    simp only [hw_def, hr]
    field_simp
    ring
  -- second moments
  have hkpos : 0 < k := lt_of_lt_of_le (by positivity) hk
  have hk' : 40000000 * ε * Real.sqrt n * Real.log n ^ 2 ≤ k := by
    refine le_trans ?_ hk
    rw [le_div_iff₀ hεmp]
    have : 0 ≤ ε * Real.sqrt n * Real.log n ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hεmp' this
    linarith
  have hs2b : ∀ i, s2 i ≤ 72 * ε ^ 2 / k + m i ^ 2 := by
    intro i
    have e : V i = fun δ => μ i / t' * (Mn δ i / μ i) + (-1 - r i) := by
      have := (hμpos i).ne'
      rw [hV]; funext δ; field_simp; ring
    have hvarV : variance (V i) P ≤ 1.1001 ^ 2 * (50 * ε ^ 2 / k) := by
      have hXm : AEStronglyMeasurable (fun δ => μ i / t' * (Mn δ i / μ i)) P :=
        (((hMn i).div_const _).const_mul _).aestronglyMeasurable
      rw [e, variance_add_const hXm, variance_const_mul]
      exact mul_le_mul (pow_le_pow_left₀ (hμt'0 i).le (hμt' i) 2) (hvar i)
        (variance_nonneg _ _) (by positivity)
    have e1 : s2 i = variance (V i) P + m i ^ 2 := by
      rw [variance_eq_sub (hVL2 i)]
      simp only [hs2, hm, Pi.pow_apply]
      ring
    have h72 : 1.1001 ^ 2 * (50 * ε ^ 2 / k) ≤ 72 * ε ^ 2 / k := by
      rw [← mul_div_assoc, ← mul_assoc]
      apply div_le_div_of_nonneg_right _ hkpos.le
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg ε)
    linarith
  have hb' : ∑ i, b i ^ 2 ≤ (0.01 * ε * t) ^ 2 := hb
  have he2 : ∑ i, e i ^ 2 ≤ (ε / 200) ^ 2 := by
    have h1 : ∑ i, e i ^ 2 = (norm2 e) ^ 2 := by
      unfold norm2; rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    rw [h1]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) he 2
  have hw2 : ∑ i, w i ^ 2 ≤ (0.02 * ε) ^ 2 :=
    w_bound b e μ t ε (1 - α) ht hε hq0 (by linarith) hμ hb' he2
  have hhnn : ∀ i, 0 ≤ h i := fun i => (mul_pos (by positivity) (Real.cosh_pos _)).le
  set M := Real.sqrt (∑ i, lam n ^ 2 * Real.cosh (lam n * r i) ^ 2) with hM
  have hhM : ∀ i, h i ≤ lam n * M := by
    intro i
    have h1 : lam n * Real.cosh (lam n * r i) ≤ M := by
      have h2 : (lam n * Real.cosh (lam n * r i)) ^ 2 ≤
          ∑ j, lam n ^ 2 * Real.cosh (lam n * r j) ^ 2 := by
        rw [mul_pow]
        exact Finset.single_le_sum (f := fun j => lam n ^ 2 * Real.cosh (lam n * r j) ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ i)
      exact (le_abs_self _).trans (Real.abs_le_sqrt h2)
    calc h i = lam n * (lam n * Real.cosh (lam n * r i)) := by simp only [hh]; ring
      _ ≤ lam n * M := mul_le_mul_of_nonneg_left h1 hlampos.le
  have hlM : 0 ≤ lam n * M := mul_nonneg hlampos.le (Real.sqrt_nonneg _)
  obtain ⟨hS1, hS2⟩ := sums_bound g m w h s2 G M ε k (lam n) hε hkpos hG hmean hw2 hhnn hhM hlM hs2b
  have hSh : ∑ i, h i = lam n ^ 2 * Φ0 := by
    simp only [hh, hΦ0, potential, Finset.mul_sum]
  have hΦn : (n : ℝ) ≤ Φ0 := by
    simp only [hΦ0, potential]
    calc (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => Real.one_le_cosh _
  have h412b' : lam n / Real.sqrt n * (Φ0 - n) ≤ G := h412b
  have h412c' : M ≤ lam n * Real.sqrt n + G := h412c
  have hfin := final_ineq hn ε k Φ0 G M hε hεle hk' hΦn (Real.sqrt_nonneg _) h412b' h412c'
    (∑ i, g i * m i) (∑ i, h i * s2 i) (∑ i, h i) hS1 hS2 hSh
  calc ∫ δ, potential (lam n) (fun i => Mn δ i / t' - 1) ∂P ≤ ∫ δ, F δ ∂P := hmono
    _ = Φ0 + ∑ i, g i * m i + 2 * ∑ i, h i * s2 i := hFint
    _ ≤ _ := hfin

/-- `C M C = C` for `C = M⁻¹` (Mathlib's inverse is `0` on singular matrices). -/
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

/-- Every entry of `P̄` is at most `1` in absolute value: `P̄ᵀ P̄ = P̄`. -/
lemma projBar_entry_le {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (xb sb : Fin n → ℝ)
    (hx : ∀ i, 0 < xb i) (hs : ∀ i, 0 < sb i) (i j : Fin n) :
    |projBar A xb sb j i| ≤ 1 := by
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
  have hcol : ∀ i, ∑ j, P j i ^ 2 = P i i := by
    intro i
    have := congrFun (congrFun hPP i) i
    rw [Matrix.mul_apply] at this
    simpa [Matrix.transpose_apply, sq] using this
  have hii : P i i ≤ 1 := by
    have h1 : P i i ^ 2 ≤ ∑ j, P j i ^ 2 :=
      Finset.single_le_sum (f := fun j => P j i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hcol i] at h1
    nlinarith [sq_nonneg (P i i)]
  have h2 : P j i ^ 2 ≤ 1 := by
    have : P j i ^ 2 ≤ ∑ k, P k i ^ 2 :=
      Finset.single_le_sum (f := fun k => P k i ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    rw [hcol i] at this; linarith
  have := Real.abs_le_sqrt h2
  rwa [Real.sqrt_one] at this

lemma stepX_add {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v u w : Fin n → ℝ) (j : Fin n) :
    stepX A x s v (u + w) j = stepX A x s v u j + stepX A x s v w j := by
  unfold stepX pMu
  have e : (fun l => (u + w) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      (fun l => u l / Real.sqrt (xbar x s v l * sbar x s v l)) +
      (fun l => w l / Real.sqrt (xbar x s v l * sbar x s v l)) := by
    funext l; simp [add_div]
  rw [e, Matrix.mulVec_add]
  simp only [Pi.add_apply]
  ring

lemma stepS_add {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v u w : Fin n → ℝ) (j : Fin n) :
    stepS A x s v (u + w) j = stepS A x s v u j + stepS A x s v w j := by
  unfold stepS pMu
  have e : (fun l => (u + w) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      (fun l => u l / Real.sqrt (xbar x s v l * sbar x s v l)) +
      (fun l => w l / Real.sqrt (xbar x s v l * sbar x s v l)) := by
    funext l; simp [add_div]
  rw [e, Matrix.mulVec_add]
  simp only [Pi.add_apply]
  ring

lemma pMu_single {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n)
    (a : ℝ) (j : Fin n) :
    pMu A x s v (Pi.single i a) j = projBar A (xbar x s v) (sbar x s v) j i *
      (a / Real.sqrt (xbar x s v i * sbar x s v i)) := by
  unfold pMu
  have e : (fun l => (Pi.single i a : Fin n → ℝ) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      Pi.single i (a / Real.sqrt (xbar x s v i * sbar x s v i)) := by
    funext l
    by_cases h : l = i
    · subst h; simp
    · simp [h]
  rw [e]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The effect of one coordinate of the sample on the normalised steps. -/
lemma single_step_bound {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ)
    (hxb : ∀ j, 0 < xbar x s v j) (hsb : ∀ j, 0 < sbar x s v j) (c : ℝ) (hc : 0 < c)
    (hcj : ∀ j, c ≤ xbar x s v j * sbar x s v j) (i : Fin n) (a : ℝ) (j : Fin n) :
    |stepS A x s v (Pi.single i a) j / sbar x s v j| ≤ |a| / c ∧
    |stepX A x s v (Pi.single i a) j / xbar x s v j| ≤ 2 * (|a| / c) := by
  set mi := xbar x s v i * sbar x s v i with hmi
  set mj := xbar x s v j * sbar x s v j with hmj
  have hmi0 : 0 < mi := mul_pos (hxb i) (hsb i)
  have hmj0 : 0 < mj := mul_pos (hxb j) (hsb j)
  have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hsi : Real.sqrt c ≤ Real.sqrt mi := Real.sqrt_le_sqrt (hcj i)
  have hsj : Real.sqrt c ≤ Real.sqrt mj := Real.sqrt_le_sqrt (hcj j)
  have hsc0 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hprod : c ≤ Real.sqrt mi * Real.sqrt mj := by
    rw [← hsc, sq]; exact mul_le_mul hsi hsj hsc0.le (Real.sqrt_nonneg _)
  have hP := projBar_entry_le A (xbar x s v) (sbar x s v) hxb hsb i j
  set p := pMu A x s v (Pi.single i a) j with hp
  have hpj : |p| ≤ |a| / Real.sqrt mi := by
    rw [hp, pMu_single, abs_mul, abs_div, abs_of_pos (Real.sqrt_pos.2 hmi0)]
    calc |projBar A (xbar x s v) (sbar x s v) j i| * (|a| / Real.sqrt mi)
        ≤ 1 * (|a| / Real.sqrt mi) := mul_le_mul_of_nonneg_right hP (by positivity)
      _ = |a| / Real.sqrt mi := one_mul _
  have hkey : |p / Real.sqrt mj| ≤ |a| / c := by
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 hmj0)]
    calc |p| / Real.sqrt mj ≤ (|a| / Real.sqrt mi) / Real.sqrt mj :=
          div_le_div_of_nonneg_right hpj (Real.sqrt_nonneg _)
      _ = |a| / (Real.sqrt mi * Real.sqrt mj) := by rw [div_div]
      _ ≤ |a| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hprod
  have eS : stepS A x s v (Pi.single i a) j / sbar x s v j = p / Real.sqrt mj := by
    unfold stepS
    rw [← hp]
    have := (hsb j).ne'
    rw [hmj]
    field_simp
  have eX : stepX A x s v (Pi.single i a) j / xbar x s v j =
      (Pi.single i a : Fin n → ℝ) j / mj - p / Real.sqrt mj := by
    unfold stepX
    rw [← hp]
    have := (hsb j).ne'
    have := (hxb j).ne'
    have := (Real.sqrt_pos.2 hmj0).ne'
    rw [hmj]
    field_simp
  refine ⟨by rw [eS]; exact hkey, ?_⟩
  rw [eX]
  have h1 : |(Pi.single i a : Fin n → ℝ) j / mj| ≤ |a| / c := by
    rw [abs_div, abs_of_pos hmj0]
    have ha : |(Pi.single i a : Fin n → ℝ) j| ≤ |a| := by
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    calc |(Pi.single i a : Fin n → ℝ) j| / mj ≤ |a| / mj := div_le_div_of_nonneg_right ha hmj0.le
      _ ≤ |a| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc (hcj j)
  calc |(Pi.single i a : Fin n → ℝ) j / mj - p / Real.sqrt mj|
      ≤ |(Pi.single i a : Fin n → ℝ) j / mj| + |p / Real.sqrt mj| := abs_sub _ _
    _ ≤ |a| / c + |a| / c := add_le_add h1 hkey
    _ = 2 * (|a| / c) := by ring



lemma sum_sq_div_norm2_le' {n : ℕ} (g : Fin n → ℝ) :
    ∑ i, (g i / norm2 g) ^ 2 ≤ 1 := by
  unfold norm2
  set G := Real.sqrt (∑ i, g i ^ 2) with hG
  have hsq : G ^ 2 = ∑ i, g i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases h0 : G = 0
  · rw [h0]; simp
  · have : ∑ i, (g i / G) ^ 2 = (∑ i, g i ^ 2) / G ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← hsq, div_self (pow_ne_zero 2 h0)]

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

lemma coordLaw_bad (p a : ℝ) (hp0 : 0 < p) : coordLaw p a {y | |a| / p < |y|} = 0 := by
  unfold coordLaw
  have hm : MeasurableSet {y : ℝ | |a| / p < |y|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hm,
    Measure.dirac_apply' _ hm]
  have h1 : a / p ∉ {y : ℝ | |a| / p < |y|} := by
    simp [abs_div, abs_of_pos hp0]
  have h2 : (0:ℝ) ∉ {y : ℝ | |a| / p < |y|} := by
    simp only [Set.mem_setOf_eq, abs_zero, not_lt]; positivity
  rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  simp

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

/-- Coordinate `i` of a product law is independent of the other coordinates. -/
lemma indep_update {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (H : Set (Fin n → ℝ)) (hH : MeasurableSet H) :
    ∫ δ, |δ i| * H.indicator 1 (Function.update δ i 0) ∂(Measure.pi μs) =
      (∫ δ, |δ i| ∂(Measure.pi μs)) *
        ∫ δ, H.indicator 1 (Function.update δ i 0) ∂(Measure.pi μs) := by
  have hI := iIndepFun_pi (μ := μs) (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hdisj : Disjoint ({i} : Finset (Fin n)) (Finset.univ.erase i) := by simp
  have h2 := hI.indepFun_finset {i} (Finset.univ.erase i) hdisj
    (fun j => measurable_id.comp (measurable_pi_apply j))
  set φ : (({i} : Finset (Fin n)) → ℝ) → ℝ := fun y => |y ⟨i, Finset.mem_singleton_self i⟩|
    with hφ
  set ext : ((Finset.univ.erase i) → ℝ) → Fin n → ℝ := fun z j =>
    if h : j = i then 0 else z ⟨j, Finset.mem_erase.2 ⟨h, Finset.mem_univ j⟩⟩ with hext
  have hextm : Measurable ext := by
    refine measurable_pi_lambda _ fun j => ?_
    by_cases h : j = i
    · subst h; simpa [hext] using measurable_const
    · simp only [hext, h, ↓reduceDIte]; exact measurable_pi_apply _
  have hφm : Measurable φ := continuous_abs.measurable.comp (measurable_pi_apply _)
  have hψm : Measurable (fun z => H.indicator (1 : (Fin n → ℝ) → ℝ) (ext z)) :=
    (measurable_const.indicator hH).comp hextm
  have h3 := h2.comp hφm hψm
  have h4 := h3.integral_fun_mul_eq_mul_integral
    (hφm.comp (measurable_pi_lambda _ fun j => measurable_id.comp
      (measurable_pi_apply _))).aestronglyMeasurable
    (hψm.comp (measurable_pi_lambda _ fun j => measurable_id.comp
      (measurable_pi_apply _))).aestronglyMeasurable
  have e1 : ∀ δ : Fin n → ℝ, (φ ∘ fun a (j : ({i} : Finset (Fin n))) => id (a j)) δ = |δ i| := by
    intro δ; rfl
  have e2 : ∀ δ : Fin n → ℝ, ((fun z => H.indicator (1 : (Fin n → ℝ) → ℝ) (ext z)) ∘
      fun a (j : (Finset.univ.erase i)) => id (a j)) δ = H.indicator 1 (Function.update δ i 0) := by
    intro δ
    simp only [Function.comp_apply, id]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp [hext]
    · simp [hext, h, Function.update_of_ne h]
  simp only [e1, e2] at h4
  exact h4

lemma abs_sum_mul_le' {n : ℕ} (g w : Fin n → ℝ) (G W : ℝ) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hg : ∑ i, g i ^ 2 ≤ G ^ 2) (hw : ∑ i, w i ^ 2 ≤ W ^ 2) : |∑ i, g i * w i| ≤ G * W := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g w
  have h1 : (∑ i, g i * w i) ^ 2 ≤ (G * W) ^ 2 := by
    rw [mul_pow]
    exact hcs.trans (mul_le_mul hg hw (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _))
  have h2 := Real.abs_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity)] at h2

/-- `‖δ_μ‖₂ ≤ 0.8667 ε t` for the direction of line 11 of Main. -/
lemma direction_sq_le {n : ℕ} (hn : 10 ≤ n) (x s : Fin n → ℝ) (t ε : ℝ) (ht : 0 < t)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 40000) (hap : ApproxScalar 0.1 (fun i => x i * s i) t) :
    ∑ i, direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s i ^ 2 ≤
      (0.8667 * ε * t) ^ 2 := by
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hsn : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  set α := ε / (3 * Real.sqrt n) with hα
  have hα0 : 0 < α := by positivity
  have hα1 : α ≤ 1 := by
    have : α ≤ ε := div_le_self hε.le (by nlinarith)
    linarith
  set g := potentialGrad (lam n) (fun l => x l * s l / t - 1) with hg
  set a : Fin n → ℝ := fun i => -α * (x i * s i) with ha
  set c : Fin n → ℝ := fun i => -(ε / 2 * ((1 - α) * t)) * (g i / norm2 g) with hc
  have e : ∀ i, direction (lam n) ε t ((1 - α) * t) x s i = a i + c i := by
    intro i
    simp only [direction, ha, hc, ← hg]
    field_simp
    ring
  simp only [e]
  have hA : ∑ i, a i ^ 2 ≤ (0.3667 * ε * t) ^ 2 := by
    have h1 : ∀ i, a i ^ 2 ≤ α ^ 2 * (1.1 * t) ^ 2 := by
      intro i
      have := hap i
      simp only [ha]
      rw [neg_mul, neg_sq, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by nlinarith) (by linarith) 2)
        (sq_nonneg _)
    calc ∑ i, a i ^ 2 ≤ ∑ _i : Fin n, α ^ 2 * (1.1 * t) ^ 2 := Finset.sum_le_sum fun i _ => h1 i
      _ = n * (α ^ 2 * (1.1 * t) ^ 2) := by simp
      _ = 1.21 / 9 * ε ^ 2 * t ^ 2 := by
          rw [hα]; field_simp; rw [hsn]; ring
      _ ≤ (0.3667 * ε * t) ^ 2 := by nlinarith [sq_nonneg (ε * t)]
  have hC : ∑ i, c i ^ 2 ≤ (0.5 * ε * t) ^ 2 := by
    have h2 := sum_sq_div_norm2_le' g
    have e2 : ∑ i, c i ^ 2 = (ε / 2 * ((1 - α) * t)) ^ 2 * ∑ i, (g i / norm2 g) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]; ring
    rw [e2]
    have hq0 : 0 ≤ (1 - α) * t := mul_nonneg (by linarith) ht.le
    have hq1 : (1 - α) * t ≤ t := by nlinarith
    have h3 : (ε / 2 * ((1 - α) * t)) ^ 2 ≤ (0.5 * ε * t) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by positivity) hq0)
        (by have := mul_le_mul_of_nonneg_left hq1 (show (0:ℝ) ≤ ε / 2 by positivity); linarith) 2
    calc (ε / 2 * ((1 - α) * t)) ^ 2 * ∑ i, (g i / norm2 g) ^ 2
        ≤ (0.5 * ε * t) ^ 2 * 1 := mul_le_mul h3 h2 (Finset.sum_nonneg fun i _ => sq_nonneg _)
          (sq_nonneg _)
      _ = (0.5 * ε * t) ^ 2 := mul_one _
  have hAC := abs_sum_mul_le' a c (0.3667 * ε * t) (0.5 * ε * t) (by positivity) (by positivity) hA hC
  have e3 : ∑ i, (a i + c i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * c i + ∑ i, c i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [e3]
  have := le_abs_self (∑ i, a i * c i)
  nlinarith

/-- On the success event, `|δ_i| ≤ 2 x̄_i s̄_i`: `δ̃_x/x̄ + δ̃_s/s̄ = δ̃_μ/(x̄ s̄)`. -/
lemma delta_le_on_success {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (x s v : Fin n → ℝ) (hxb : ∀ j, 0 < xbar x s v j) (hsb : ∀ j, 0 < sbar x s v j)
    (δ : Fin n → ℝ) (hδ : δ ∈ successEvent A x s v) (i : Fin n) :
    |δ i| ≤ 2 * (xbar x s v i * sbar x s v i) := by
  have hL : 1 < Real.log n := by
    have h10 : (10:ℝ) ≤ n := by exact_mod_cast hn
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log n := Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  obtain ⟨h1, h2⟩ := hδ i
  have hb : 1 / (100 * Real.log n) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hm := mul_pos (hxb i) (hsb i)
  have e : δ i = (xbar x s v i * sbar x s v i) *
      (stepS A x s v δ i / sbar x s v i + stepX A x s v δ i / xbar x s v i) := by
    have := (hxb i).ne'
    have := (hsb i).ne'
    have := (Real.sqrt_pos.2 hm).ne'
    unfold stepS stepX
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos hm]
  have h3 := abs_add_le (stepS A x s v δ i / sbar x s v i) (stepX A x s v δ i / xbar x s v i)
  have h4 : |stepS A x s v δ i / sbar x s v i + stepX A x s v δ i / xbar x s v i| ≤ 2 := by linarith
  nlinarith

lemma cont_stepX {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n) :
    Continuous (fun δ => stepX A x s v δ i) := by
  unfold stepX pMu; fun_prop

lemma cont_stepS {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n) :
    Continuous (fun δ => stepS A x s v δ i) := by
  unfold stepS pMu; fun_prop

lemma stepS_smul {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ) (c : ℝ)
    (j : Fin n) : stepS A x s v (c • δ) j = c * stepS A x s v δ j := by
  unfold stepS pMu
  have e : (fun l => (c • δ) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      c • (fun l => δ l / Real.sqrt (xbar x s v l * sbar x s v l)) := by
    funext l; simp [mul_div_assoc]
  rw [e, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma stepX_smul {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ) (c : ℝ)
    (j : Fin n) : stepX A x s v (c • δ) j = c * stepX A x s v δ j := by
  unfold stepX pMu
  have e : (fun l => (c • δ) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      c • (fun l => δ l / Real.sqrt (xbar x s v l * sbar x s v l)) := by
    funext l; simp [mul_div_assoc]
  rw [e, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma sampleProb_smul {n : ℕ} (k : ℝ) (δ : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) (i : Fin n) :
    sampleProb k (c • δ) i = sampleProb k δ i := by
  unfold sampleProb
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

lemma coordLaw_map (p a c : ℝ) :
    (coordLaw p a).map (fun y => c * y) = coordLaw p (c * a) := by
  unfold coordLaw
  rw [Measure.map_add _ _ (measurable_const_mul c), Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' (measurable_const_mul c), Measure.map_dirac' (measurable_const_mul c)]
  simp [mul_div_assoc]

lemma sampleLaw_smul {n : ℕ} (k : ℝ) (δ : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    sampleLaw k (c • δ) = (sampleLaw k δ).map (fun δ => c • δ) := by
  unfold sampleLaw
  have e : (fun δ : Fin n → ℝ => c • δ) = (fun x i => (fun y => c * y) (x i)) := by
    funext x i; simp
  rw [e, Measure.pi_map_pi (fun i => (measurable_const_mul c).aemeasurable)]
  congr 1; funext i
  rw [coordLaw_map, sampleProb_smul k δ c hc]
  simp

lemma integral_coord {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ δ, f (δ i) ∂(Measure.pi μs) = ∫ y, f y ∂(μs i) := by
  have := integral_map (μ := Measure.pi μs) (measurable_pi_apply i).aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [(measurePreserving_eval μs i).map_eq] at this
  exact this.symm

lemma ae_coord_le {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (B : ℝ) (h : μs i {y | B < |y|} = 0) :
    ∀ᵐ δ ∂(Measure.pi μs), |δ i| ≤ B := by
  rw [ae_iff]
  have hm : MeasurableSet {y : ℝ | B < |y|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have := (measurePreserving_eval μs i).measure_preimage hm.nullMeasurableSet
  simp only [not_le]
  rw [show {a : Fin n → ℝ | B < |a i|} = Function.eval i ⁻¹' {y | B < |y|} from rfl, this, h]

lemma perturb_good {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ)
    (hxb : ∀ j, 0 < xbar x s v j) (hsb : ∀ j, 0 < sbar x s v j) (c : ℝ) (hc : 0 < c)
    (hcj : ∀ j, c ≤ xbar x s v j * sbar x s v j) (u : Fin n → ℝ) (i : Fin n) (a ρ τ : ℝ)
    (ha : 2 * (|a| / c) ≤ ρ)
    (hu : ∀ j, |stepS A x s v u j / sbar x s v j| ≤ τ ∧ |stepX A x s v u j / xbar x s v j| ≤ τ) :
    ∀ j, |stepS A x s v (u + Pi.single i a) j / sbar x s v j| ≤ τ + ρ ∧
      |stepX A x s v (u + Pi.single i a) j / xbar x s v j| ≤ τ + ρ := by
  intro j
  obtain ⟨h1, h2⟩ := single_step_bound A x s v hxb hsb c hc hcj i a j
  obtain ⟨h3, h4⟩ := hu j
  rw [stepS_add, stepX_add, add_div, add_div]
  have h0 : 0 ≤ |a| / c := by positivity
  constructor
  · calc _ ≤ |stepS A x s v u j / sbar x s v j| +
          |stepS A x s v (Pi.single i a) j / sbar x s v j| := abs_add_le _ _
      _ ≤ τ + ρ := by linarith
  · calc _ ≤ |stepX A x s v u j / xbar x s v j| +
          |stepX A x s v (Pi.single i a) j / xbar x s v j| := abs_add_le _ _
      _ ≤ τ + ρ := by linarith

lemma bias_real (dm J η ηs : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ ηs) (hηs : ηs ≤ 0.002)
    (hJ : |J| ≤ |dm| * ηs) : ((1 - η)⁻¹ * (dm - J) - dm) ^ 2 ≤ (0.0041 * dm) ^ 2 := by
  have h1 : 0 < 1 - η := by linarith
  have e : (1 - η)⁻¹ * (dm - J) - dm = (η * dm - J) / (1 - η) := by field_simp; ring
  rw [e, div_pow]
  rw [div_le_iff₀ (by positivity)]
  have h2 : |η * dm - J| ≤ 2 * ηs * |dm| := by
    calc |η * dm - J| ≤ |η * dm| + |J| := abs_sub _ _
      _ = η * |dm| + |J| := by rw [abs_mul, abs_of_nonneg hη0]
      _ ≤ ηs * |dm| + |dm| * ηs := by
          have := mul_le_mul_of_nonneg_right hη (abs_nonneg dm); linarith
      _ = 2 * ηs * |dm| := by ring
  have h3 : (η * dm - J) ^ 2 ≤ (2 * ηs * |dm|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : (2 * ηs * |dm|) ^ 2 ≤ (0.004 * |dm|) ^ 2 := by
    have : 0 ≤ ηs := hη0.trans hη
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg dm]) 2
  have h5 : (0.004 * |dm|) ^ 2 ≤ (0.0041 * dm) ^ 2 * (1 - η) ^ 2 := by
    have h6 : (0.998:ℝ) ^ 2 ≤ (1 - η) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have h7 : (0.004 * |dm|) ^ 2 = 0.000016 * dm ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [h7, mul_pow]
    have : 0 ≤ dm ^ 2 := sq_nonneg _
    nlinarith
  linarith

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
    push_neg at hcon
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

set_option maxHeartbeats 1000000 in
/-- The conditioning bias: `E_P[δ̃_μ] − δ_μ` is tiny, from Claim 4.7 applied to `1.15 δ_μ`. -/
lemma bias_bound {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (x s v δμ : Fin n → ℝ) (t k ε εmp : ℝ) (hAs : Assumption41 x s t v δμ k ε εmp)
    (hδ : ∑ i, δμ i ^ 2 ≤ (0.8667 * ε * t) ^ 2) :
    ∑ i, (∫ δ, δ i ∂(stepLaw A x s v k δμ) - δμ i) ^ 2 ≤ (0.01 * ε * t) ^ 2 := by
  have hL := one_lt_log hn
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  obtain ⟨hxb, hsb, hmu⟩ := xbar_sbar x s v δμ t k ε εmp hAs
  obtain ⟨hx, hs, ht, hap, hεmp, hεmp', hw, hε, hεle, hnorm, hk, hkge⟩ := hAs
  have hεL : ε * Real.log n ≤ 1 / 40000 := by
    rw [le_div_iff₀ (by positivity)] at hεle; linarith
  have hcj : ∀ j, 0.9 * t ≤ xbar x s v j * sbar x s v j := fun j => by
    rw [hmu]; have h := (hap j).1; dsimp only at h; linarith
  have hc : (0:ℝ) < 0.9 * t := by positivity
  have hpr : ∀ i, 0 < sampleProb k δμ i ∧ sampleProb k δμ i ≤ 1 := sampleProb_pos hn0 k hk δμ
  haveI hcl : ∀ i, IsProbabilityMeasure (coordLaw (sampleProb k δμ i) (δμ i)) :=
    fun i => coordLaw_isProb _ _ (hpr i).1 (hpr i).2
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = sampleLaw k δμ := ⟨_, rfl⟩
  have hQpi : Q = Measure.pi (fun i => coordLaw (sampleProb k δμ i) (δμ i)) := hQ
  haveI : IsProbabilityMeasure Q := by rw [hQpi]; infer_instance
  set L := Real.log n with hLdef
  have hL0 : 0 < L := by linarith
  have hD0 : 0 ≤ ∑ l, δμ l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hsD : Real.sqrt (∑ l, δμ l ^ 2) ≤ 0.8667 * ε * t := by
    rw [show 0.8667 * ε * t = Real.sqrt ((0.8667 * ε * t) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hδ
  have hk' : 40000000 * ε * Real.sqrt n * L ^ 2 ≤ k := by
    refine le_trans ?_ hkge
    rw [le_div_iff₀ hεmp]
    have : 0 ≤ ε * Real.sqrt n * L ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hεmp' this
    linarith
  -- size of one coordinate of the sample
  have hAi : ∀ i, |δμ i| / sampleProb k δμ i ≤ 0.0000251 * t / L := by
    intro i
    set D := ∑ l, δμ l ^ 2 with hD
    set u := Real.sqrt D with hu
    set X := k * (δμ i ^ 2 / D + 1 / (n:ℝ)) with hX
    have hX0 : 0 < X := by
      have : (0:ℝ) < 1 / n := by positivity
      have : 0 ≤ δμ i ^ 2 / D := div_nonneg (sq_nonneg _) hD0
      positivity
    have h1 : |δμ i| / sampleProb k δμ i ≤ |δμ i| + |δμ i| / X := by
      have e : sampleProb k δμ i = min 1 X := rfl
      rw [e]
      rcases min_cases (1:ℝ) X with ⟨hm, -⟩ | ⟨hm, -⟩
      · rw [hm, div_one]; have : 0 ≤ |δμ i| / X := by positivity
        linarith
      · rw [hm]; have : 0 ≤ |δμ i| := abs_nonneg _; linarith
    have hdi : |δμ i| ≤ u := Real.abs_le_sqrt (Finset.single_le_sum
      (f := fun l => δμ l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i))
    have h2 : |δμ i| / X ≤ u * Real.sqrt n / (2 * k) := by
      by_cases hD0' : D = 0
      · have h0 : δμ i ^ 2 ≤ 0 := by
          have := Finset.single_le_sum (f := fun l => δμ l ^ 2) (fun l _ => sq_nonneg _)
            (Finset.mem_univ i)
          rw [← hD, hD0'] at this; exact this
        have : δμ i = 0 := by nlinarith [sq_nonneg (δμ i)]
        rw [this, abs_zero, zero_div]; positivity
      · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hD0')
        have hu0 : 0 < u := Real.sqrt_pos.2 hDpos
        have hu2 : u ^ 2 = D := Real.sq_sqrt hD0
        have hm2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
        have ha2 : δμ i ^ 2 = |δμ i| ^ 2 := (sq_abs _).symm
        set m := Real.sqrt (n:ℝ) with hm
        have hmn : (n:ℝ) = m ^ 2 := hm2.symm
        have hm0 : 0 < m := hsq
        rw [div_le_div_iff₀ hX0 (by positivity), hX, ha2, ← hu2, hmn]
        have key : u * m * (k * (|δμ i| ^ 2 / u ^ 2 + 1 / m ^ 2)) -
            |δμ i| * (2 * k) = k * (m * |δμ i| - u) ^ 2 / (u * m) := by
          field_simp; ring
        have : 0 ≤ k * (m * |δμ i| - u) ^ 2 / (u * m) := by positivity
        linarith
    have h3 : u * Real.sqrt n / (2 * k) ≤ 0.8667 * t / (80000000 * L) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : u * Real.sqrt n * (80000000 * L) ≤
          0.8667 * ε * t * Real.sqrt n * (80000000 * L) := by
        have := mul_le_mul_of_nonneg_right hsD
          (show 0 ≤ Real.sqrt n * (80000000 * L) by positivity)
        linarith
      have hLL : L ≤ L ^ 2 := by nlinarith
      have h5 : 0.8667 * ε * t * Real.sqrt n * (80000000 * L) ≤
          0.8667 * t * (2 * (40000000 * ε * Real.sqrt n * L ^ 2)) := by
        have := mul_le_mul_of_nonneg_left hLL
          (show (0:ℝ) ≤ 0.8667 * ε * t * Real.sqrt n * 80000000 by positivity)
        linarith
      have h6 := mul_le_mul_of_nonneg_left hk' (show (0:ℝ) ≤ 0.8667 * t * 2 by positivity)
      linarith
    have h7 : u ≤ 0.8667 * t / (40000 * L) := by
      calc u ≤ 0.8667 * ε * t := hsD
        _ ≤ 0.8667 * t / (40000 * L) := by
          rw [le_div_iff₀ (by positivity)]
          have := mul_le_mul_of_nonneg_left hεL (show (0:ℝ) ≤ 0.8667 * t by positivity)
          linarith
    have h8 : 0.8667 * t / (40000 * L) + 0.8667 * t / (80000000 * L) ≤ 0.0000251 * t / L := by
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 < t * L ^ 2 := by positivity
      nlinarith
    linarith
  -- the good sets
  set τ0 := 1 / (100 * L) with hτ0
  set ρ := 0.0001 / L with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  obtain ⟨Gd, hGd⟩ : ∃ Gd : ℝ → Set (Fin n → ℝ), Gd = fun τ => {δ | ∀ j,
      |stepS A x s v δ j / sbar x s v j| ≤ τ ∧ |stepX A x s v δ j / xbar x s v j| ≤ τ} :=
    ⟨_, rfl⟩
  have hGdm : ∀ τ, MeasurableSet (Gd τ) := by
    intro τ
    have e : Gd τ = ⋂ j, ({δ | |stepS A x s v δ j / sbar x s v j| ≤ τ} ∩
        {δ | |stepX A x s v δ j / xbar x s v j| ≤ τ}) := by
      rw [hGd]; ext δ; simp
    rw [e]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le ((cont_stepS A x s v j).div_const _).abs.measurable measurable_const).inter
      (measurableSet_le ((cont_stepX A x s v j).div_const _).abs.measurable measurable_const)
  have hS : successEvent A x s v = Gd τ0 := by rw [hGd]; rfl
  have hSm : MeasurableSet (successEvent A x s v) := by rw [hS]; exact hGdm _
  have hρA : ∀ i (a : ℝ), |a| ≤ |δμ i| / sampleProb k δμ i → 2 * (|a| / (0.9 * t)) ≤ ρ := by
    intro i a ha
    have h0 := ha.trans (hAi i)
    have h1 : |a| / (0.9 * t) ≤ (0.0000251 * t / L) / (0.9 * t) :=
      div_le_div_of_nonneg_right h0 hc.le
    have h2 : (0.0000251 * t / L) / (0.9 * t) = 0.0000251 / 0.9 / L := by
      field_simp
    have h3 : 2 * (0.0000251 / 0.9 / L) ≤ 0.0001 / L := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by norm_num) hL0.le
    rw [hρ]; linarith
  have hsplit : ∀ (δ : Fin n → ℝ) i, δ = Function.update δ i 0 + Pi.single i (δ i) := by
    intro δ i; funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h, Function.update_of_ne h]
  have hsplit' : ∀ (δ : Fin n → ℝ) i, Function.update δ i 0 = δ + Pi.single i (-δ i) := by
    intro δ i; funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h, Function.update_of_ne h]
  have P1 : ∀ (δ : Fin n → ℝ) i τ, |δ i| ≤ |δμ i| / sampleProb k δμ i →
      Function.update δ i 0 ∈ Gd τ → δ ∈ Gd (τ + ρ) := by
    intro δ i τ hδ hu
    simp only [hGd, Set.mem_setOf_eq] at hu ⊢
    have := perturb_good A x s v hxb hsb (0.9 * t) hc hcj (Function.update δ i 0) i (δ i) ρ τ
      (hρA i _ hδ) hu
    rwa [← hsplit δ i] at this
  have P2 : ∀ (δ : Fin n → ℝ) i τ, |δ i| ≤ |δμ i| / sampleProb k δμ i →
      δ ∈ Gd τ → Function.update δ i 0 ∈ Gd (τ + ρ) := by
    intro δ i τ hδ hu
    simp only [hGd, Set.mem_setOf_eq] at hu ⊢
    have := perturb_good A x s v hxb hsb (0.9 * t) hc hcj δ i (-δ i) ρ τ
      (by rw [abs_neg]; exact hρA i _ hδ) hu
    rwa [← hsplit' δ i] at this
  have hsupp : ∀ i, ∀ᵐ δ ∂Q, |δ i| ≤ |δμ i| / sampleProb k δμ i := by
    intro i; rw [hQpi]
    exact ae_coord_le _ i _ (coordLaw_bad _ _ (hpr i).1)
  -- Claim 4.7 at `1.15 δ_μ`
  have hnorm' : norm2 ((1.15:ℝ) • δμ) ≤ ε * t := by
    unfold norm2
    have e : ∑ i, ((1.15:ℝ) • δμ) i ^ 2 = 1.3225 * ∑ i, δμ i ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    calc Real.sqrt (1.3225 * ∑ i, δμ i ^ 2) ≤ Real.sqrt ((ε * t) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [hδ, sq_nonneg (ε * t)])
      _ = ε * t := Real.sqrt_sq (by positivity)
  have hAs2 : Assumption41 x s t v ((1.15:ℝ) • δμ) k ε εmp :=
    ⟨hx, hs, ht, hap, hεmp, hεmp', hw, hε, hεle, hnorm', hk, hkge⟩
  obtain ⟨-, h47⟩ := L47_sp_main hn A hA x s v ((1.15:ℝ) • δμ) t k ε εmp hAs2
  rw [sampleLaw_smul k δμ 1.15 (by norm_num), ← hQ] at h47
  set ηs := 2 * n * Real.exp (-(0.003 * k / (ε * Real.sqrt n * Real.log n))) with hηs
  have hηs0 : 0 ≤ ηs := by positivity
  have hηs2 : ηs ≤ 0.002 := by
    have hy : 4 * L ≤ 0.003 * k / (ε * Real.sqrt n * L) := by
      rw [le_div_iff₀ (by positivity)]
      have : 0 ≤ ε * Real.sqrt n * L ^ 2 := by positivity
      nlinarith
    have h1 : Real.exp (-(0.003 * k / (ε * Real.sqrt n * L))) ≤ Real.exp (-(4 * L)) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-(4 * L)) = ((n:ℝ) ^ 4)⁻¹ := by
      rw [Real.exp_neg, show 4 * L = ((4:ℕ):ℝ) * L by norm_num, Real.exp_nat_mul, hLdef,
        Real.exp_log (by linarith)]
    have h3 : 2 * (n:ℝ) * ((n:ℝ) ^ 4)⁻¹ ≤ 0.002 := by
      rw [show 2 * (n:ℝ) * ((n:ℝ) ^ 4)⁻¹ = 2 / (n:ℝ) ^ 3 by field_simp]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10) hn' 3]
    calc ηs = 2 * n * Real.exp (-(0.003 * k / (ε * Real.sqrt n * L))) := rfl
      _ ≤ 2 * n * ((n:ℝ) ^ 4)⁻¹ := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 0.002 := h3
  have hgood : ENNReal.ofReal (1 - ηs) ≤ Q (Gd (τ0 - ρ - ρ)) := by
    have hsub : ∀ δ : Fin n → ℝ, (∀ i, |stepS A x s v δ i / sbar x s v i| ≤ 0.01 / Real.log n ∧
        |stepS A x s v δ i / s i| ≤ 0.02 / Real.log n ∧
        |stepX A x s v δ i / xbar x s v i| ≤ 0.01 / Real.log n ∧
        |stepX A x s v δ i / x i| ≤ 0.02 / Real.log n ∧
        |δ i / (x i * s i)| ≤ 0.02 / Real.log n) → δ ∈ Gd (0.01 / L) := by
      intro δ hδ
      simp only [hGd, Set.mem_setOf_eq]
      exact fun j => ⟨(hδ j).1, (hδ j).2.2.1⟩
    refine h47.trans ((measure_mono hsub).trans ?_)
    rw [Measure.map_apply (measurable_const_smul _) (hGdm _)]
    apply measure_mono
    intro δ hδ
    simp only [Set.mem_preimage, hGd, Set.mem_setOf_eq] at hδ ⊢
    have hb : 0.01 / L / 1.15 ≤ τ0 - ρ - ρ := by
      rw [hτ0, hρ]
      have e1 : 0.01 / L / 1.15 = (0.01 / 1.15) / L := by ring
      have e2 : 1 / (100 * L) - 0.0001 / L - 0.0001 / L = 0.0098 / L := by
        field_simp; ring
      rw [e1, e2]; exact div_le_div_of_nonneg_right (by norm_num) hL0.le
    intro j
    obtain ⟨h1, h2⟩ := hδ j
    rw [stepS_smul, mul_div_assoc, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.15)] at h1
    rw [stepX_smul, mul_div_assoc, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.15)] at h2
    constructor
    · have : |stepS A x s v δ j / sbar x s v j| ≤ 0.01 / L / 1.15 := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
    · have : |stepX A x s v δ j / xbar x s v j| ≤ 0.01 / L / 1.15 := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
  have hQG : Q.real (Gd (τ0 - ρ - ρ))ᶜ ≤ ηs := by
    rw [probReal_compl_eq_one_sub (hGdm _)]
    have := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hgood
    simp only [Measure.real]; linarith
  -- moments of one coordinate
  have hint : ∀ i, Integrable (fun δ : Fin n → ℝ => δ i) Q := fun i =>
    Integrable.of_bound (continuous_apply i).aestronglyMeasurable _
      (by filter_upwards [hsupp i] with δ hδ; rw [Real.norm_eq_abs]; exact hδ)
  have hEi : ∀ i, ∫ δ, δ i ∂Q = δμ i := by
    intro i
    have h1 := integral_coord (fun j => coordLaw (sampleProb k δμ j) (δμ j)) i (fun y => y)
      measurable_id
    rw [hQpi, h1, integral_coordLaw _ _ (hpr i).1 (hpr i).2]
    have := (hpr i).1.ne'
    field_simp; ring
  have hEabs : ∀ i, ∫ δ, |δ i| ∂Q = |δμ i| := by
    intro i
    have h1 := integral_coord (fun j => coordLaw (sampleProb k δμ j) (δμ j)) i (fun y => |y|)
      continuous_abs.measurable
    rw [hQpi, h1, integral_coordLaw _ _ (hpr i).1 (hpr i).2, abs_div, abs_of_pos (hpr i).1,
      abs_zero]
    have := (hpr i).1.ne'
    field_simp; ring
  have hJ : ∀ i, |∫ δ in (successEvent A x s v)ᶜ, δ i ∂Q| ≤ |δμ i| * ηs := by
    intro i
    have hupd : Measurable (fun δ : Fin n → ℝ => Function.update δ i 0) := by
      refine measurable_pi_lambda _ fun j => ?_
      by_cases h : j = i
      · subst h; simpa using measurable_const
      · simp only [Function.update_of_ne h]; exact measurable_pi_apply j
    have hH : MeasurableSet (Gd (τ0 - ρ))ᶜ := (hGdm _).compl
    have hpt : ∀ᵐ δ ∂Q, (successEvent A x s v)ᶜ.indicator (fun δ => |δ i|) δ ≤
        |δ i| * (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0) := by
      filter_upwards [hsupp i] with δ hδ
      by_cases hmem : δ ∈ (successEvent A x s v)ᶜ
      · rw [Set.indicator_of_mem hmem]
        have : Function.update δ i 0 ∈ (Gd (τ0 - ρ))ᶜ := by
          intro hu
          apply hmem
          have := P1 δ i (τ0 - ρ) hδ hu
          rw [hS]; simpa using this
        rw [Set.indicator_of_mem this]; simp
      · rw [Set.indicator_of_notMem hmem]
        exact mul_nonneg (abs_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hI1 : Integrable (fun δ : Fin n → ℝ =>
        |δ i| * (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0)) Q := by
      refine Integrable.of_bound ?_ (|δμ i| / sampleProb k δμ i) ?_
      · exact ((continuous_apply i).abs.measurable.mul
          ((measurable_const.indicator hH).comp hupd)).aestronglyMeasurable
      · filter_upwards [hsupp i] with δ hδ
        rw [Real.norm_eq_abs, abs_mul, abs_abs]
        have h0 : 0 ≤ (Gd (τ0 - ρ))ᶜ.indicator (1 : (Fin n → ℝ) → ℝ) (Function.update δ i 0) :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) _
        have h1 : (Gd (τ0 - ρ))ᶜ.indicator (1 : (Fin n → ℝ) → ℝ) (Function.update δ i 0) ≤ 1 :=
          Set.indicator_le_self' (fun _ _ => zero_le_one) _
        rw [abs_of_nonneg h0]
        calc |δ i| * (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0) ≤ |δ i| * 1 :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact hδ
    have hind := indep_update (fun j => coordLaw (sampleProb k δμ j) (δμ j)) i _ hH
    rw [← hQpi] at hind
    calc |∫ δ in (successEvent A x s v)ᶜ, δ i ∂Q|
        ≤ ∫ δ in (successEvent A x s v)ᶜ, |δ i| ∂Q := abs_integral_le_integral_abs
      _ = ∫ δ, (successEvent A x s v)ᶜ.indicator (fun δ => |δ i|) δ ∂Q :=
          (integral_indicator hSm.compl).symm
      _ ≤ ∫ δ, |δ i| * (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0) ∂Q :=
          integral_mono_ae ((hint i).abs.indicator hSm.compl) hI1 hpt
      _ = (∫ δ, |δ i| ∂Q) * ∫ δ, (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0) ∂Q := hind
      _ ≤ |δμ i| * ηs := by
          rw [hEabs i]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have e : (fun δ : Fin n → ℝ =>
              (Gd (τ0 - ρ))ᶜ.indicator (1 : (Fin n → ℝ) → ℝ) (Function.update δ i 0)) =
              ((fun δ => Function.update δ i 0) ⁻¹' (Gd (τ0 - ρ))ᶜ).indicator 1 := by
            funext δ; rfl
          rw [e, integral_indicator_one (hupd hH)]
          refine le_trans ?_ hQG
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          apply measure_mono_ae
          filter_upwards [hsupp i] with δ hδ
          intro hmem hg
          apply hmem
          have := P2 δ i (τ0 - ρ - ρ) hδ hg
          simpa using this
  -- assembly
  have hcond : ∀ i, ∫ δ, δ i ∂(stepLaw A x s v k δμ) =
      (Q.real (successEvent A x s v))⁻¹ * (δμ i - ∫ δ in (successEvent A x s v)ᶜ, δ i ∂Q) := by
    intro i
    have h1 := integral_add_compl hSm (hint i)
    rw [hEi i] at h1
    unfold stepLaw
    rw [← hQ, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
    simp only [Measure.real]
    congr 1
    linarith
  have hη : Q.real (successEvent A x s v)ᶜ ≤ ηs := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hQG
    rw [hS]
    exact Set.compl_subset_compl.2 (fun δ hδ => by
      simp only [hGd, Set.mem_setOf_eq] at hδ ⊢
      exact fun j => ⟨(hδ j).1.trans (by linarith), (hδ j).2.trans (by linarith)⟩)
  have hQS : Q.real (successEvent A x s v) = 1 - Q.real (successEvent A x s v)ᶜ := by
    rw [probReal_compl_eq_one_sub hSm]; ring
  have hterm : ∀ i, (∫ δ, δ i ∂(stepLaw A x s v k δμ) - δμ i) ^ 2 ≤ (0.0041 * δμ i) ^ 2 := by
    intro i
    rw [hcond i, hQS]
    exact bias_real (δμ i) _ _ ηs measureReal_nonneg hη hηs2 (hJ i)
  calc ∑ i, (∫ δ, δ i ∂(stepLaw A x s v k δμ) - δμ i) ^ 2
      ≤ ∑ i, (0.0041 * δμ i) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = 0.0041 ^ 2 * ∑ i, δμ i ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (0.01 * ε * t) ^ 2 := by nlinarith [hδ, sq_nonneg (ε * t)]

end CohenLeeSongLP.StochCentralPath.L413

namespace CohenLeeSongLP.StochCentralPath.L48

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

lemma coordLaw_bad (p a : ℝ) (hp0 : 0 < p) : coordLaw p a {y | |a| / p < |y|} = 0 := by
  have hm : MeasurableSet {y : ℝ | |a| / p < |y|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  unfold coordLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hm,
    Measure.dirac_apply' _ hm]
  have hA : a / p ∉ {y : ℝ | |a| / p < |y|} := by
    simp only [Set.mem_setOf_eq, abs_div, abs_of_pos hp0, not_lt]; exact le_rfl
  have hZ : (0:ℝ) ∉ {y : ℝ | |a| / p < |y|} := by
    simp only [Set.mem_setOf_eq, abs_zero, not_lt]; positivity
  rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hZ]; simp

lemma integral_coord {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ δ, f (δ i) ∂(Measure.pi μs) = ∫ y, f y ∂(μs i) := by
  have := integral_map (μ := Measure.pi μs) (measurable_pi_apply i).aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [(measurePreserving_eval μs i).map_eq] at this
  exact this.symm

lemma ae_coord_le {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (B : ℝ) (h : μs i {y | B < |y|} = 0) :
    ∀ᵐ δ ∂(Measure.pi μs), |δ i| ≤ B := by
  rw [ae_iff]
  have hm : MeasurableSet {y : ℝ | B < |y|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have := (measurePreserving_eval μs i).measure_preimage hm.nullMeasurableSet
  simp only [not_le]
  rw [show {a : Fin n → ℝ | B < |a i|} = Function.eval i ⁻¹' {y | B < |y|} from rfl, this, h]

/-- Second moment of a linear functional of the product of two-point laws. -/
lemma second_moment_Q {n : ℕ} (p a : Fin n → ℝ) (hp0 : ∀ j, 0 < p j) (hp1 : ∀ j, p j ≤ 1)
    (V : ℝ) (hV : ∀ j, a j ^ 2 * (1 - p j) / p j ≤ V) (c : Fin n → ℝ) :
    Integrable (fun δ => (∑ j, c j * (δ j - a j)) ^ 2)
        (Measure.pi fun j => coordLaw (p j) (a j)) ∧
    ∫ δ, (∑ j, c j * (δ j - a j)) ^ 2 ∂(Measure.pi fun j => coordLaw (p j) (a j))
      ≤ V * ∑ j, c j ^ 2 := by
  haveI : ∀ j, IsProbabilityMeasure (coordLaw (p j) (a j)) :=
    fun j => coordLaw_isProb _ _ (hp0 j) (hp1 j)
  set μs : Fin n → Measure ℝ := fun j => coordLaw (p j) (a j) with hμs
  let X : Fin n → ℝ → ℝ := fun j y => c j * (y - a j)
  have hXm : ∀ j, Measurable (X j) := fun j => by fun_prop
  have hL2 : ∀ j, MemLp (X j) 2 (μs j) := by
    intro j
    refine MemLp.of_bound (hXm j).aestronglyMeasurable (|c j| * (|a j| / p j + |a j|)) ?_
    have h : ∀ᵐ y ∂(μs j), |y| ≤ |a j| / p j := by
      rw [ae_iff]; simpa [not_le] using coordLaw_bad (p j) (a j) (hp0 j)
    filter_upwards [h] with y hy
    rw [Real.norm_eq_abs]
    simp only [X]
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc |y - a j| ≤ |y| + |a j| := abs_sub _ _
      _ ≤ _ := by linarith
  have hmean : ∀ j, ∫ y, X j y ∂(μs j) = 0 := by
    intro j
    simp only [hμs, X]
    rw [integral_coordLaw _ _ (hp0 j) (hp1 j)]
    have := (hp0 j).ne'
    field_simp
    ring
  have hsq : ∀ j, ∫ y, (X j y) ^ 2 ∂(μs j) = c j ^ 2 * (a j ^ 2 * (1 - p j) / p j) := by
    intro j
    simp only [hμs, X]
    rw [integral_coordLaw _ _ (hp0 j) (hp1 j)]
    have := (hp0 j).ne'
    field_simp
    ring
  have hvarj : ∀ j, variance (X j) (μs j) = c j ^ 2 * (a j ^ 2 * (1 - p j) / p j) := by
    intro j
    rw [variance_eq_sub (hL2 j)]
    simp only [Pi.pow_apply]
    rw [hsq j, hmean j]; ring
  have hvar := variance_sum_pi (μ := μs) (X := X) hL2
  have hLS : ∀ j, MemLp (fun ω : Fin n → ℝ => X j (ω j)) 2 (Measure.pi μs) :=
    fun j => (hL2 j).comp_measurePreserving (measurePreserving_eval μs j)
  have hS2 : MemLp (∑ j, fun ω : Fin n → ℝ => X j (ω j)) 2 (Measure.pi μs) :=
    memLp_finsetSum' _ (fun j _ => hLS j)
  have hES : ∫ ω, (∑ j, fun ω : Fin n → ℝ => X j (ω j)) ω ∂(Measure.pi μs) = 0 := by
    simp only [Finset.sum_apply]
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [integral_coord μs j (X j) (hXm j), hmean j]
    · exact fun j _ => (hLS j).integrable (by norm_num)
  have hV2 := variance_eq_sub hS2
  rw [hvar] at hV2
  simp only [Pi.pow_apply] at hV2
  have hES' : (Measure.pi μs)[∑ j, fun ω : Fin n → ℝ => X j (ω j)] = 0 := hES
  rw [hES'] at hV2
  have e : ∫ δ, (∑ j, c j * (δ j - a j)) ^ 2 ∂(Measure.pi μs) =
      ∫ ω, ((∑ j, fun ω : Fin n → ℝ => X j (ω j)) ω) ^ 2 ∂(Measure.pi μs) := by
    simp only [Finset.sum_apply, X]
  have hInt : Integrable (fun δ => (∑ j, c j * (δ j - a j)) ^ 2) (Measure.pi μs) := by
    have := hS2.integrable_sq
    refine this.congr (Filter.Eventually.of_forall fun δ => ?_)
    simp only [Finset.sum_apply, X]
  refine ⟨hInt, ?_⟩
  rw [e]
  have : ∫ ω, ((∑ j, fun ω : Fin n → ℝ => X j (ω j)) ω) ^ 2 ∂(Measure.pi μs) =
      ∑ j, variance (X j) (μs j) := by linarith
  rw [this]
  calc ∑ j, variance (X j) (μs j) = ∑ j, c j ^ 2 * (a j ^ 2 * (1 - p j) / p j) :=
        Finset.sum_congr rfl fun j _ => hvarj j
    _ ≤ ∑ j, c j ^ 2 * V := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hV j) (sq_nonneg _)
    _ = V * ∑ j, c j ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

/-- Integrals against the conditional measure are bounded by the unconditional integral. -/
lemma cond_integral_le {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (S : Set Ω) (F : Ω → ℝ) (hF0 : ∀ ω, 0 ≤ F ω)
    (hFi : Integrable F Q) :
    ∫ ω, F ω ∂(Q[|S]) ≤ (Q.real S)⁻¹ * ∫ ω, F ω ∂Q := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ENNReal.toReal_nonneg)
  exact setIntegral_le_integral hFi (Filter.Eventually.of_forall hF0)



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


lemma projBar_symm_idem {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (xb sb : Fin n → ℝ)
    (hx : ∀ i, 0 < xb i) (hs : ∀ i, 0 < sb i) :
    (projBar A xb sb).transpose = projBar A xb sb ∧
      projBar A xb sb * projBar A xb sb = projBar A xb sb := by
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
  refine ⟨hsym, ?_⟩
  calc P * P = P.transpose * P := by rw [hsym]
    _ = P := hPP

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

lemma projBar_opnorm {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (xb sb : Fin n → ℝ)
    (hx : ∀ i, 0 < xb i) (hs : ∀ i, 0 < sb i) (z : Fin n → ℝ) :
    ∑ i, (∑ j, projBar A xb sb i j * z j) ^ 2 ≤ ∑ j, z j ^ 2 ∧
    ∑ i, (∑ j, ((1 : Matrix (Fin n) (Fin n) ℝ) i j - projBar A xb sb i j) * z j) ^ 2
      ≤ ∑ j, z j ^ 2 := by
  obtain ⟨hsym, hPP⟩ := projBar_symm_idem A xb sb hx hs
  set P := projBar A xb sb with hPdef
  set u : Fin n → ℝ := P.mulVec z with hu
  have hui : ∀ i, u i = ∑ j, P i j * z j := fun i => by simp [hu, Matrix.mulVec, dotProduct]
  have hPu : P.mulVec u = u := by rw [hu, Matrix.mulVec_mulVec, hPP]
  have hvec : Matrix.vecMul u P = u := by
    calc Matrix.vecMul u P = Matrix.vecMul u P.transpose := by rw [hsym]
      _ = P.mulVec u := Matrix.vecMul_transpose P u
      _ = u := hPu
  have key : dotProduct u u = dotProduct u z := by
    have h1 : dotProduct u u = dotProduct u (P.mulVec z) := rfl
    rw [h1, Matrix.dotProduct_mulVec, hvec]
  simp only [dotProduct, ← sq] at key
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u z
  have hA0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB0 : 0 ≤ ∑ j, z j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAB : ∑ i, u i ^ 2 ≤ ∑ j, z j ^ 2 := by
    rw [key] at hcs
    rw [← key] at hcs
    nlinarith [hcs, hA0, hB0]
  refine ⟨?_, ?_⟩
  · simpa only [hui] using hAB
  · have e : ∀ i, ∑ j, ((1 : Matrix (Fin n) (Fin n) ℝ) i j - P i j) * z j = z i - u i := by
      intro i
      simp only [sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, hui]
    simp only [e]
    have e2 : ∑ i, (z i - u i) ^ 2 = ∑ j, z j ^ 2 - 2 * ∑ i, u i * z i + ∑ i, u i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e2, ← key]
    linarith

lemma coef_opnorm {n : ℕ} (q : Fin n → Fin n → ℝ) (R : Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (hR : ∀ j, 0.9 * t ≤ R j ^ 2) (hRpos : ∀ j, 0 < R j)
    (hq : ∀ z : Fin n → ℝ, ∑ i, (∑ j, q i j * z j) ^ 2 ≤ ∑ j, z j ^ 2) (z : Fin n → ℝ) :
    ∑ i, (∑ j, q i j / (R j * R i) * z j) ^ 2 ≤ (1 / (0.9 * t)) ^ 2 * ∑ j, z j ^ 2 := by
  have h9 : 0 < 0.9 * t := by positivity
  set z' : Fin n → ℝ := fun j => z j / R j with hz'
  have e : ∀ i, ∑ j, q i j / (R j * R i) * z j = (∑ j, q i j * z' j) / R i := by
    intro i
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hz']
    have := (hRpos j).ne'
    have := (hRpos i).ne'
    field_simp
  calc ∑ i, (∑ j, q i j / (R j * R i) * z j) ^ 2
      = ∑ i, (∑ j, q i j * z' j) ^ 2 / R i ^ 2 := by simp_rw [e, div_pow]
    _ ≤ ∑ i, (∑ j, q i j * z' j) ^ 2 / (0.9 * t) :=
        Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (sq_nonneg _) h9 (hR i)
    _ = (∑ i, (∑ j, q i j * z' j) ^ 2) / (0.9 * t) := by rw [Finset.sum_div]
    _ ≤ (∑ j, z' j ^ 2) / (0.9 * t) := div_le_div_of_nonneg_right (hq z') h9.le
    _ ≤ (∑ j, z j ^ 2 / (0.9 * t)) / (0.9 * t) := by
        apply div_le_div_of_nonneg_right _ h9.le
        refine Finset.sum_le_sum fun j _ => ?_
        simp only [hz']
        rw [div_pow]
        exact div_le_div_of_nonneg_left (sq_nonneg _) h9 (hR j)
    _ = (1 / (0.9 * t)) ^ 2 * ∑ j, z j ^ 2 := by
        rw [← Finset.sum_div, div_div]
        field_simp

lemma rho_bounds {n : ℕ} (x s v δμ : Fin n → ℝ) (t k ε εmp : ℝ)
    (hAs : Assumption41 x s t v δμ k ε εmp) (i : Fin n) :
    0.9999 ≤ xbar x s v i / x i ∧ xbar x s v i / x i ≤ 1.0001 := by
  obtain ⟨hx, hs, -, -, hεmp, hεmp1, hw, -, -, -, -, -⟩ := hAs
  have hw0 : 0 < x i / s i := div_pos (hx i) (hs i)
  obtain ⟨h1, h2⟩ := hw i
  have hv : 0 < v i := by nlinarith
  have e : xbar x s v i / x i = Real.sqrt (v i / (x i / s i)) := by
    unfold xbar
    have := (hx i).ne'
    field_simp
  rw [e]
  have h3 : εmp * v i ≤ v i / 40000 := by nlinarith
  have hlo : 0.9999 ≤ v i / (x i / s i) := by
    rw [le_div_iff₀ hw0]; nlinarith
  have hhi : v i / (x i / s i) ≤ 1.0001 := by
    rw [div_le_iff₀ hw0]; nlinarith
  constructor
  · calc (0.9999:ℝ) = Real.sqrt (0.9999 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  · calc Real.sqrt (v i / (x i / s i)) ≤ Real.sqrt (1.0001 ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1.0001 := Real.sqrt_sq (by norm_num)



lemma two_sq (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

lemma bdd_memLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (C : ℝ) (hf : Measurable f) (hC : ∀ᵐ ω ∂P, |f ω| ≤ C) : MemLp f 2 P :=
  MemLp.of_bound hf.aestronglyMeasurable C (by
    filter_upwards [hC] with ω hω; rwa [Real.norm_eq_abs])

lemma var_le_sq_center {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X P) (c : ℝ) :
    variance X P ≤ ∫ ω, (X ω - c) ^ 2 ∂P := by
  have h := variance_le_expectation_sq (μ := P) (X := fun ω => X ω - c)
    (hX.sub aestronglyMeasurable_const)
  rw [variance_sub_const hX c] at h
  simpa [Pi.pow_apply] using h

lemma abs_mean_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (C : ℝ) (hC : ∀ᵐ ω ∂P, |f ω| ≤ C) : |∫ ω, f ω ∂P| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := C)
    (by filter_upwards [hC] with ω hω; rwa [Real.norm_eq_abs])
  simpa using this

lemma cov_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → ℝ) (C : ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfC : ∀ᵐ ω ∂P, |f ω| ≤ C) (hgC : ∀ᵐ ω ∂P, |g ω| ≤ C) :
    |∫ ω, f ω * g ω ∂P - (∫ ω, f ω ∂P) * (∫ ω, g ω ∂P)|
      ≤ (variance f P + variance g P) / 2 := by
  have hfL := bdd_memLp P f C hf hfC
  have hgL := bdd_memLp P g C hg hgC
  have h1 := covariance_eq_sub hfL hgL
  have h2 : covariance f g P = ∫ ω, (f ω - P[f]) * (g ω - P[g]) ∂P := rfl
  have hFL : MemLp (fun ω => f ω - P[f]) 2 P := hfL.sub (memLp_const _)
  have hGL : MemLp (fun ω => g ω - P[g]) 2 P := hgL.sub (memLp_const _)
  have hV1 : variance f P = ∫ ω, (f ω - P[f]) ^ 2 ∂P := variance_eq_integral hf.aemeasurable
  have hV2 : variance g P = ∫ ω, (g ω - P[g]) ^ 2 ∂P := variance_eq_integral hg.aemeasurable
  have e : ∫ ω, f ω * g ω ∂P - (∫ ω, f ω ∂P) * (∫ ω, g ω ∂P) =
      ∫ ω, (f ω - P[f]) * (g ω - P[g]) ∂P := by
    rw [← h2, h1]; simp [Pi.mul_apply]
  rw [e]
  have hI1 : Integrable (fun ω => (f ω - P[f]) * (g ω - P[g])) P := hFL.integrable_mul hGL
  have hI2 : Integrable (fun ω => ((f ω - P[f]) ^ 2 + (g ω - P[g]) ^ 2) / 2) P :=
    (hFL.integrable_sq.add hGL.integrable_sq).div_const 2
  calc |∫ ω, (f ω - P[f]) * (g ω - P[g]) ∂P| ≤ ∫ ω, |(f ω - P[f]) * (g ω - P[g])| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, ((f ω - P[f]) ^ 2 + (g ω - P[g]) ^ 2) / 2 ∂P := by
        refine integral_mono hI1.abs hI2 fun ω => ?_
        rw [abs_mul]
        nlinarith [sq_abs (f ω - P[f]), sq_abs (g ω - P[g]), sq_nonneg (|f ω - P[f]| - |g ω - P[g]|)]
    _ = (variance f P + variance g P) / 2 := by
        rw [integral_div, integral_add hFL.integrable_sq hGL.integrable_sq, hV1, hV2]

lemma mean_decomp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → ℝ) (C ρ : ℝ) (hρ : ρ ≠ 0) (hf : Measurable f) (hg : Measurable g)
    (hfC : ∀ᵐ ω ∂P, |f ω| ≤ C) (hgC : ∀ᵐ ω ∂P, |g ω| ≤ C) :
    ∫ ω, ((1 + ρ * g ω) * (1 + f ω / ρ) - 1 - f ω - g ω) ∂P =
      (ρ - 1) * ∫ ω, g ω ∂P + (1 / ρ - 1) * ∫ ω, f ω ∂P + ∫ ω, f ω * g ω ∂P := by
  have hfL := bdd_memLp P f C hf hfC
  have hgL := bdd_memLp P g C hg hgC
  have hfi : Integrable f P := hfL.integrable one_le_two
  have hgi : Integrable g P := hgL.integrable one_le_two
  have hfg : Integrable (fun ω => f ω * g ω) P := hfL.integrable_mul hgL
  have hpt : ∀ ω, (1 + ρ * g ω) * (1 + f ω / ρ) - 1 - f ω - g ω =
      (ρ - 1) * g ω + (1 / ρ - 1) * f ω + f ω * g ω := by
    intro ω; field_simp; ring
  have hA : Integrable (fun ω => (ρ - 1) * g ω + (1 / ρ - 1) * f ω) P :=
    (hgi.const_mul _).add (hfi.const_mul _)
  simp_rw [hpt]
  rw [integral_add hA hfg, integral_add (hgi.const_mul _) (hfi.const_mul _), integral_const_mul,
    integral_const_mul]

lemma var_bound_X {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → ℝ) (ρ τ : ℝ) (hρ0 : 0.9999 ≤ ρ) (hρ1 : ρ ≤ 1.0001)
    (hf : Measurable f) (hg : Measurable g)
    (hfC : ∀ᵐ ω ∂P, |f ω| ≤ 0.01) (hgC : ∀ᵐ ω ∂P, |g ω| ≤ 0.01)
    (hVf : variance f P ≤ τ) (hVg : variance g P ≤ τ) :
    variance (fun ω => (1 + ρ * g ω) * (1 + f ω / ρ)) P ≤ 5 * τ := by
  have hρpos : 0 < ρ := by linarith
  have hfL := bdd_memLp P f 0.01 hf hfC
  have hgL := bdd_memLp P g 0.01 hg hgC
  have hMf := abs_mean_le P f 0.01 hfC
  have hMg := abs_mean_le P g 0.01 hgC
  set Mf := ∫ ω, f ω ∂P with hMfdef
  set Mg := ∫ ω, g ω ∂P with hMgdef
  have hXm : Measurable (fun ω => (1 + ρ * g ω) * (1 + f ω / ρ)) := by fun_prop
  set c : ℝ := 1 + ρ * Mg + Mf / ρ + Mf * Mg with hc
  have h1 := var_le_sq_center P _ hXm.aestronglyMeasurable c
  have hFL : MemLp (fun ω => f ω - Mf) 2 P := hfL.sub (memLp_const _)
  have hGL : MemLp (fun ω => g ω - Mg) 2 P := hgL.sub (memLp_const _)
  have hV1 : variance f P = ∫ ω, (f ω - Mf) ^ 2 ∂P := variance_eq_integral hf.aemeasurable
  have hV2 : variance g P = ∫ ω, (g ω - Mg) ^ 2 ∂P := variance_eq_integral hg.aemeasurable
  have hdom : Integrable (fun ω => 2.2 * (g ω - Mg) ^ 2 + 2.1 * (f ω - Mf) ^ 2) P :=
    (hGL.integrable_sq.const_mul _).add (hFL.integrable_sq.const_mul _)
  have hpt : ∀ᵐ ω ∂P, ((1 + ρ * g ω) * (1 + f ω / ρ) - c) ^ 2 ≤
      2.2 * (g ω - Mg) ^ 2 + 2.1 * (f ω - Mf) ^ 2 := by
    filter_upwards [hfC, hgC] with ω hf1 hg1
    have e : (1 + ρ * g ω) * (1 + f ω / ρ) - c =
        (ρ + Mf) * (g ω - Mg) + (1 / ρ + Mg) * (f ω - Mf) + (f ω - Mf) * (g ω - Mg) := by
      simp only [hc]; field_simp; ring
    rw [e]
    obtain ⟨hf1l, hf1r⟩ := abs_le.1 hf1
    obtain ⟨hg1l, hg1r⟩ := abs_le.1 hg1
    obtain ⟨hMfl, hMfr⟩ := abs_le.1 hMf
    obtain ⟨hMgl, hMgr⟩ := abs_le.1 hMg
    set Zf := f ω - Mf with hZf
    set Zg := g ω - Mg with hZg
    have hZf2 : |Zf| ≤ 0.02 := abs_le.2 ⟨by linarith, by linarith⟩
    have hZg2 : |Zg| ≤ 0.02 := abs_le.2 ⟨by linarith, by linarith⟩
    have hinv : 1 / ρ ≤ 1.0002 := by
      rw [div_le_iff₀ hρpos]; nlinarith
    have hinv0 : 0 < 1 / ρ := by positivity
    have ha : |ρ + Mf| ≤ 1.0101 := abs_le.2 ⟨by linarith, by linarith⟩
    have hb : |1 / ρ + Mg| ≤ 1.0102 := abs_le.2 ⟨by linarith, by linarith⟩
    have hsum : |(ρ + Mf) * Zg + (1 / ρ + Mg) * Zf + Zf * Zg| ≤
        1.0301 * |Zg| + 1.0102 * |Zf| := by
      calc |(ρ + Mf) * Zg + (1 / ρ + Mg) * Zf + Zf * Zg|
          ≤ |(ρ + Mf) * Zg| + |(1 / ρ + Mg) * Zf| + |Zf * Zg| := abs_add_three _ _ _
        _ = |ρ + Mf| * |Zg| + |1 / ρ + Mg| * |Zf| + |Zf| * |Zg| := by
            rw [abs_mul, abs_mul, abs_mul]
        _ ≤ 1.0101 * |Zg| + 1.0102 * |Zf| + 0.02 * |Zg| := by
            have h1' := mul_le_mul_of_nonneg_right ha (abs_nonneg Zg)
            have h2' := mul_le_mul_of_nonneg_right hb (abs_nonneg Zf)
            have h3' := mul_le_mul_of_nonneg_right hZf2 (abs_nonneg Zg)
            linarith
        _ = 1.0301 * |Zg| + 1.0102 * |Zf| := by ring
    set E := (ρ + Mf) * Zg + (1 / ρ + Mg) * Zf + Zf * Zg with hE
    have hE0 : 0 ≤ |E| := abs_nonneg E
    have hsq : E ^ 2 ≤ (1.0301 * |Zg| + 1.0102 * |Zf|) ^ 2 := by
      rw [← sq_abs E]
      exact pow_le_pow_left₀ hE0 hsum 2
    have h2 : (1.0301 * |Zg| + 1.0102 * |Zf|) ^ 2 ≤ 2.2 * Zg ^ 2 + 2.1 * Zf ^ 2 := by
      have k1 := two_sq (1.0301 * |Zg|) (1.0102 * |Zf|)
      have k2 : (1.0301 * |Zg|) ^ 2 = 1.0301 ^ 2 * Zg ^ 2 := by rw [mul_pow, sq_abs]
      have k3 : (1.0102 * |Zf|) ^ 2 = 1.0102 ^ 2 * Zf ^ 2 := by rw [mul_pow, sq_abs]
      rw [k2, k3] at k1
      norm_num at k1 ⊢
      linarith [sq_nonneg Zg, sq_nonneg Zf]
    linarith
  have hint : Integrable (fun ω => ((1 + ρ * g ω) * (1 + f ω / ρ) - c) ^ 2) P := by
    refine Integrable.mono' hdom ?_ ?_
    · exact ((hXm.sub measurable_const).pow_const 2).aestronglyMeasurable
    · filter_upwards [hpt] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hω
  have hV0 : 0 ≤ τ := le_trans (variance_nonneg _ _) hVf
  calc variance (fun ω => (1 + ρ * g ω) * (1 + f ω / ρ)) P
      ≤ ∫ ω, ((1 + ρ * g ω) * (1 + f ω / ρ) - c) ^ 2 ∂P := h1
    _ ≤ ∫ ω, (2.2 * (g ω - Mg) ^ 2 + 2.1 * (f ω - Mf) ^ 2) ∂P :=
        integral_mono_ae hint hdom hpt
    _ = 2.2 * variance g P + 2.1 * variance f P := by
        rw [integral_add (hGL.integrable_sq.const_mul _) (hFL.integrable_sq.const_mul _),
          integral_const_mul, integral_const_mul, hV1, hV2]
    _ ≤ 5 * τ := by linarith

lemma sq_four {a b c d : ℝ} : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

lemma l2_final {n : ℕ} (ρ MP MQ c : Fin n → ℝ) (ε τ Mb : ℝ)
    (hρ : ∀ i, 0.9999 ≤ ρ i ∧ ρ i ≤ 1.0001)
    (hMP : ∑ i, MP i ^ 2 ≤ Mb ^ 2) (hMQ : ∑ i, MQ i ^ 2 ≤ Mb ^ 2)
    (hc : ∀ i, |c i| ≤ τ) (hnτ : (n:ℝ) * τ ^ 2 ≤ (ε / 1000) ^ 2)
    (hMb : Mb ≤ 1.13 * ε) (hMb0 : 0 ≤ Mb) (hε : 0 < ε) (hε1 : ε ≤ 1 / 40000) :
    ∑ i, ((ρ i - 1) * MQ i + (1 / ρ i - 1) * MP i + (MP i * MQ i + c i)) ^ 2
      ≤ (ε / 200) ^ 2 := by
  have h1 : ∀ i, ((ρ i - 1) * MQ i + (1 / ρ i - 1) * MP i + (MP i * MQ i + c i)) ^ 2 ≤
      4 * (1e-8 * MQ i ^ 2 + 1.21e-8 * MP i ^ 2 + MP i ^ 2 * MQ i ^ 2 + c i ^ 2) := by
    intro i
    obtain ⟨h0, h1⟩ := hρ i
    have hρpos : 0 < ρ i := by linarith
    have ha : ((ρ i - 1) * MQ i) ^ 2 ≤ 1e-8 * MQ i ^ 2 := by
      rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    have hb : ((1 / ρ i - 1) * MP i) ^ 2 ≤ 1.21e-8 * MP i ^ 2 := by
      rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hu : 1 / ρ i ≤ 1.00011 := by rw [div_le_iff₀ hρpos]; nlinarith
      have hl : 0.99989 ≤ 1 / ρ i := by rw [le_div_iff₀ hρpos]; nlinarith
      nlinarith
    have hd : (MP i * MQ i) ^ 2 = MP i ^ 2 * MQ i ^ 2 := mul_pow _ _ _
    have hcc : c i ^ 2 ≤ c i ^ 2 := le_rfl
    have := sq_four (a := (ρ i - 1) * MQ i) (b := (1 / ρ i - 1) * MP i) (c := MP i * MQ i)
      (d := c i)
    have e : (ρ i - 1) * MQ i + (1 / ρ i - 1) * MP i + (MP i * MQ i + c i) =
        (ρ i - 1) * MQ i + (1 / ρ i - 1) * MP i + MP i * MQ i + c i := by ring
    rw [e]
    nlinarith
  calc ∑ i, ((ρ i - 1) * MQ i + (1 / ρ i - 1) * MP i + (MP i * MQ i + c i)) ^ 2
      ≤ ∑ i, 4 * (1e-8 * MQ i ^ 2 + 1.21e-8 * MP i ^ 2 + MP i ^ 2 * MQ i ^ 2 + c i ^ 2) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = 4 * (1e-8 * ∑ i, MQ i ^ 2 + 1.21e-8 * ∑ i, MP i ^ 2 + ∑ i, MP i ^ 2 * MQ i ^ 2 +
          ∑ i, c i ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 4 * (1e-8 * Mb ^ 2 + 1.21e-8 * Mb ^ 2 + Mb ^ 2 * Mb ^ 2 + (ε / 1000) ^ 2) := by
        have hp : ∑ i, MP i ^ 2 * MQ i ^ 2 ≤ Mb ^ 2 * Mb ^ 2 := by
          calc ∑ i, MP i ^ 2 * MQ i ^ 2 ≤ ∑ i, MP i ^ 2 * ∑ j, MQ j ^ 2 := by
                refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
                exact Finset.single_le_sum (f := fun j => MQ j ^ 2) (fun j _ => sq_nonneg _)
                  (Finset.mem_univ i)
            _ = (∑ i, MP i ^ 2) * ∑ j, MQ j ^ 2 := by rw [← Finset.sum_mul]
            _ ≤ Mb ^ 2 * Mb ^ 2 := mul_le_mul hMP hMQ (Finset.sum_nonneg fun j _ => sq_nonneg _)
                (sq_nonneg _)
        have hcs : ∑ i, c i ^ 2 ≤ (ε / 1000) ^ 2 := by
          calc ∑ i, c i ^ 2 ≤ ∑ _i : Fin n, τ ^ 2 :=
                Finset.sum_le_sum fun i _ => by
                  rw [← sq_abs (c i)]; exact pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
            _ = (n:ℝ) * τ ^ 2 := by simp
            _ ≤ _ := hnτ
        nlinarith [hp, hcs, hMP, hMQ]
    _ ≤ (ε / 200) ^ 2 := by
        have hMb2 : Mb ^ 2 ≤ 1.2769 * ε ^ 2 := by nlinarith
        have hε2 : ε ^ 2 ≤ (1 / 40000) ^ 2 := pow_le_pow_left₀ hε.le hε1 2
        have hMb4 : Mb ^ 2 * Mb ^ 2 ≤ 1.64 * ε ^ 2 * (1 / 40000) ^ 2 := by
          have h0 : 0 ≤ Mb ^ 2 := sq_nonneg _
          have h1 := mul_le_mul hMb2 hMb2 h0 (by positivity)
          have h2 := mul_le_mul_of_nonneg_left hε2 (show (0:ℝ) ≤ 1.64 * ε ^ 2 by positivity)
          nlinarith [sq_nonneg ε]
        nlinarith [sq_nonneg ε]

lemma abstract_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (Pf Qf : Fin n → Ω → ℝ) (ρ : Fin n → ℝ) (ε τ Mb : ℝ)
    (hPm : ∀ i, Measurable (Pf i)) (hQm : ∀ i, Measurable (Qf i))
    (hPb : ∀ᵐ ω ∂P, ∀ i, |Pf i ω| ≤ 0.01) (hQb : ∀ᵐ ω ∂P, ∀ i, |Qf i ω| ≤ 0.01)
    (hρ : ∀ i, 0.9999 ≤ ρ i ∧ ρ i ≤ 1.0001)
    (hVP : ∀ i, variance (Pf i) P ≤ τ) (hVQ : ∀ i, variance (Qf i) P ≤ τ)
    (hnτ : (n:ℝ) * τ ^ 2 ≤ (ε / 1000) ^ 2)
    (hMP : ∑ i, (∫ ω, Pf i ω ∂P) ^ 2 ≤ Mb ^ 2) (hMQ : ∑ i, (∫ ω, Qf i ω ∂P) ^ 2 ≤ Mb ^ 2)
    (hMb : Mb ≤ 1.13 * ε) (hMb0 : 0 ≤ Mb) (hε : 0 < ε) (hε1 : ε ≤ 1 / 40000) :
    ∑ i, (∫ ω, ((1 + ρ i * Qf i ω) * (1 + Pf i ω / ρ i) - 1 - Pf i ω - Qf i ω) ∂P) ^ 2
        ≤ (ε / 200) ^ 2 ∧
      ∀ i, variance (fun ω => (1 + ρ i * Qf i ω) * (1 + Pf i ω / ρ i)) P ≤ 5 * τ := by
  have hPb' : ∀ i, ∀ᵐ ω ∂P, |Pf i ω| ≤ 0.01 := fun i => by
    filter_upwards [hPb] with ω h using h i
  have hQb' : ∀ i, ∀ᵐ ω ∂P, |Qf i ω| ≤ 0.01 := fun i => by
    filter_upwards [hQb] with ω h using h i
  refine ⟨?_, fun i => var_bound_X P (Pf i) (Qf i) (ρ i) τ (hρ i).1 (hρ i).2 (hPm i) (hQm i)
    (hPb' i) (hQb' i) (hVP i) (hVQ i)⟩
  have hc : ∀ i, |(∫ ω, Pf i ω * Qf i ω ∂P) - (∫ ω, Pf i ω ∂P) * (∫ ω, Qf i ω ∂P)| ≤ τ := by
    intro i
    have := cov_bound P (Pf i) (Qf i) 0.01 (hPm i) (hQm i) (hPb' i) (hQb' i)
    linarith [hVP i, hVQ i]
  have e : ∀ i, ∫ ω, ((1 + ρ i * Qf i ω) * (1 + Pf i ω / ρ i) - 1 - Pf i ω - Qf i ω) ∂P =
      (ρ i - 1) * (∫ ω, Qf i ω ∂P) + (1 / ρ i - 1) * (∫ ω, Pf i ω ∂P) +
        ((∫ ω, Pf i ω ∂P) * (∫ ω, Qf i ω ∂P) +
          ((∫ ω, Pf i ω * Qf i ω ∂P) - (∫ ω, Pf i ω ∂P) * (∫ ω, Qf i ω ∂P))) := by
    intro i
    have hρne : ρ i ≠ 0 := by have := (hρ i).1; intro h; rw [h] at this; norm_num at this
    rw [mean_decomp P (Pf i) (Qf i) 0.01 (ρ i) hρne (hPm i) (hQm i) (hPb' i) (hQb' i)]
    ring
  simp_rw [e]
  exact l2_final ρ (fun i => ∫ ω, Pf i ω ∂P) (fun i => ∫ ω, Qf i ω ∂P)
    (fun i => (∫ ω, Pf i ω * Qf i ω ∂P) - (∫ ω, Pf i ω ∂P) * (∫ ω, Qf i ω ∂P))
    ε τ Mb hρ hMP hMQ hc hnτ hMb hMb0 hε hε1



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

lemma coord_var_le {n : ℕ} (hn : 0 < n) (k : ℝ) (hk : 0 < k) (a : Fin n → ℝ) (N : ℝ)
    (hN : ∑ l, a l ^ 2 ≤ N) (j : Fin n) :
    a j ^ 2 * (1 - sampleProb k a j) / sampleProb k a j ≤ N / k := by
  have hp := sampleProb_pos hn k hk a j
  have hN0 : 0 ≤ N := le_trans (Finset.sum_nonneg fun l _ => sq_nonneg _) hN
  have hNk : 0 ≤ N / k := div_nonneg hN0 hk.le
  by_cases h1 : sampleProb k a j = 1
  · rw [h1]; simpa using hNk
  · have hlt : sampleProb k a j < 1 := lt_of_le_of_ne hp.2 h1
    have hpeq : sampleProb k a j = k * (a j ^ 2 / ∑ l, a l ^ 2 + 1 / (n:ℝ)) := by
      unfold sampleProb at hlt ⊢
      rcases min_lt_iff.1 hlt with h | h
      · exact absurd h (lt_irrefl 1)
      · exact min_eq_right h.le
    set p := sampleProb k a j with hpdef
    set D := ∑ l, a l ^ 2 with hD
    have hD0 : 0 ≤ D := Finset.sum_nonneg fun l _ => sq_nonneg _
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have key : a j ^ 2 * (1 - p) / p ≤ a j ^ 2 / p :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (a j), hp.1]) hp.1.le
    refine key.trans ?_
    by_cases hD' : D = 0
    · have h0 : a j ^ 2 ≤ D := Finset.single_le_sum (f := fun l => a l ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ j)
      have : a j ^ 2 = 0 := le_antisymm (by rw [hD'] at h0; exact h0) (sq_nonneg _)
      rw [this, zero_div]; exact hNk
    · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hD')
      have hDp : D * p = k * a j ^ 2 + k * D / n := by
        rw [hpeq]; field_simp
      have : a j ^ 2 / p ≤ D / k := by
        rw [div_le_div_iff₀ hp.1 hk]
        have : 0 ≤ k * D / n := by positivity
        nlinarith
      exact this.trans (div_le_div_of_nonneg_right hN hk.le)

lemma sampleLaw_prob {n : ℕ} (hn : 0 < n) (k : ℝ) (hk : 0 < k) (a : Fin n → ℝ) :
    IsProbabilityMeasure (sampleLaw k a) := by
  haveI : ∀ j, IsProbabilityMeasure (coordLaw (sampleProb k a j) (a j)) :=
    fun j => coordLaw_isProb _ _ (sampleProb_pos hn k hk a j).1 (sampleProb_pos hn k hk a j).2
  unfold sampleLaw; infer_instance

lemma integrable_coord_P {n : ℕ} (hn : 0 < n) (k : ℝ) (hk : 0 < k) (a : Fin n → ℝ)
    (S : Set (Fin n → ℝ)) (hQS0 : sampleLaw k a S ≠ 0) (j : Fin n) :
    Integrable (fun δ : Fin n → ℝ => δ j) ((sampleLaw k a)[|S]) := by
  haveI : ∀ j, IsProbabilityMeasure (coordLaw (sampleProb k a j) (a j)) :=
    fun j => coordLaw_isProb _ _ (sampleProb_pos hn k hk a j).1 (sampleProb_pos hn k hk a j).2
  haveI := sampleLaw_prob hn k hk a
  have hae : ∀ᵐ δ ∂(sampleLaw k a), |δ j| ≤ |a j| / sampleProb k a j := by
    unfold sampleLaw
    exact ae_coord_le _ j _ (coordLaw_bad _ _ (sampleProb_pos hn k hk a j).1)
  have hQ : Integrable (fun δ : Fin n → ℝ => δ j) (sampleLaw k a) :=
    Integrable.of_bound (continuous_apply j).aestronglyMeasurable _
      (by filter_upwards [hae] with δ hδ; rwa [Real.norm_eq_abs])
  unfold ProbabilityTheory.cond
  exact (hQ.restrict).smul_measure (ENNReal.inv_ne_top.2 hQS0)

lemma lin_var_P {n : ℕ} (hn : 0 < n) (k : ℝ) (hk : 0 < k) (a : Fin n → ℝ) (N : ℝ)
    (hN : ∑ l, a l ^ 2 ≤ N) (S : Set (Fin n → ℝ)) (c : Fin n → ℝ) (C : ℝ)
    (hC : ∑ j, c j ^ 2 ≤ C) :
    ∫ δ, (∑ j, c j * δ j - ∑ j, c j * a j) ^ 2 ∂((sampleLaw k a)[|S])
      ≤ ((sampleLaw k a).real S)⁻¹ * (N / k * C) := by
  haveI := sampleLaw_prob hn k hk a
  have hp := sampleProb_pos hn k hk a
  have hsm := second_moment_Q (fun j => sampleProb k a j) a (fun j => (hp j).1)
    (fun j => (hp j).2) (N / k) (fun j => coord_var_le hn k hk a N hN j) c
  have hsm' : Integrable (fun δ : Fin n → ℝ => (∑ j, c j * (δ j - a j)) ^ 2) (sampleLaw k a) :=
    hsm.1
  have hle := cond_integral_le (sampleLaw k a) S (fun δ => (∑ j, c j * (δ j - a j)) ^ 2)
    (fun _ => sq_nonneg _) hsm'
  have e : ∀ δ : Fin n → ℝ, ∑ j, c j * δ j - ∑ j, c j * a j = ∑ j, c j * (δ j - a j) := by
    intro δ; simp only [mul_sub, Finset.sum_sub_distrib]
  simp_rw [e]
  have h2 : ∫ δ, (∑ j, c j * (δ j - a j)) ^ 2 ∂(sampleLaw k a) ≤ N / k * C := by
    have := hsm.2
    have hNk : 0 ≤ N / k := div_nonneg (le_trans (Finset.sum_nonneg fun l _ => sq_nonneg _) hN)
      hk.le
    calc _ ≤ N / k * ∑ j, c j ^ 2 := this
      _ ≤ N / k * C := mul_le_mul_of_nonneg_left hC hNk
  exact hle.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 measureReal_nonneg))

lemma lin_variance_P {n : ℕ} (hn : 0 < n) (k : ℝ) (hk : 0 < k) (a : Fin n → ℝ) (N : ℝ)
    (hN : ∑ l, a l ^ 2 ≤ N) (S : Set (Fin n → ℝ)) (hQS0 : sampleLaw k a S ≠ 0)
    (c : Fin n → ℝ) (C : ℝ) (hC : ∑ j, c j ^ 2 ≤ C) :
    variance (fun δ : Fin n → ℝ => ∑ j, c j * δ j) ((sampleLaw k a)[|S])
      ≤ ((sampleLaw k a).real S)⁻¹ * (N / k * C) := by
  haveI := sampleLaw_prob hn k hk a
  haveI : IsProbabilityMeasure ((sampleLaw k a)[|S]) := cond_isProbabilityMeasure hQS0
  have hm : Measurable (fun δ : Fin n → ℝ => ∑ j, c j * δ j) := by fun_prop
  exact (var_le_sq_center _ _ hm.aestronglyMeasurable (∑ j, c j * a j)).trans
    (lin_var_P hn k hk a N hN S c C hC)

lemma QS_ge {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (x s v δμ : Fin n → ℝ) (t k ε εmp : ℝ) (hAs : Assumption41 x s t v δμ k ε εmp) :
    0.998 ≤ (sampleLaw k δμ).real (successEvent A x s v) := by
  have hL : 1 < Real.log n := by
    have h10 : (10:ℝ) ≤ n := by exact_mod_cast hn
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log n := Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  obtain ⟨hprob, h47⟩ := L47_sp_main hn A hA x s v δμ t k ε εmp hAs
  obtain ⟨hx, hs, ht, hap, hεmp, hεmp', hw, hε, hεle, hnorm, hk, hkge⟩ := hAs
  set L := Real.log n with hLdef
  have hL0 : 0 < L := by linarith
  have hk' : 40000000 * ε * Real.sqrt n * L ^ 2 ≤ k := by
    refine le_trans ?_ hkge
    rw [le_div_iff₀ hεmp]
    have : 0 ≤ ε * Real.sqrt n * L ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hεmp' this
    linarith
  set ηs := 2 * n * Real.exp (-(0.003 * k / (ε * Real.sqrt n * Real.log n))) with hηs
  have hηs2 : ηs ≤ 0.002 := by
    have hy : 4 * L ≤ 0.003 * k / (ε * Real.sqrt n * L) := by
      rw [le_div_iff₀ (by positivity)]
      have : 0 ≤ ε * Real.sqrt n * L ^ 2 := by positivity
      nlinarith
    have h1 : Real.exp (-(0.003 * k / (ε * Real.sqrt n * L))) ≤ Real.exp (-(4 * L)) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-(4 * L)) = ((n:ℝ) ^ 4)⁻¹ := by
      rw [Real.exp_neg, show 4 * L = ((4:ℕ):ℝ) * L by norm_num, Real.exp_nat_mul, hLdef,
        Real.exp_log (by linarith)]
    have h3 : 2 * (n:ℝ) * ((n:ℝ) ^ 4)⁻¹ ≤ 0.002 := by
      rw [show 2 * (n:ℝ) * ((n:ℝ) ^ 4)⁻¹ = 2 / (n:ℝ) ^ 3 by field_simp]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10) hn' 3]
    calc ηs = 2 * n * Real.exp (-(0.003 * k / (ε * Real.sqrt n * L))) := rfl
      _ ≤ 2 * n * ((n:ℝ) ^ 4)⁻¹ := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 0.002 := h3
  have hsub : {δ : Fin n → ℝ | ∀ i, |stepS A x s v δ i / sbar x s v i| ≤ 0.01 / Real.log n ∧
        |stepS A x s v δ i / s i| ≤ 0.02 / Real.log n ∧
        |stepX A x s v δ i / xbar x s v i| ≤ 0.01 / Real.log n ∧
        |stepX A x s v δ i / x i| ≤ 0.02 / Real.log n ∧
        |δ i / (x i * s i)| ≤ 0.02 / Real.log n} ⊆ successEvent A x s v := by
    intro δ hδ i
    have e : (0.01:ℝ) / Real.log n = 1 / (100 * Real.log n) := by field_simp; norm_num
    exact ⟨e ▸ (hδ i).1, e ▸ (hδ i).2.2.1⟩
  have h1 : ENNReal.ofReal (1 - ηs) ≤ sampleLaw k δμ (successEvent A x s v) :=
    h47.trans (measure_mono hsub)
  have h2 := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h1
  simp only [Measure.real]
  linarith



lemma muNew_eq {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i)
    (hxb : ∀ i, 0 < xbar x s v i) (hsb : ∀ i, 0 < sbar x s v i)
    (hmu : ∀ i, xbar x s v i * sbar x s v i = x i * s i) (i : Fin n) :
    muNew A x s v δ i / (x i * s i) =
      (1 + xbar x s v i / x i * (stepX A x s v δ i / xbar x s v i)) *
        (1 + (stepS A x s v δ i / sbar x s v i) / (xbar x s v i / x i)) := by
  unfold muNew
  have h1 := hmu i
  have hX := (hxb i).ne'
  have hS := (hsb i).ne'
  have hx0 := (hx i).ne'
  have hs0 := (hs i).ne'
  have e2 : stepS A x s v δ i / sbar x s v i / (xbar x s v i / x i) =
      stepS A x s v δ i / s i := by
    rw [div_div, div_eq_div_iff (mul_ne_zero hS (div_ne_zero hX hx0)) hs0]
    field_simp
    linear_combination (-(stepS A x s v δ i)) * h1
  have e1 : xbar x s v i / x i * (stepX A x s v δ i / xbar x s v i) =
      stepX A x s v δ i / x i := by field_simp
  rw [e1, e2]
  field_simp

lemma delta_over_mu {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ)
    (hxb : ∀ i, 0 < xbar x s v i) (hsb : ∀ i, 0 < sbar x s v i)
    (hmu : ∀ i, xbar x s v i * sbar x s v i = x i * s i) (i : Fin n) :
    δ i / (x i * s i) =
      stepX A x s v δ i / xbar x s v i + stepS A x s v δ i / sbar x s v i := by
  rw [← hmu i]
  exact step_sum A x s v δ hxb hsb i



lemma cont_stepX {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n) :
    Continuous (fun δ => stepX A x s v δ i) := by
  unfold stepX pMu; fun_prop

lemma cont_stepS {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n) :
    Continuous (fun δ => stepS A x s v δ i) := by
  unfold stepS pMu; fun_prop

lemma one_lt_log {n : ℕ} (hn : 10 ≤ n) : 1 < Real.log n := by
  have h10 : (10:ℝ) ≤ n := by exact_mod_cast hn
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log n := Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

lemma l2_add {n : ℕ} (u w : Fin n → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∑ i, u i ^ 2 ≤ A ^ 2) (hw : ∑ i, w i ^ 2 ≤ B ^ 2) :
    ∑ i, (u i + w i) ^ 2 ≤ (A + B) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u w
  have h1 : (∑ i, u i * w i) ^ 2 ≤ (A * B) ^ 2 := by
    calc (∑ i, u i * w i) ^ 2 ≤ (∑ i, u i ^ 2) * ∑ i, w i ^ 2 := hcs
      _ ≤ A ^ 2 * B ^ 2 := mul_le_mul hu hw (Finset.sum_nonneg fun i _ => sq_nonneg _)
          (sq_nonneg _)
      _ = (A * B) ^ 2 := by ring
  have h2 : ∑ i, u i * w i ≤ A * B := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg hA hB]
  have e : ∑ i, (u i + w i) ^ 2 = ∑ i, u i ^ 2 + 2 * ∑ i, u i * w i + ∑ i, w i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  nlinarith

lemma tau_calc (r ε t k : ℝ) (hr : 0.998 ≤ r) (hε : 0 < ε) (ht : 0 < t) (hk : 0 < k) :
    r⁻¹ * (((ε * t) ^ 2) / k * (1 / (0.9 * t)) ^ 2) ≤ 1.24 * ε ^ 2 / k := by
  have hr0 : 0 < r := by linarith
  have e : ((ε * t) ^ 2) / k * (1 / (0.9 * t)) ^ 2 = ε ^ 2 / k / 0.81 := by
    field_simp; ring
  rw [e]
  have h1 : r⁻¹ ≤ 1 / 0.998 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hr
  have h0 : 0 ≤ ε ^ 2 / k / 0.81 := by positivity
  calc r⁻¹ * (ε ^ 2 / k / 0.81) ≤ 1 / 0.998 * (ε ^ 2 / k / 0.81) :=
        mul_le_mul_of_nonneg_right h1 h0
    _ ≤ 1.24 * ε ^ 2 / k := by
        have : 0 ≤ ε ^ 2 / k := by positivity
        have e2 : 1.24 * ε ^ 2 / k = 1.24 * (ε ^ 2 / k) := by ring
        rw [e2]
        calc 1 / 0.998 * (ε ^ 2 / k / 0.81) = (1 / (0.998 * 0.81)) * (ε ^ 2 / k) := by ring
          _ ≤ 1.24 * (ε ^ 2 / k) := mul_le_mul_of_nonneg_right (by norm_num) this



set_option maxHeartbeats 1000000 in
lemma mu_new_moments {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (x s v δμ : Fin n → ℝ) (t k ε εmp : ℝ) (hAs : Assumption41 x s t v δμ k ε εmp)
    (hb : ∑ i, (∫ δ, δ i ∂(stepLaw A x s v k δμ) - δμ i) ^ 2 ≤ (0.01 * ε * t) ^ 2) :
    IsProbabilityMeasure (stepLaw A x s v k δμ) ∧
    norm2 (fun i => ∫ δ, (muNew A x s v δ i - x i * s i - δ i) / (x i * s i)
      ∂(stepLaw A x s v k δμ)) ≤ ε / 200 ∧
    (∀ i, variance (fun δ => muNew A x s v δ i / (x i * s i)) (stepLaw A x s v k δμ)
      ≤ 50 * ε ^ 2 / k) ∧
    (∀ δ ∈ successEvent A x s v, ∀ i,
      |(muNew A x s v δ i - x i * s i) / (x i * s i)| ≤ 0.021 / Real.log n) := by
  have hL := one_lt_log hn
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  obtain ⟨hxb, hsb, hmu⟩ := xbar_sbar x s v δμ t k ε εmp hAs
  have hQS := QS_ge hn A hA x s v δμ t k ε εmp hAs
  obtain ⟨hx, hs, ht, hap, hεmp, hεmp', hw, hε, hεle, hnorm, hk, hkge⟩ := hAs
  set L := Real.log n with hLdef
  have hL0 : 0 < L := by linarith
  have hεL : ε * L ≤ 1 / 40000 := by
    rw [le_div_iff₀ (by positivity)] at hεle; linarith
  have hε1 : ε ≤ 1 / 40000 := by nlinarith
  have hk' : 40000000 * ε * Real.sqrt n * L ^ 2 ≤ k := by
    refine le_trans ?_ hkge
    rw [le_div_iff₀ hεmp]
    have : 0 ≤ ε * Real.sqrt n * L ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hεmp' this
    linarith
  haveI hQprob : IsProbabilityMeasure (sampleLaw k δμ) := sampleLaw_prob hn0 k hk δμ
  set S := successEvent A x s v with hSdef
  have hSm : MeasurableSet S := by
    have e : S = ⋂ j, ({δ | |stepS A x s v δ j / sbar x s v j| ≤ 1 / (100 * Real.log n)} ∩
        {δ | |stepX A x s v δ j / xbar x s v j| ≤ 1 / (100 * Real.log n)}) := by
      ext δ; simp [hSdef, successEvent]
    rw [e]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le ((cont_stepS A x s v j).div_const _).abs.measurable
        measurable_const).inter
      (measurableSet_le ((cont_stepX A x s v j).div_const _).abs.measurable
        measurable_const)
  have hQS0 : sampleLaw k δμ S ≠ 0 := by
    intro h
    have h2 := hQS
    simp only [Measure.real, h, ENNReal.toReal_zero] at h2
    norm_num at h2
  have hPdef : stepLaw A x s v k δμ = (sampleLaw k δμ)[|S] := rfl
  haveI hP : IsProbabilityMeasure (stepLaw A x s v k δμ) := by
    rw [hPdef]; exact cond_isProbabilityMeasure hQS0
  -- the linear forms
  set R : Fin n → ℝ := fun j => Real.sqrt (xbar x s v j * sbar x s v j) with hRdef
  have hRpos : ∀ j, 0 < R j := fun j => Real.sqrt_pos.2 (mul_pos (hxb j) (hsb j))
  have hμ : ∀ i, 0.9 * t ≤ x i * s i ∧ x i * s i ≤ 1.1 * t := by
    intro i
    have h := hap i
    dsimp only at h
    constructor <;> linarith [h.1, h.2]
  have hRlow : ∀ j, 0.9 * t ≤ R j ^ 2 := by
    intro j
    simp only [hRdef]
    rw [Real.sq_sqrt (mul_pos (hxb j) (hsb j)).le, hmu j]
    exact (hμ j).1
  set Pm := projBar A (xbar x s v) (sbar x s v) with hPm
  let cS : Fin n → Fin n → ℝ := fun i j => Pm i j / (R j * R i)
  let cX : Fin n → Fin n → ℝ := fun i j => ((1 : Matrix (Fin n) (Fin n) ℝ) i j - Pm i j) / (R j * R i)
  have hbS : ∀ i, ∑ j, cS i j ^ 2 ≤ (1 / (0.9 * t)) ^ 2 := fun i =>
    coef_bound (fun j => Pm i j) R (R i) t ht hRlow (hRlow i) (proj_rows A _ _ hxb hsb i).1
  have hbX : ∀ i, ∑ j, cX i j ^ 2 ≤ (1 / (0.9 * t)) ^ 2 := fun i =>
    coef_bound (fun j => (1 : Matrix (Fin n) (Fin n) ℝ) i j - Pm i j) R (R i) t ht hRlow (hRlow i)
      (proj_rows A _ _ hxb hsb i).2
  have hoS : ∀ z : Fin n → ℝ, ∑ i, (∑ j, cS i j * z j) ^ 2 ≤ (1 / (0.9 * t)) ^ 2 * ∑ j, z j ^ 2 :=
    fun z => coef_opnorm (fun i j => Pm i j) R t ht hRlow hRpos
      (fun z => (projBar_opnorm A _ _ hxb hsb z).1) z
  have hoX : ∀ z : Fin n → ℝ, ∑ i, (∑ j, cX i j * z j) ^ 2 ≤ (1 / (0.9 * t)) ^ 2 * ∑ j, z j ^ 2 :=
    fun z => coef_opnorm (fun i j => (1 : Matrix (Fin n) (Fin n) ℝ) i j - Pm i j) R t ht hRlow
      hRpos (fun z => (projBar_opnorm A _ _ hxb hsb z).2) z
  obtain ⟨Pf, hPf⟩ : ∃ Pf : Fin n → (Fin n → ℝ) → ℝ, Pf = fun i δ => ∑ j, cS i j * δ j :=
    ⟨_, rfl⟩
  obtain ⟨Qf, hQf⟩ : ∃ Qf : Fin n → (Fin n → ℝ) → ℝ, Qf = fun i δ => ∑ j, cX i j * δ j :=
    ⟨_, rfl⟩
  have hPeq : ∀ i δ, stepS A x s v δ i / sbar x s v i = Pf i δ := fun i δ => by
    rw [hPf]; exact stepS_lin A x s v δ hxb hsb i
  have hQeq : ∀ i δ, stepX A x s v δ i / xbar x s v i = Qf i δ := fun i δ => by
    rw [hQf]; exact stepX_lin A x s v δ hxb hsb i
  have hPmeas : ∀ i, Measurable (Pf i) := fun i => by rw [hPf]; fun_prop
  have hQmeas : ∀ i, Measurable (Qf i) := fun i => by rw [hQf]; fun_prop
  -- the sample is supported on the success event
  have hae : ∀ᵐ δ ∂(stepLaw A x s v k δμ), δ ∈ S := by
    rw [hPdef]; exact ae_cond_mem hSm
  have hτ0 : 1 / (100 * L) ≤ 0.01 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hPb : ∀ᵐ δ ∂(stepLaw A x s v k δμ), ∀ i, |Pf i δ| ≤ 0.01 := by
    filter_upwards [hae] with δ hδ i
    rw [← hPeq]; exact ((hδ i).1).trans hτ0
  have hQb : ∀ᵐ δ ∂(stepLaw A x s v k δμ), ∀ i, |Qf i δ| ≤ 0.01 := by
    filter_upwards [hae] with δ hδ i
    rw [← hQeq]; exact ((hδ i).2).trans hτ0
  -- moments
  have hN : ∑ l, δμ l ^ 2 ≤ (ε * t) ^ 2 := by
    have h := hnorm
    unfold norm2 at h
    rw [Real.sqrt_le_left (by positivity)] at h
    exact h
  set τ : ℝ := 1.24 * ε ^ 2 / k with hτ
  have hτ0' : 0 ≤ τ := by positivity
  have hVP : ∀ i, variance (Pf i) (stepLaw A x s v k δμ) ≤ τ := by
    intro i
    rw [hPf, hPdef]
    exact (lin_variance_P hn0 k hk δμ ((ε * t) ^ 2) hN S hQS0 (cS i) _ (hbS i)).trans
      (tau_calc _ ε t k hQS hε ht hk)
  have hVQ : ∀ i, variance (Qf i) (stepLaw A x s v k δμ) ≤ τ := by
    intro i
    rw [hQf, hPdef]
    exact (lin_variance_P hn0 k hk δμ ((ε * t) ^ 2) hN S hQS0 (cX i) _ (hbX i)).trans
      (tau_calc _ ε t k hQS hε ht hk)
  have hnτ : (n:ℝ) * τ ^ 2 ≤ (ε / 1000) ^ 2 := by
    have h1 : Real.sqrt n * τ ≤ ε / 1000 := by
      rw [hτ, ← mul_div_assoc, div_le_iff₀ hk]
      have hL2 : 1 ≤ L ^ 2 := by nlinarith
      have h2 : 40000000 * ε * Real.sqrt n ≤ k := by
        have : 40000000 * ε * Real.sqrt n * 1 ≤ 40000000 * ε * Real.sqrt n * L ^ 2 :=
          mul_le_mul_of_nonneg_left hL2 (by positivity)
        linarith
      have h3 : 0 ≤ ε * Real.sqrt n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]
    have h4 : (n:ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt hnR.le).symm
    rw [h4, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 2
  -- the mean vectors
  have hint : ∀ j, Integrable (fun δ : Fin n → ℝ => δ j) (stepLaw A x s v k δμ) := fun j => by
    rw [hPdef]; exact integrable_coord_P hn0 k hk δμ S hQS0 j
  have hmean : ∀ (c : Fin n → ℝ), ∫ δ, ∑ j, c j * δ j ∂(stepLaw A x s v k δμ) =
      ∑ j, c j * ∫ δ, δ j ∂(stepLaw A x s v k δμ) := by
    intro c
    rw [integral_finset_sum]
    · exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    · exact fun j _ => (hint j).const_mul _
  have hm2 : ∑ j, (∫ δ, δ j ∂(stepLaw A x s v k δμ)) ^ 2 ≤ (1.01 * ε * t) ^ 2 := by
    have h := l2_add δμ (fun j => ∫ δ, δ j ∂(stepLaw A x s v k δμ) - δμ j) (ε * t) (0.01 * ε * t)
      (by positivity) (by positivity) hN hb
    have e : ∀ j, δμ j + (∫ δ, δ j ∂(stepLaw A x s v k δμ) - δμ j) =
        ∫ δ, δ j ∂(stepLaw A x s v k δμ) := fun j => by ring
    simp only [e] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hMP : ∑ i, (∫ δ, Pf i δ ∂(stepLaw A x s v k δμ)) ^ 2 ≤ (1.13 * ε) ^ 2 := by
    have e : ∀ i, ∫ δ, Pf i δ ∂(stepLaw A x s v k δμ) =
        ∑ j, cS i j * ∫ δ, δ j ∂(stepLaw A x s v k δμ) := fun i => by
      rw [hPf]; exact hmean (cS i)
    simp only [e]
    refine (hoS _).trans ?_
    have h9 : (1 / (0.9 * t)) ^ 2 * (1.01 * ε * t) ^ 2 = (1.01 / 0.9 * ε) ^ 2 := by
      field_simp
    calc (1 / (0.9 * t)) ^ 2 * ∑ j, (∫ δ, δ j ∂(stepLaw A x s v k δμ)) ^ 2
        ≤ (1 / (0.9 * t)) ^ 2 * (1.01 * ε * t) ^ 2 :=
          mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ = (1.01 / 0.9 * ε) ^ 2 := h9
      _ ≤ (1.13 * ε) ^ 2 := pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  have hMQ : ∑ i, (∫ δ, Qf i δ ∂(stepLaw A x s v k δμ)) ^ 2 ≤ (1.13 * ε) ^ 2 := by
    have e : ∀ i, ∫ δ, Qf i δ ∂(stepLaw A x s v k δμ) =
        ∑ j, cX i j * ∫ δ, δ j ∂(stepLaw A x s v k δμ) := fun i => by
      rw [hQf]; exact hmean (cX i)
    simp only [e]
    refine (hoX _).trans ?_
    have h9 : (1 / (0.9 * t)) ^ 2 * (1.01 * ε * t) ^ 2 = (1.01 / 0.9 * ε) ^ 2 := by
      field_simp
    calc (1 / (0.9 * t)) ^ 2 * ∑ j, (∫ δ, δ j ∂(stepLaw A x s v k δμ)) ^ 2
        ≤ (1 / (0.9 * t)) ^ 2 * (1.01 * ε * t) ^ 2 :=
          mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ = (1.01 / 0.9 * ε) ^ 2 := h9
      _ ≤ (1.13 * ε) ^ 2 := pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Fin n → ℝ, ρ = fun i => xbar x s v i / x i := ⟨_, rfl⟩
  have hρ : ∀ i, 0.9999 ≤ ρ i ∧ ρ i ≤ 1.0001 := fun i => by
    rw [hρdef]; exact rho_bounds x s v δμ t k ε εmp ⟨hx, hs, ht, hap, hεmp, hεmp', hw, hε, hεle, hnorm, hk, hkge⟩ i
  obtain ⟨hE, hV⟩ := abstract_moments (stepLaw A x s v k δμ) Pf Qf ρ ε τ (1.13 * ε) hPmeas
    hQmeas hPb hQb hρ hVP hVQ hnτ hMP hMQ le_rfl (by positivity) hε hε1
  -- rewriting the target in terms of P, Q
  have hX : ∀ i δ, muNew A x s v δ i / (x i * s i) =
      (1 + ρ i * Qf i δ) * (1 + Pf i δ / ρ i) := by
    intro i δ
    rw [muNew_eq A x s v δ hx hs hxb hsb hmu i, hρdef, hPeq i δ, hQeq i δ]
  refine ⟨hP, ?_, ?_, ?_⟩
  · have e : ∀ i, ∫ δ, (muNew A x s v δ i - x i * s i - δ i) / (x i * s i)
        ∂(stepLaw A x s v k δμ) =
        ∫ δ, ((1 + ρ i * Qf i δ) * (1 + Pf i δ / ρ i) - 1 - Pf i δ - Qf i δ)
          ∂(stepLaw A x s v k δμ) := by
      intro i
      refine integral_congr_ae (Filter.Eventually.of_forall fun δ => ?_)
      dsimp only
      have hxs : x i * s i ≠ 0 := (mul_pos (hx i) (hs i)).ne'
      have h1 := hX i δ
      have h2 := delta_over_mu A x s v δ hxb hsb hmu i
      rw [hPeq i δ, hQeq i δ] at h2
      have e1 : (muNew A x s v δ i - x i * s i - δ i) / (x i * s i) =
          muNew A x s v δ i / (x i * s i) - 1 - δ i / (x i * s i) := by
        rw [sub_div, sub_div, div_self hxs]
      rw [e1, h1, h2]; ring
    unfold norm2
    simp only [e]
    calc Real.sqrt (∑ i, (∫ δ, ((1 + ρ i * Qf i δ) * (1 + Pf i δ / ρ i) - 1 - Pf i δ - Qf i δ)
          ∂(stepLaw A x s v k δμ)) ^ 2) ≤ Real.sqrt ((ε / 200) ^ 2) := Real.sqrt_le_sqrt hE
      _ = ε / 200 := Real.sqrt_sq (by positivity)
  · intro i
    have e : (fun δ => muNew A x s v δ i / (x i * s i)) =
        fun δ => (1 + ρ i * Qf i δ) * (1 + Pf i δ / ρ i) := funext (hX i)
    rw [e]
    refine (hV i).trans ?_
    rw [hτ]
    have : 0 ≤ ε ^ 2 / k := by positivity
    have e2 : 5 * (1.24 * ε ^ 2 / k) = 6.2 * (ε ^ 2 / k) := by ring
    have e3 : 50 * ε ^ 2 / k = 50 * (ε ^ 2 / k) := by ring
    rw [e2, e3]; nlinarith
  · intro δ hδ i
    have hP1 := (hδ i).1
    have hQ1 := (hδ i).2
    rw [hPeq i δ] at hP1
    rw [hQeq i δ] at hQ1
    have hxs : x i * s i ≠ 0 := (mul_pos (hx i) (hs i)).ne'
    obtain ⟨hρ0, hρ1⟩ := hρ i
    have hρpos : 0 < ρ i := by linarith
    have e : (muNew A x s v δ i - x i * s i) / (x i * s i) =
        ρ i * Qf i δ + Pf i δ / ρ i + Pf i δ * Qf i δ := by
      have h1 := hX i δ
      have h2 : (muNew A x s v δ i - x i * s i) / (x i * s i) =
          muNew A x s v δ i / (x i * s i) - 1 := by rw [sub_div, div_self hxs]
      rw [h2, h1]; field_simp; ring
    rw [e]
    have hu0 : 0 < 1 / (100 * L) := by positivity
    have hinv : 1 / ρ i ≤ 1.00011 := by rw [div_le_iff₀ hρpos]; nlinarith
    have hP2 : |Pf i δ / ρ i| ≤ 1.00011 * (1 / (100 * L)) := by
      rw [abs_div, abs_of_pos hρpos, div_eq_mul_one_div]
      have := mul_le_mul hP1 hinv (by positivity) hu0.le
      linarith
    have hQ2 : |ρ i * Qf i δ| ≤ 1.0001 * (1 / (100 * L)) := by
      rw [abs_mul, abs_of_pos hρpos]
      exact mul_le_mul hρ1 hQ1 (abs_nonneg _) (by norm_num)
    have hPQ : |Pf i δ * Qf i δ| ≤ 0.01 * (1 / (100 * L)) := by
      rw [abs_mul]
      exact mul_le_mul (hP1.trans hτ0) hQ1 (abs_nonneg _) (by norm_num)
    have h3 := abs_add_three (ρ i * Qf i δ) (Pf i δ / ρ i) (Pf i δ * Qf i δ)
    have h4 : 0.021 / L = 2.1 * (1 / (100 * L)) := by
      rw [mul_one_div, div_eq_div_iff hL0.ne' (by positivity)]
      ring
    rw [h4]
    linarith


end CohenLeeSongLP.StochCentralPath.L48

open CohenLeeSongLP.StochCentralPath MeasureTheory ProbabilityTheory in
theorem solution {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : A.rank = d) (x s v : Fin n → ℝ) (t kSamp ε εmp : ℝ)
    (hAs : Assumption41 x s t v
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s) kSamp ε εmp) :
    IsProbabilityMeasure (stepLaw A x s v kSamp
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s)) ∧
    ∫ δ, potential (lam n)
        (fun i => muNew A x s v δ i / ((1 - ε / (3 * Real.sqrt n)) * t) - 1)
        ∂(stepLaw A x s v kSamp (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s))
      ≤ potential (lam n) (fun i => x i * s i / t - 1) -
        lam n * ε / (15 * Real.sqrt n) *
          (potential (lam n) (fun i => x i * s i / t - 1) - 10 * n) := by
  obtain ⟨hxb, hsb, hmu⟩ := L413.xbar_sbar x s v _ t kSamp ε εmp hAs
  have hAs' := hAs
  obtain ⟨hx, hs, ht, hap, hεmp, hεmp', hw, hε, hεle, hnorm, hk, hkge⟩ := hAs'
  have hL := L413.one_lt_log hn
  have hε1 : ε ≤ 1 / 40000 := by
    have hεL : ε * Real.log n ≤ 1 / 40000 := by
      rw [le_div_iff₀ (by positivity)] at hεle; linarith
    nlinarith
  have hδsq := L413.direction_sq_le hn x s t ε ht hε hε1 hap
  have hb := L413.bias_bound hn A hA x s v _ t kSamp ε εmp hAs hδsq
  obtain ⟨hP, he, hvar, hsup⟩ := L48.mu_new_moments hn A hA x s v _ t kSamp ε εmp hAs hb
  refine ⟨hP, ?_⟩
  have hSm : MeasurableSet (successEvent A x s v) := by
    have e : successEvent A x s v = ⋂ j, ({δ | |stepS A x s v δ j / sbar x s v j| ≤
        1 / (100 * Real.log n)} ∩ {δ | |stepX A x s v δ j / xbar x s v j| ≤
        1 / (100 * Real.log n)}) := by
      ext δ; simp [successEvent]
    rw [e]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le ((L413.cont_stepS A x s v j).div_const _).abs.measurable
        measurable_const).inter
      (measurableSet_le ((L413.cont_stepX A x s v j).div_const _).abs.measurable
        measurable_const)
  have hδbd : ∀ᵐ δ ∂(stepLaw A x s v kSamp
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s)),
      ∀ i, |δ i| ≤ ∑ j, 2 * (xbar x s v j * sbar x s v j) := by
    filter_upwards [ae_cond_mem hSm] with δ hδ i
    exact (L413.delta_le_on_success hn A x s v hxb hsb δ hδ i).trans
      (Finset.single_le_sum (f := fun j => 2 * (xbar x s v j * sbar x s v j))
        (fun j _ => by have := mul_pos (hxb j) (hsb j); positivity) (Finset.mem_univ i))
  have hsup' : ∀ᵐ δ ∂(stepLaw A x s v kSamp
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s)),
      ∀ i, |(muNew A x s v δ i - x i * s i) / (x i * s i)| ≤ 0.021 / Real.log n := by
    filter_upwards [ae_cond_mem hSm] with δ hδ
    exact hsup δ hδ
  have hMn : ∀ i, Continuous fun δ => muNew A x s v δ i := fun i => by
    unfold muNew stepX stepS pMu; fun_prop
  have hμ : ∀ i, 0.9 * t ≤ (fun i => x i * s i) i ∧ (fun i => x i * s i) i ≤ 1.1 * t := by
    intro i
    have h := hap i
    dsimp only at h ⊢
    constructor <;> linarith [h.1, h.2]
  exact L413.core hn _ (muNew A x s v) hMn (fun i => x i * s i) _ t ε εmp kSamp ht hε hεle
    hεmp hεmp' hkge hμ (fun i => rfl) hsup' _ hδbd he hvar hb
