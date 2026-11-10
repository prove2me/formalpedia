-- Prove2me | solution 1 for FloatPointSynth.Gearbox.theorem_2_mean_variance_applications
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T17:13:04.729774+00:00
-- url     : https://prove2.me/submissions/1891a807-5eba-4d93-8260-442a401ef5bf

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Cost

set_option autoImplicit false

namespace FloatPointSynth.Gearbox.Aux278

open Matrix Complex
open scoped ENNReal NNReal

/-! ## Part 1: the one-ancilla success block -/

lemma sum_fin1 (f : (Fin 1 → Fin 2) → ℂ) :
    ∑ a, f a = f (fun _ => 0) + f (fun _ => 1) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp, Fin.sum_univ_two]
  rfl

lemma fin1_ne : (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ => 1) := by
  intro h; have := congrFun h 0; simp at this

lemma fin1_zero : (0 : Fin 1 → Fin 2) = (fun _ => 0) := rfl

lemma succBlock_apply (V : Matrix (Fin 2) (Fin 2) ℂ) (s t : Fin 2) :
    succBlock V s t =
      (starRingEnd ℂ (V 0 0) * V 0 0) * (if s = t then 1 else 0) +
      (starRingEnd ℂ (V 1 0) * V 1 0) * ((-I) • pauliX) s t := by
  simp only [succBlock, gearbox, Matrix.mul_apply, Fintype.sum_prod_type, sum_fin1,
    Fin.sum_univ_two, onAnc, ctrlNegIX, ancTensor, Matrix.conjTranspose_apply, fin1_zero]
  fin_cases s <;> fin_cases t <;>
    simp [fin1_ne, fin1_ne.symm, pauliX] <;> ring

/-! ## Part 2: moments of PMFs on ℕ -/

lemma tsum_bind_mul (μ : PMF ℕ) (f : ℕ → PMF ℕ) (h : ℕ → ℝ≥0∞) :
    ∑' n, (μ.bind f) n * h n = ∑' a, μ a * ∑' n, f a n * h n := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

lemma tsum_map_mul (μ : PMF ℕ) (g : ℕ → ℕ) (h : ℕ → ℝ≥0∞) :
    ∑' n, (μ.map g) n * h n = ∑' a, μ a * h (g a) := by
  rw [← PMF.bind_pure_comp, tsum_bind_mul]
  congr 1; ext a; congr 1
  simp [PMF.pure_apply]

lemma tsum_pmf (μ : PMF ℕ) : ∑' n, μ n = 1 := μ.tsum_coe


/-! ## Part 1b: column recursion of the composed circuit -/

lemma nb0 (V : Matrix (Fin 2) (Fin 2) ℂ) : ‖succBlock V 0 0‖ = ‖V 0 0‖ ^ 2 := by
  rw [succBlock_apply]
  first | (simp [pauliX, sq]; done) | (simp [pauliX]; ring)

lemma nb1 (V : Matrix (Fin 2) (Fin 2) ℂ) : ‖succBlock V 1 0‖ = ‖V 1 0‖ ^ 2 := by
  rw [succBlock_apply]
  first | (simp [pauliX, sq]; done) | (simp [pauliX]; ring)

noncomputable def cc (U : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) : ℝ := ‖composed U q 0 0‖ ^ 2
noncomputable def ss (U : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) : ℝ := ‖composed U q 1 0‖ ^ 2

lemma sumBlock (U : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) :
    ∑ s, ‖succBlock (composed U q) s 0‖ ^ 2 = cc U q ^ 2 + ss U q ^ 2 := by
  rw [Fin.sum_univ_two, nb0, nb1]; rfl

lemma levelProb_succ (U : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) :
    levelProb U (q + 1) = cc U q ^ 2 + ss U q ^ 2 := by
  rw [levelProb, Nat.add_sub_cancel, sumBlock]

lemma norm_composed_succ (U : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (i : Fin 2) :
    ‖composed U (q + 1) i 0‖ =
      (Real.sqrt (cc U q ^ 2 + ss U q ^ 2))⁻¹ * ‖succBlock (composed U q) i 0‖ := by
  show ‖succUnitary (composed U q) i 0‖ = _
  rw [succUnitary, Matrix.smul_apply, smul_eq_mul, norm_mul, sumBlock]
  congr 1
  simp [abs_of_nonneg (Real.sqrt_nonneg _)]

lemma cs_succ (U : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) :
    cc U (q + 1) = cc U q ^ 2 / (cc U q ^ 2 + ss U q ^ 2) ∧
    ss U (q + 1) = ss U q ^ 2 / (cc U q ^ 2 + ss U q ^ 2) := by
  have hX : 0 ≤ cc U q ^ 2 + ss U q ^ 2 := by positivity
  constructor
  · rw [cc, norm_composed_succ, nb0, mul_pow, inv_pow, Real.sq_sqrt hX]
    simp only [cc]; ring
  · rw [ss, norm_composed_succ, nb1, mul_pow, inv_pow, Real.sq_sqrt hX]
    simp only [ss]; ring

lemma col0 (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    cc U 0 + ss U 0 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h2 : ((cc U 0 + ss U 0 : ℝ) : ℂ) = 1 := by
    rw [← h]; simp only [cc, ss, composed]; push_cast
    first
      | (simp only [Complex.star_def, Complex.conj_mul']; done)
      | (simp [Complex.conj_mul']; done)
      | (simp [Complex.mul_conj, Complex.normSq_eq_norm_sq])
  exact_mod_cast h2

lemma cs_sum (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (q : ℕ) :
    cc U q + ss U q = 1 := by
  induction q with
  | zero => exact col0 U hU
  | succ q ih =>
    obtain ⟨h1, h2⟩ := cs_succ U q
    have hpos : 0 < cc U q ^ 2 + ss U q ^ 2 := by nlinarith [sq_nonneg (cc U q - ss U q)]
    rw [h1, h2, ← add_div, div_self hpos.ne']

/-! ## Part 2b: level probabilities equal P -/

noncomputable def yy (θ0 : ℝ) (q : ℕ) : ℝ := (Real.tan θ0 ^ (2 ^ q)) ^ 2

lemma yy_nonneg (θ0 : ℝ) (q : ℕ) : 0 ≤ yy θ0 q := by unfold yy; positivity

lemma yy_succ (θ0 : ℝ) (q : ℕ) : yy θ0 (q + 1) = yy θ0 q ^ 2 := by
  unfold yy; rw [show 2 ^ (q + 1) = 2 ^ q * 2 from pow_succ 2 q, pow_mul]

lemma P_form (x : ℝ) :
    Real.sin (Real.arctan x) ^ 4 + Real.cos (Real.arctan x) ^ 4 = (1 + (x ^ 2) ^ 2) / (1 + x ^ 2) ^ 2 := by
  have hx : 0 < 1 + x ^ 2 := by positivity
  have e1 : Real.sin (Real.arctan x) ^ 2 = x ^ 2 / (1 + x ^ 2) := by
    rw [Real.sin_arctan, div_pow, Real.sq_sqrt hx.le]
  have e2 : Real.cos (Real.arctan x) ^ 2 = 1 / (1 + x ^ 2) := by
    rw [Real.cos_arctan, div_pow, Real.sq_sqrt hx.le, one_pow]
  rw [show Real.sin (Real.arctan x) ^ 4 = (Real.sin (Real.arctan x) ^ 2) ^ 2 by ring,
    show Real.cos (Real.arctan x) ^ 4 = (Real.cos (Real.arctan x) ^ 2) ^ 2 by ring, e1, e2,
    div_pow, div_pow, ← add_div]
  ring

lemma P_succ (θ0 : ℝ) (q : ℕ) : P θ0 (q + 1) = (1 + yy θ0 q ^ 2) / (1 + yy θ0 q) ^ 2 := by
  unfold P phi
  rw [Nat.add_sub_cancel, P_form]
  rfl

lemma P_succ_le (θ0 : ℝ) (q : ℕ) : P θ0 (q + 1) ≤ 1 ∧ 1 / 2 ≤ P θ0 (q + 1) := by
  rw [P_succ]
  have hy := yy_nonneg θ0 q
  have hpos : (0:ℝ) < (1 + yy θ0 q) ^ 2 := pow_pos (by linarith) 2
  constructor
  · rw [div_le_one hpos]; nlinarith
  · rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg (yy θ0 q - 1)]

lemma alg2 (y : ℝ) (hy : 0 ≤ y) :
    (1 - y / (1 + y)) ^ 2 + (y / (1 + y)) ^ 2 = (1 + y ^ 2) / (1 + y) ^ 2 := by
  have h1 : (1:ℝ) + y ≠ 0 := (by linarith : (0:ℝ) < 1 + y).ne'
  rw [one_sub_div h1, div_pow, div_pow, ← add_div]
  congr 1; ring

lemma alg1 (y : ℝ) (hy : 0 ≤ y) :
    (y / (1 + y)) ^ 2 / ((1 - y / (1 + y)) ^ 2 + (y / (1 + y)) ^ 2) = y ^ 2 / (1 + y ^ 2) := by
  rw [alg2 y hy]
  have h1 : (1:ℝ) + y ≠ 0 := (by linarith : (0:ℝ) < 1 + y).ne'
  have h2 : (1:ℝ) + y ^ 2 ≠ 0 := (by positivity : (0:ℝ) < 1 + y ^ 2).ne'
  first
    | (rw [div_pow, div_div_div_cancel_right₀ (pow_ne_zero 2 h1)]; done)
    | (field_simp; done)
    | (field_simp; ring)

lemma ss_formula (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (hlt : θ0 < Real.pi / 2) (hθ : Real.sin θ0 ^ 2 = ‖U 1 0‖ ^ 2)
    (q : ℕ) : ss U q = yy θ0 q / (1 + yy θ0 q) := by
  induction q with
  | zero =>
    have hc : 0 < Real.cos θ0 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
    have hc2 : Real.cos θ0 ^ 2 = 1 - Real.sin θ0 ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ0]
    have hne : (1 - Real.sin θ0 ^ 2) ≠ 0 := by rw [← hc2]; exact (pow_pos hc 2).ne'
    have hs : ss U 0 = Real.sin θ0 ^ 2 := by rw [hθ]; rfl
    rw [hs]; unfold yy
    rw [pow_zero, pow_one, Real.tan_eq_sin_div_cos, div_pow, hc2]
    first | (field_simp; done) | (field_simp; ring)
  | succ q ih =>
    have hy := yy_nonneg θ0 q
    rw [(cs_succ U q).2, yy_succ, show cc U q = 1 - ss U q by linarith [cs_sum U hU q], ih,
      alg1 _ hy]

lemma ss_one (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (θ0 : ℝ) (heq : θ0 = Real.pi / 2) (hθ : Real.sin θ0 ^ 2 = ‖U 1 0‖ ^ 2) (q : ℕ) :
    ss U q = 1 := by
  induction q with
  | zero =>
    show ‖U 1 0‖ ^ 2 = 1
    rw [← hθ, heq, Real.sin_pi_div_two, one_pow]
  | succ q ih =>
    have hc : cc U q = 0 := by linarith [cs_sum U hU q]
    rw [(cs_succ U q).2, hc, ih]; norm_num

lemma yy_zero (θ0 : ℝ) (heq : θ0 = Real.pi / 2) (q : ℕ) : yy θ0 q = 0 := by
  unfold yy; rw [heq, Real.tan_eq_sin_div_cos, Real.cos_pi_div_two, div_zero]; simp

lemma levelProb_eq (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (hθ1 : θ0 ≤ Real.pi / 2) (hθ : Real.sin θ0 ^ 2 = ‖U 1 0‖ ^ 2)
    (q : ℕ) : levelProb U (q + 1) = P θ0 (q + 1) := by
  rw [levelProb_succ, P_succ, show cc U q = 1 - ss U q by linarith [cs_sum U hU q]]
  rcases lt_or_eq_of_le hθ1 with hlt | heq
  · rw [ss_formula U hU θ0 hθ0 hlt hθ q]; exact alg2 _ (yy_nonneg θ0 q)
  · rw [ss_one U hU θ0 heq hθ q, yy_zero θ0 heq q]; norm_num

lemma P_mono (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (h4 : θ0 < Real.pi / 4) (q : ℕ) (hq : 1 ≤ q) :
    P θ0 1 ≤ P θ0 q := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have hc : 0 < Real.cos θ0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcos2 : 0 ≤ Real.cos (2 * θ0) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith)
  have ht1 : Real.tan θ0 ^ 2 ≤ 1 := by
    rw [Real.tan_eq_sin_div_cos, div_pow, div_le_one (pow_pos hc 2)]
    nlinarith [Real.cos_two_mul θ0, Real.sin_sq_add_cos_sq θ0]
  have ht0 : 0 ≤ Real.tan θ0 ^ 2 := sq_nonneg _
  have yform : ∀ k, yy θ0 k = (Real.tan θ0 ^ 2) ^ (2 ^ k) := fun k => by
    unfold yy; rw [← pow_mul, ← pow_mul, mul_comm]
  have hyk : yy θ0 k ≤ yy θ0 0 := by
    rw [yform, yform, pow_zero, pow_one]
    exact pow_le_of_le_one ht0 ht1 (pow_ne_zero _ two_ne_zero)
  have hy0 : yy θ0 0 ≤ 1 := by rw [yform, pow_zero, pow_one]; exact ht1
  have hyk0 := yy_nonneg θ0 k
  have hy00 := yy_nonneg θ0 0
  have e1 : P θ0 1 = (1 + yy θ0 0 ^ 2) / (1 + yy θ0 0) ^ 2 := P_succ θ0 0
  have hprod : yy θ0 0 * yy θ0 k ≤ 1 := by nlinarith
  rw [e1, P_succ, div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos (by linarith) 2)]
  nlinarith [mul_nonneg (sub_nonneg.2 hyk) (sub_nonneg.2 hprod)]

/-! ## Part 3: moments -/

noncomputable def M1 (μ : PMF ℕ) : ℝ≥0∞ := ∑' n, μ n * (n : ℝ≥0∞)
noncomputable def M2 (μ : PMF ℕ) : ℝ≥0∞ := ∑' n, μ n * (n : ℝ≥0∞) ^ 2

lemma tsum_pure_mul (a : ℕ) (h : ℕ → ℝ≥0∞) : ∑' n, (PMF.pure a) n * h n = h a := by
  rw [tsum_eq_single a (fun b hb => by simp [PMF.pure_apply, hb])]
  simp [PMF.pure_apply]

lemma tsum_lin (μ : PMF ℕ) (c : ℝ≥0∞) : ∑' a, μ a * ((a : ℝ≥0∞) + c) = M1 μ + c := by
  unfold M1
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

lemma tsum_shift (ν : PMF ℕ) (x : ℝ≥0∞) : ∑' b, ν b * (x + (b : ℝ≥0∞)) = x + M1 ν := by
  unfold M1
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]

lemma tsum_sq_shift (ν : PMF ℕ) (x : ℝ≥0∞) :
    ∑' b, ν b * (x + (b : ℝ≥0∞)) ^ 2 = x ^ 2 + 2 * x * M1 ν + M2 ν := by
  unfold M1 M2
  have e : ∀ b : ℕ, ν b * (x + (b : ℝ≥0∞)) ^ 2 =
      ν b * x ^ 2 + (ν b * b) * (2 * x) + ν b * (b : ℝ≥0∞) ^ 2 := fun b => by ring
  simp_rw [e]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
    ν.tsum_coe, one_mul]
  ring

lemma tsum_poly (μ : PMF ℕ) (c1 c2 : ℝ≥0∞) :
    ∑' a, μ a * ((a : ℝ≥0∞) ^ 2 + 2 * a * c1 + c2) = M2 μ + 2 * c1 * M1 μ + c2 := by
  unfold M1 M2
  have e : ∀ a : ℕ, μ a * ((a : ℝ≥0∞) ^ 2 + 2 * a * c1 + c2) =
      μ a * (a : ℝ≥0∞) ^ 2 + (μ a * a) * (2 * c1) + μ a * c2 := fun a => by ring
  simp_rw [e]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
    μ.tsum_coe, one_mul]
  ring

lemma iid_moments (μ : PMF ℕ) (m v : ℝ≥0) (h1 : M1 μ = m)
    (h2 : M2 μ = (v : ℝ≥0∞) + (m : ℝ≥0∞) ^ 2) (k : ℕ) :
    M1 (iidSum μ k) = (k : ℝ≥0∞) * m ∧
      M2 (iidSum μ k) = (k : ℝ≥0∞) * v + ((k : ℝ≥0∞) * m) ^ 2 := by
  induction k with
  | zero =>
    simp only [iidSum, M1, M2, tsum_pure_mul]; simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · have e : M1 (iidSum μ (k + 1)) = ∑' a, μ a * ∑' b, (iidSum μ k) b * ((a : ℝ≥0∞) + b) := by
        simp only [M1, iidSum, tsum_bind_mul, tsum_map_mul, Nat.cast_add]
      rw [e]; simp_rw [tsum_shift]; rw [tsum_lin, ih1, h1]
      first | (push_cast; ring) | push_cast
    · have e : M2 (iidSum μ (k + 1)) =
          ∑' a, μ a * ∑' b, (iidSum μ k) b * ((a : ℝ≥0∞) + b) ^ 2 := by
        simp only [M2, iidSum, tsum_bind_mul, tsum_map_mul, Nat.cast_add]
      rw [e]; simp_rw [tsum_sq_shift]; rw [tsum_poly, ih1, ih2, h1, h2]
      first | (push_cast; ring) | push_cast

lemma geom_moments (p : ℝ≥0) (hp : 0 < p) (hp1 : p ≤ 1) :
    M1 (geomPos (p : ℝ)) = ((p⁻¹ : ℝ≥0) : ℝ≥0∞) ∧
    M2 (geomPos (p : ℝ)) = (((1 - p) / p ^ 2 + p⁻¹ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hp1' : (p:ℝ) ≤ 1 := by exact_mod_cast hp1
  have hr : ‖(1:ℝ) - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have hnn : ∀ a : ℕ, 0 ≤ (1 - (p:ℝ)) ^ a * p := fun a =>
    mul_nonneg (pow_nonneg (by linarith) _) hp'.le
  have hq : (⟨(p:ℝ), hp'.le, hp1'⟩ : unitInterval) ≠ 0 := by
    intro h0
    have := congrArg Subtype.val h0
    first | exact hp'.ne' this | exact hp'.ne' (by simpa using this)
  have hterm : ∀ h : ℕ → ℝ, ∑' n, geomPos (p:ℝ) n * ENNReal.ofReal (h n) =
      ∑' a, ENNReal.ofReal ((1 - (p:ℝ)) ^ a * p * h (a + 1)) := by
    intro h
    unfold geomPos
    rw [dif_pos ⟨hp', hp1'⟩, tsum_map_mul]
    congr 1; ext a
    rw [MeasureTheory.Measure.toPMF_apply, ProbabilityTheory.geometricMeasure_singleton hq]
    exact (ENNReal.ofReal_mul (hnn a)).symm
  have H1 : HasSum (fun a : ℕ => (1 - (p:ℝ)) ^ a * p * ((a + 1 : ℕ) : ℝ)) ((p⁻¹ : ℝ≥0) : ℝ) := by
    have := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hr).mul_left (p:ℝ)
    have hf : (fun a : ℕ => (1 - (p:ℝ)) ^ a * p * ((a + 1 : ℕ) : ℝ)) =
        fun i : ℕ => (p:ℝ) * (((i + 1).choose 1 : ℕ) * (1 - (p:ℝ)) ^ i) := by
      funext a; simp only [Nat.choose_one_right]; push_cast; ring
    have hv : (((p⁻¹ : ℝ≥0)) : ℝ) = (p:ℝ) * (1 / (1 - (1 - (p:ℝ))) ^ (1 + 1)) := by
      rw [sub_sub_cancel]; push_cast
      first | (field_simp; done) | (field_simp; ring)
    rw [hf, hv]; exact this
  have H2 : HasSum (fun a : ℕ => (1 - (p:ℝ)) ^ a * p * ((a + 1 : ℕ) : ℝ) ^ 2)
      ((((1 - p) / p ^ 2 + p⁻¹ ^ 2 : ℝ≥0)) : ℝ) := by
    have h2 := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).mul_left (2 * (p:ℝ))
    have h1 := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hr).mul_left (p:ℝ)
    have hf : (fun a : ℕ => (1 - (p:ℝ)) ^ a * p * ((a + 1 : ℕ) : ℝ) ^ 2) =
        fun b : ℕ => 2 * (p:ℝ) * (((b + 2).choose 2 : ℕ) * (1 - (p:ℝ)) ^ b) -
          (p:ℝ) * (((b + 1).choose 1 : ℕ) * (1 - (p:ℝ)) ^ b) := by
      funext a; simp only [Nat.choose_one_right, Nat.cast_choose_two]; push_cast; ring
    have hv : ((((1 - p) / p ^ 2 + p⁻¹ ^ 2 : ℝ≥0)) : ℝ) =
        2 * (p:ℝ) * (1 / (1 - (1 - (p:ℝ))) ^ (2 + 1)) - (p:ℝ) * (1 / (1 - (1 - (p:ℝ))) ^ (1 + 1)) := by
      rw [sub_sub_cancel, NNReal.coe_add, NNReal.coe_div, NNReal.coe_sub hp1]; push_cast
      first | (field_simp; done) | (field_simp; ring)
    rw [hf, hv]; exact h2.sub h1
  constructor
  · have h1 := hterm (fun n => (n:ℝ))
    simp only [ENNReal.ofReal_natCast] at h1
    unfold M1
    rw [h1, ← ENNReal.ofReal_tsum_of_nonneg (fun a => mul_nonneg (hnn a) (Nat.cast_nonneg _))
      H1.summable, H1.tsum_eq, ENNReal.ofReal_coe_nnreal]
  · have e2 : ∀ n : ℕ, ENNReal.ofReal ((n:ℝ) ^ 2) = (n:ℝ≥0∞) ^ 2 := fun n => by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have h2 := hterm (fun n => (n:ℝ) ^ 2)
    simp only [e2] at h2
    unfold M2
    rw [h2, ← ENNReal.ofReal_tsum_of_nonneg (fun a => mul_nonneg (hnn a) (sq_nonneg _))
      H2.summable, H2.tsum_eq, ENNReal.ofReal_coe_nnreal]

lemma geom_bind (p : ℝ≥0) (hp : 0 < p) (hp1 : p ≤ 1) (ρ : PMF ℕ) (m v : ℝ≥0)
    (h1 : M1 ρ = m) (h2 : M2 ρ = (v : ℝ≥0∞) + (m : ℝ≥0∞) ^ 2) :
    M1 ((geomPos (p:ℝ)).bind fun N => iidSum ρ (2 * N)) = ((p⁻¹ * (2 * m) : ℝ≥0) : ℝ≥0∞) ∧
    M2 ((geomPos (p:ℝ)).bind fun N => iidSum ρ (2 * N)) =
      (((p⁻¹ * (2 * v) + (1 - p) / p ^ 2 * (4 * m ^ 2)) : ℝ≥0) : ℝ≥0∞) +
        ((p⁻¹ * (2 * m) : ℝ≥0) : ℝ≥0∞) ^ 2 := by
  obtain ⟨g1, g2⟩ := geom_moments p hp hp1
  have hi := iid_moments ρ m v h1 h2
  constructor
  · have e : M1 ((geomPos (p:ℝ)).bind fun N => iidSum ρ (2 * N)) =
        ∑' N, geomPos (p:ℝ) N * M1 (iidSum ρ (2 * N)) := by
      simp only [M1, tsum_bind_mul]
    have hi1 : ∀ N : ℕ, M1 (iidSum ρ (2 * N)) = ((2 * N : ℕ) : ℝ≥0∞) * m := fun N => (hi (2 * N)).1
    have e2 : ∀ N : ℕ, geomPos (p:ℝ) N * (((2 * N : ℕ) : ℝ≥0∞) * m) =
        (geomPos (p:ℝ) N * N) * (2 * m) := fun N => by push_cast; ring
    rw [e]; simp_rw [hi1, e2]
    rw [ENNReal.tsum_mul_right]
    change M1 (geomPos (p:ℝ)) * _ = _
    rw [g1]
    first | (push_cast; ring) | push_cast
  · have e : M2 ((geomPos (p:ℝ)).bind fun N => iidSum ρ (2 * N)) =
        ∑' N, geomPos (p:ℝ) N * M2 (iidSum ρ (2 * N)) := by
      simp only [M2, tsum_bind_mul]
    have hi2 : ∀ N : ℕ, M2 (iidSum ρ (2 * N)) =
        ((2 * N : ℕ) : ℝ≥0∞) * v + (((2 * N : ℕ) : ℝ≥0∞) * m) ^ 2 := fun N => (hi (2 * N)).2
    have e2 : ∀ N : ℕ, geomPos (p:ℝ) N * (((2 * N : ℕ) : ℝ≥0∞) * v + (((2 * N : ℕ) : ℝ≥0∞) * m) ^ 2) =
        (geomPos (p:ℝ) N * N) * (2 * v) + (geomPos (p:ℝ) N * (N : ℝ≥0∞) ^ 2) * (4 * (m : ℝ≥0∞) ^ 2) :=
      fun N => by push_cast; ring
    rw [e]; simp_rw [hi2, e2]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    change M1 (geomPos (p:ℝ)) * _ + M2 (geomPos (p:ℝ)) * _ = _
    rw [g1, g2]
    first | (push_cast; ring) | push_cast

lemma nLaw_mom (x : PMF ℕ) (m v : ℝ≥0) (h1 : M1 x = m) (h2 : M2 x = (v : ℝ≥0∞) + (m : ℝ≥0∞) ^ 2) :
    M1 (x.map (fun n => 2 * n)) = ((2 * m : ℝ≥0) : ℝ≥0∞) ∧
    M2 (x.map (fun n => 2 * n)) = ((4 * v : ℝ≥0) : ℝ≥0∞) + ((2 * m : ℝ≥0) : ℝ≥0∞) ^ 2 := by
  constructor
  · have e : M1 (x.map (fun n => 2 * n)) = (∑' a, x a * (a : ℝ≥0∞)) * 2 := by
      simp only [M1, tsum_map_mul]
      rw [← ENNReal.tsum_mul_right]; congr 1; ext a; push_cast; ring
    rw [e, show (∑' a, x a * (a : ℝ≥0∞)) = M1 x from rfl, h1]
    first | (push_cast; ring) | push_cast
  · have e : M2 (x.map (fun n => 2 * n)) = (∑' a, x a * (a : ℝ≥0∞) ^ 2) * 4 := by
      simp only [M2, tsum_map_mul]
      rw [← ENNReal.tsum_mul_right]; congr 1; ext a; push_cast; ring
    rw [e, show (∑' a, x a * (a : ℝ≥0∞) ^ 2) = M2 x from rfl, h2]
    first | (push_cast; ring) | push_cast

lemma var_of (μ : PMF ℕ) (m v : ℝ≥0) (h1 : M1 μ = m)
    (h2 : M2 μ = (v : ℝ≥0∞) + (m : ℝ≥0∞) ^ 2) : pmfVar μ = v := by
  have hmean : (pmfMean μ).toReal = m := by
    rw [show pmfMean μ = M1 μ from rfl, h1, ENNReal.coe_toReal]
  have key : ∀ n : ℕ, ENNReal.ofReal (((n:ℝ) - (pmfMean μ).toReal) ^ 2) +
      (n : ℝ≥0∞) * ((2 * m : ℝ≥0) : ℝ≥0∞) = (n : ℝ≥0∞) ^ 2 + (m : ℝ≥0∞) ^ 2 := by
    intro n
    rw [hmean]
    have e1 : (n : ℝ≥0∞) * ((2 * m : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal ((n:ℝ) * ((2 * m : ℝ≥0) : ℝ)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_coe_nnreal]
    have e2 : (n : ℝ≥0∞) ^ 2 + (m : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((n:ℝ) ^ 2 + (m:ℝ) ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_pow (NNReal.coe_nonneg m),
        ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]
    rw [e1, e2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; push_cast; ring
  have hsum : pmfVar μ + M1 μ * ((2 * m : ℝ≥0) : ℝ≥0∞) = M2 μ + (m : ℝ≥0∞) ^ 2 := by
    have e : ∀ n : ℕ, μ n * ENNReal.ofReal (((n:ℝ) - (pmfMean μ).toReal) ^ 2) +
        μ n * (n : ℝ≥0∞) * ((2 * m : ℝ≥0) : ℝ≥0∞) =
        μ n * (n : ℝ≥0∞) ^ 2 + μ n * (m : ℝ≥0∞) ^ 2 := by
      intro n; rw [mul_assoc, ← mul_add, key, mul_add]
    unfold pmfVar M1 M2
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    simp_rw [e]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
  rw [h1, h2] at hsum
  have h3 : (m : ℝ≥0∞) * ((2 * m : ℝ≥0) : ℝ≥0∞) = (m : ℝ≥0∞) ^ 2 + (m : ℝ≥0∞) ^ 2 := by
    push_cast; ring
  rw [h3, add_assoc] at hsum
  exact (ENNReal.add_left_inj (by simp)).mp hsum

/-! ## Part 4: the recursion for x_d and assembly -/

noncomputable def mm (p : ℕ → ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | 1 => (p 1)⁻¹
  | q + 2 => (p (q + 2))⁻¹ * (2 * mm p (q + 1))

noncomputable def vv (p : ℕ → ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | 1 => (1 - p 1) / (p 1) ^ 2
  | q + 2 => (p (q + 2))⁻¹ * (2 * vv p (q + 1)) +
      (1 - p (q + 2)) / (p (q + 2)) ^ 2 * (4 * (mm p (q + 1)) ^ 2)

lemma xLaw_moments (U : Matrix (Fin 2) (Fin 2) ℂ) (p : ℕ → ℝ≥0)
    (hl : ∀ q, 1 ≤ q → levelProb U q = p q) (h0 : ∀ q, 1 ≤ q → 0 < p q)
    (h1 : ∀ q, 1 ≤ q → p q ≤ 1) (q : ℕ) :
    M1 (xLaw U (q + 1)) = (mm p (q + 1) : ℝ≥0∞) ∧
      M2 (xLaw U (q + 1)) = (vv p (q + 1) : ℝ≥0∞) + (mm p (q + 1) : ℝ≥0∞) ^ 2 := by
  induction q with
  | zero =>
    obtain ⟨g1, g2⟩ := geom_moments (p 1) (h0 1 le_rfl) (h1 1 le_rfl)
    have hx : xLaw U (0 + 1) = geomPos (p 1 : ℝ) := by rw [← hl 1 le_rfl]; rfl
    rw [hx]
    refine ⟨g1, ?_⟩
    rw [g2, ENNReal.coe_add, ENNReal.coe_pow]; rfl
  | succ q ih =>
    obtain ⟨i1, i2⟩ := ih
    have hx : xLaw U (q + 1 + 1) =
        (geomPos (p (q + 1 + 1) : ℝ)).bind fun N => iidSum (xLaw U (q + 1)) (2 * N) := by
      rw [← hl (q + 1 + 1) (by omega)]; rfl
    rw [hx]
    exact geom_bind (p (q + 1 + 1)) (h0 _ (by omega)) (h1 _ (by omega)) (xLaw U (q + 1))
      (mm p (q + 1)) (vv p (q + 1)) i1 i2

theorem main (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (hθ1 : θ0 ≤ Real.pi / 2)
    (hθ : Real.sin θ0 ^ 2 = ‖U 1 0‖ ^ 2) (d : ℕ) (hd : 1 ≤ d) :
    pmfMean (nLaw U d) = ENNReal.ofReal (2 ^ d / ∏ q ∈ Finset.Icc 1 d, P θ0 q) ∧
    (θ0 < Real.pi / 4 →
      pmfVar (nLaw U d) ≤
        ENNReal.ofReal (2 ^ (2 * d + 1) * (1 - P θ0 1) / (∏ q ∈ Finset.Icc 1 d, P θ0 q) ^ 2 *
          (1 + (∏ q ∈ Finset.Icc 1 d, P θ0 q) / (2 ^ d * P θ0 1)))) := by
  have hPq : ∀ q, 1 ≤ q → P θ0 q ≤ 1 ∧ 1 / 2 ≤ P θ0 q := by
    intro q hq
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact P_succ_le θ0 k
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ → ℝ≥0, p = fun q => (P θ0 q).toNNReal := ⟨_, rfl⟩
  have hpc : ∀ q, 1 ≤ q → ((p q : ℝ≥0) : ℝ) = P θ0 q := fun q hq => by
    rw [hpdef]; exact Real.coe_toNNReal _ (by linarith [(hPq q hq).2])
  have hl : ∀ q, 1 ≤ q → levelProb U q = p q := by
    intro q hq
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [hpc _ hq, levelProb_eq U hU θ0 hθ0 hθ1 hθ k]
  have h0 : ∀ q, 1 ≤ q → 0 < p q := fun q hq => by
    rw [← NNReal.coe_pos, hpc q hq]; linarith [(hPq q hq).2]
  have h1 : ∀ q, 1 ≤ q → p q ≤ 1 := fun q hq => by
    rw [← NNReal.coe_le_coe, hpc q hq, NNReal.coe_one]; exact (hPq q hq).1
  have hPi : ∀ n, 0 < ∏ q ∈ Finset.Icc 1 n, P θ0 q := fun n =>
    Finset.prod_pos (fun q hq => by linarith [(hPq q (Finset.mem_Icc.mp hq).1).2])
  have hmm : ∀ e, ((mm p (e + 1) : ℝ≥0) : ℝ) = 2 ^ e / ∏ q ∈ Finset.Icc 1 (e + 1), P θ0 q := by
    intro e
    induction e with
    | zero =>
      show (((p 1)⁻¹ : ℝ≥0) : ℝ) = 2 ^ 0 / ∏ q ∈ Finset.Icc 1 (0 + 1), P θ0 q
      rw [NNReal.coe_inv, hpc 1 le_rfl, Nat.zero_add, Finset.Icc_self, Finset.prod_singleton,
        pow_zero, one_div]
    | succ e ih =>
      have hR := hPq (e + 1 + 1) (by omega)
      have hRne : P θ0 (e + 1 + 1) ≠ 0 := (by linarith [hR.2] : (0:ℝ) < _).ne'
      have hQne := (hPi (e + 1)).ne'
      show ((((p (e + 1 + 1))⁻¹ * (2 * mm p (e + 1)) : ℝ≥0)) : ℝ) = _
      rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_inv, ih, hpc _ (by omega),
        Finset.prod_Icc_succ_top (by omega : 1 ≤ e + 1 + 1)]
      first
        | (push_cast; field_simp; done)
        | (push_cast; field_simp; ring)
        | (field_simp; ring)
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨X1, X2⟩ := xLaw_moments U p hl h0 h1 e
  obtain ⟨N1, N2⟩ := nLaw_mom (xLaw U (e + 1)) _ _ X1 X2
  have hmean : pmfMean (nLaw U (e + 1)) = ((2 * mm p (e + 1) : ℝ≥0) : ℝ≥0∞) := N1
  refine ⟨?_, fun hπ4 => ?_⟩
  · rw [hmean, ← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    rw [hmm e]
    ring
  · have hvar : pmfVar (nLaw U (e + 1)) = ((4 * vv p (e + 1) : ℝ≥0) : ℝ≥0∞) :=
      var_of (nLaw U (e + 1)) _ _ N1 N2
    have hmono : ∀ q, 1 ≤ q → P θ0 1 ≤ P θ0 q := P_mono θ0 hθ0 hπ4
    have hP1 := hPq 1 le_rfl
    have hP1ne : P θ0 1 ≠ 0 := (by linarith [hP1.2] : (0:ℝ) < _).ne'
    have hvv : ∀ e, ((vv p (e + 1) : ℝ≥0) : ℝ) * (∏ q ∈ Finset.Icc 1 (e + 1), P θ0 q) ^ 2 ≤
        2 ^ (2 * e + 1) * (1 - P θ0 1) := by
      intro e
      induction e with
      | zero =>
        show ((vv p 1 : ℝ≥0) : ℝ) * (∏ q ∈ Finset.Icc 1 1, P θ0 q) ^ 2 ≤ 2 ^ (2 * 0 + 1) * (1 - P θ0 1)
        rw [show vv p 1 = (1 - p 1) / (p 1) ^ 2 from rfl, NNReal.coe_div,
          NNReal.coe_sub (h1 1 le_rfl), NNReal.coe_one, NNReal.coe_pow, hpc 1 le_rfl,
          Finset.Icc_self, Finset.prod_singleton, div_mul_cancel₀ _ (pow_ne_zero 2 hP1ne)]
        rw [show (2:ℝ) ^ (2 * 0 + 1) = 2 by norm_num]
        linarith [hP1.1]
      | succ e ih =>
        have hR := hPq (e + 1 + 1) (by omega)
        have hRne : P θ0 (e + 1 + 1) ≠ 0 := (by linarith [hR.2] : (0:ℝ) < _).ne'
        have hQne := (hPi (e + 1)).ne'
        have hmo := hmono (e + 1 + 1) (by omega)
        have hv : ((vv p (e + 1 + 1) : ℝ≥0) : ℝ) =
            (P θ0 (e + 1 + 1))⁻¹ * (2 * (vv p (e + 1) : ℝ)) +
              (1 - P θ0 (e + 1 + 1)) / (P θ0 (e + 1 + 1)) ^ 2 *
                (4 * (2 ^ e / ∏ q ∈ Finset.Icc 1 (e + 1), P θ0 q) ^ 2) := by
          rw [← hpc (e + 1 + 1) (by omega), ← hmm e]
          show ((((p (e + 1 + 1))⁻¹ * (2 * vv p (e + 1)) +
              (1 - p (e + 1 + 1)) / (p (e + 1 + 1)) ^ 2 * (4 * (mm p (e + 1)) ^ 2) : ℝ≥0)) : ℝ) = _
          first
            | (push_cast [NNReal.coe_sub (h1 (e + 1 + 1) (by omega))]; done)
            | (push_cast [NNReal.coe_sub (h1 (e + 1 + 1) (by omega))]; ring)
        rw [hv, Finset.prod_Icc_succ_top (by omega : 1 ≤ e + 1 + 1)]
        set A := ((vv p (e + 1) : ℝ≥0) : ℝ) with hA
        set Q := ∏ q ∈ Finset.Icc 1 (e + 1), P θ0 q with hQ
        set R := P θ0 (e + 1 + 1) with hRdef
        have key : (R⁻¹ * (2 * A) + (1 - R) / R ^ 2 * (4 * (2 ^ e / Q) ^ 2)) * (Q * R) ^ 2 =
            2 * R * (A * Q ^ 2) + (1 - R) * 2 ^ (2 * e + 2) := by
          first | (field_simp; ring) | (field_simp; done)
        rw [key]
        have hK : (0:ℝ) < 2 ^ (2 * e + 1) := by positivity
        have e1 : (2:ℝ) ^ (2 * e + 2) = 2 * 2 ^ (2 * e + 1) := by ring
        have e2 : (2:ℝ) ^ (2 * (e + 1) + 1) = 4 * 2 ^ (2 * e + 1) := by ring
        rw [e1, e2]
        nlinarith [mul_le_mul_of_nonneg_left ih (by linarith [hR.2] : (0:ℝ) ≤ 2 * R),
          mul_nonneg (mul_nonneg hK.le (sub_nonneg.2 hR.1)) (sub_nonneg.2 hP1.1),
          mul_nonneg hK.le (sub_nonneg.2 hmo)]
    rw [hvar, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    have hPie := hPi (e + 1)
    have hA := hvv e
    have hfac : 1 ≤ 1 + (∏ q ∈ Finset.Icc 1 (e + 1), P θ0 q) / (2 ^ (e + 1) * P θ0 1) :=
      le_add_of_nonneg_right (div_nonneg hPie.le
        (mul_nonneg (by positivity) (by linarith [hP1.2])))
    have hbase : 4 * ((vv p (e + 1) : ℝ≥0) : ℝ) ≤
        2 ^ (2 * (e + 1) + 1) * (1 - P θ0 1) / (∏ q ∈ Finset.Icc 1 (e + 1), P θ0 q) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hPie 2)]
      have : (2:ℝ) ^ (2 * (e + 1) + 1) = 4 * 2 ^ (2 * e + 1) := by ring
      rw [this]; nlinarith [hA]
    refine le_trans hbase (le_mul_of_one_le_right ?_ hfac)
    exact div_nonneg (mul_nonneg (by positivity) (by linarith [hP1.1])) (pow_pos hPie 2).le

end FloatPointSynth.Gearbox.Aux278

open FloatPointSynth.Gearbox in
theorem solution (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (hθ1 : θ0 ≤ Real.pi / 2)
    (hθ : Real.sin θ0 ^ 2 = ‖U 1 0‖ ^ 2) (d : ℕ) (hd : 1 ≤ d) :
    pmfMean (nLaw U d) = ENNReal.ofReal (2 ^ d / ∏ q ∈ Finset.Icc 1 d, P θ0 q) ∧
    (θ0 < Real.pi / 4 →
      pmfVar (nLaw U d) ≤
        ENNReal.ofReal (2 ^ (2 * d + 1) * (1 - P θ0 1) / (∏ q ∈ Finset.Icc 1 d, P θ0 q) ^ 2 *
          (1 + (∏ q ∈ Finset.Icc 1 d, P θ0 q) / (2 ^ d * P θ0 1)))) := by
  exact FloatPointSynth.Gearbox.Aux278.main U hU θ0 hθ0 hθ1 hθ d hd
