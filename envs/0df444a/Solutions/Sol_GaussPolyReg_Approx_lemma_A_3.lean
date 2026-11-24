-- Prove2me | solution 1 for GaussPolyReg.Approx.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T18:57:44.23369+00:00
-- url     : https://prove2.me/submissions/73f72018-1707-41bc-bd21-fc117415d36b

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Chaos
import Theorems.Thm_GaussianMatrix_gaussian_logsobolev

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

/-- Algebraic (non-closed) span of the Hermite products of degree ≤ d. -/
def polySpanLE (d : ℕ) : Submodule ℝ Original :=
  Submodule.span ℝ {p : Original | ∃ α : ℕ →₀ ℕ, multiDegree α ≤ d ∧
    (p : Sample → ℝ) =ᵐ[gaussianProduct ℕ] heMulti α}

/-- Finite span of Hermite products of degree ≤ d on finitely many coordinates `ι`. -/
def finPolySpan (ι : Type) [Fintype ι] (d : ℕ) : Submodule ℝ ((ι → ℝ) → ℝ) :=
  Submodule.span ℝ {g | ∃ α : ι → ℕ, ∑ i, α i ≤ d ∧ g = fun y => ∏ i, hermite (α i) (y i)}

namespace Hyper

/-! ### One-dimensional Hermite polynomials -/

/-- Real probabilists' Hermite polynomial. -/
def He (n : ℕ) : Polynomial ℝ := (Polynomial.hermite n).map (Int.castRingHom ℝ)

lemma hermite_eq (n : ℕ) (y : ℝ) : hermite n y = (He n).eval y := by
  rw [hermite, He, Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq]

lemma He_succ (n : ℕ) :
    He (n+1) = Polynomial.X * He n - Polynomial.derivative (He n) := by
  rw [He, He, Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.derivative_map]

lemma He_zero : He 0 = 1 := by simp [He]

lemma He_natDegree_le (n : ℕ) : (He n).natDegree ≤ n :=
  Polynomial.natDegree_map_le.trans (by rw [Polynomial.natDegree_hermite])

lemma derivative_He (n : ℕ) :
    Polynomial.derivative (He (n+1)) = Polynomial.C ((n:ℝ)+1) * He n := by
  induction n with
  | zero => simp [He]
  | succ n ih =>
    rw [He_succ (n+1)]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X,
      Polynomial.derivative_C, ih, zero_mul, zero_add, one_mul]
    have h2 := He_succ n
    simp only [Nat.cast_add, Nat.cast_one, Polynomial.C_add, Polynomial.C_1]
    linear_combination (-(Polynomial.C (n:ℝ) + 1)) * h2

lemma He_ode (n : ℕ) :
    Polynomial.derivative (Polynomial.derivative (He n))
      - Polynomial.X * Polynomial.derivative (He n) = -(Polynomial.C (n:ℝ) * He n) := by
  cases n with
  | zero => simp [He_zero]
  | succ m =>
    rw [derivative_He m]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
    have h := He_succ m
    simp only [Nat.cast_add, Nat.cast_one, Polynomial.C_add, Polynomial.C_1]
    linear_combination (Polynomial.C (m:ℝ) + 1) * h

lemma poly_contDiff (p : Polynomial ℝ) : ContDiff ℝ 1 fun x => p.eval x := by
  have := Polynomial.contDiff_aeval (𝕜 := ℝ) p 1
  simpa using this

/-! ### One-dimensional integrability and integration by parts -/

lemma integrable_exp_abs (K : ℝ) :
    Integrable (fun s : ℝ => Real.exp (K * |s|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) K).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-K))).mono'
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]; have := Real.exp_pos (-K * s); linarith
  · rw [abs_of_nonpos hs]; have := Real.exp_pos (K * s)
    have e : K * -s = -K * s := by ring
    rw [e]; linarith

lemma poly_bound (p : Polynomial ℝ) : ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |p.eval s| ≤ C * Real.exp |s| := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * (i.factorial : ℝ),
    Finset.sum_nonneg fun i _ => by positivity, fun s => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := Real.pow_div_factorial_le_exp |s| (abs_nonneg s) i
  have hf : (0:ℝ) < i.factorial := by exact_mod_cast Nat.factorial_pos i
  rw [div_le_iff₀ hf] at h
  calc |s| ^ i ≤ Real.exp |s| * i.factorial := h
    _ = _ := mul_comm _ _

lemma integrable_poly (p : Polynomial ℝ) :
    Integrable (fun s => p.eval s) (gaussianReal 0 1) := by
  obtain ⟨C, -, h⟩ := poly_bound p
  refine ((integrable_exp_abs 1).const_mul C).mono' (Polynomial.continuous p).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, one_mul]; exact h s

lemma integrable_gaussian_iff (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [smul_eq_mul]

lemma gaussianPDFReal_zero_one_eq :
    gaussianPDFReal 0 1 = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  funext x; simp [gaussianPDFReal_def]

lemma hasDerivAt_pdf (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(x * gaussianPDFReal 0 1 x)) x := by
  rw [gaussianPDFReal_zero_one_eq]
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-x) x :=
    (((hasDerivAt_pow 2 x).neg).div_const 2).congr_deriv (by norm_num; ring)
  exact ((h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹).congr_deriv (by ring)

/-- Gaussian integration by parts on the line. -/
lemma ibp1 (f f' : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (f' s) s)
    (h1 : Integrable (fun s => s * f s) (gaussianReal 0 1))
    (h2 : Integrable f' (gaussianReal 0 1)) (h3 : Integrable f (gaussianReal 0 1)) :
    ∫ s, s * f s ∂(gaussianReal 0 1) = ∫ s, f' s ∂(gaussianReal 0 1) := by
  rw [integrable_gaussian_iff] at h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  set φ := gaussianPDFReal 0 1
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f) (v := fun x => -φ x)
    (u' := f') (v' := fun x => x * φ x)
    (fun x _ => hd x)
    (fun x _ => ((hasDerivAt_pdf x).neg).congr_deriv (by ring))
    (by
      have : (f * fun x => x * φ x) = fun x => φ x * (x * f x) := by funext x; simp; ring
      rw [this]; exact h1)
    (by
      have : (f' * fun x => -φ x) = fun x => -(φ x * f' x) := by funext x; simp; ring
      rw [this]; exact h2.neg)
    (by
      have : (f * fun x => -φ x) = fun x => -(φ x * f x) := by funext x; simp; ring
      rw [this]; exact h3.neg)
  have e1 : (fun x => φ x * (x * f x)) = fun x => f x * (x * φ x) := by funext x; ring
  have e2 : (fun x => φ x * f' x) = fun x => -(f' x * -φ x) := by funext x; ring
  rw [e1, key, e2, integral_neg]

lemma integral_poly_He (n : ℕ) : ∀ p : Polynomial ℝ, p.natDegree < n →
    ∫ s, p.eval s * (He n).eval s ∂(gaussianReal 0 1) = 0 := by
  induction n with
  | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
  | succ n ih =>
    intro p hp
    have hX : Integrable (fun s => s * (p * He n).eval s) (gaussianReal 0 1) := by
      have := integrable_poly (Polynomial.X * (p * He n))
      simpa only [Polynomial.eval_mul, Polynomial.eval_X] using this
    have hibp := ibp1 (fun s => (p * He n).eval s)
      (fun s => (Polynomial.derivative (p * He n)).eval s)
      (fun s => Polynomial.hasDerivAt _ s) hX (integrable_poly _) (integrable_poly _)
    have e : ∀ s, p.eval s * (He (n+1)).eval s
        = s * (p * He n).eval s - (p * Polynomial.derivative (He n)).eval s := by
      intro s; rw [He_succ]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X]; ring
    simp_rw [e]
    rw [integral_sub hX (integrable_poly _), hibp,
      ← integral_sub (integrable_poly _) (integrable_poly _)]
    have e2 : ∀ s, (Polynomial.derivative (p * He n)).eval s
        - (p * Polynomial.derivative (He n)).eval s
        = (Polynomial.derivative p).eval s * (He n).eval s := by
      intro s; simp only [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul]; ring
    simp_rw [e2]
    by_cases h0 : p.natDegree = 0
    · rw [Polynomial.derivative_of_natDegree_zero h0]; simp
    · exact ih _ (lt_of_lt_of_le (Polynomial.natDegree_derivative_lt h0) (Nat.lt_succ_iff.mp hp))

lemma He_orth {m n : ℕ} (h : m ≠ n) :
    ∫ s, (He m).eval s * (He n).eval s ∂(gaussianReal 0 1) = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · exact integral_poly_He n (He m) (lt_of_le_of_lt (He_natDegree_le m) h)
  · have := integral_poly_He m (He n) (lt_of_le_of_lt (He_natDegree_le n) h)
    simpa only [mul_comm] using this

/-! ### Products of polynomials in several coordinates -/

variable {ι : Type} [Fintype ι]

/-- The standard Gaussian measure on `ι → ℝ`. -/
abbrev γ (ι : Type) [Fintype ι] : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1

def Pr (P : ι → Polynomial ℝ) (x : ι → ℝ) : ℝ := ∏ i, (P i).eval (x i)

lemma Pr_continuous (P : ι → Polynomial ℝ) : Continuous (Pr P) :=
  show Continuous fun x : ι → ℝ => ∏ i, (P i).eval (x i) from
    continuous_finset_prod _ fun i _ => (Polynomial.continuous (P i)).comp (continuous_apply i)

lemma Pr_contDiff (P : ι → Polynomial ℝ) : ContDiff ℝ 1 (Pr P) :=
  show ContDiff ℝ 1 fun x : ι → ℝ => ∏ i, (P i).eval (x i) from
    contDiff_prod fun i _ => (poly_contDiff (P i)).comp (contDiff_apply ℝ ℝ i)

section Dec
variable [DecidableEq ι]

lemma Pr_split (P : ι → Polynomial ℝ) (x : ι → ℝ) (i : ι) :
    Pr P x = (P i).eval (x i) * ∏ l ∈ Finset.univ.erase i, (P l).eval (x l) := by
  rw [Pr, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

lemma Pr_update_x (P : ι → Polynomial ℝ) (x : ι → ℝ) (i : ι) (s : ℝ) :
    Pr P (Function.update x i s)
      = (P i).eval s * ∏ l ∈ Finset.univ.erase i, (P l).eval (x l) := by
  rw [Pr_split P _ i, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

lemma Pr_update_P (P : ι → Polynomial ℝ) (Q : Polynomial ℝ) (x : ι → ℝ) (i : ι) :
    Pr (Function.update P i Q) x
      = Q.eval (x i) * ∏ l ∈ Finset.univ.erase i, (P l).eval (x l) := by
  rw [Pr_split _ _ i, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

lemma Pr_hasDerivAt (P : ι → Polynomial ℝ) (x : ι → ℝ) (i : ι) (s : ℝ) :
    HasDerivAt (fun s => Pr P (Function.update x i s))
      (Pr (Function.update P i (Polynomial.derivative (P i))) (Function.update x i s)) s := by
  have e : (fun s => Pr P (Function.update x i s))
      = fun s => (P i).eval s * ∏ l ∈ Finset.univ.erase i, (P l).eval (x l) :=
    funext fun s' => Pr_update_x P x i s'
  rw [e, Pr_update_P, Function.update_self]
  have : ∏ l ∈ Finset.univ.erase i, (P l).eval (Function.update x i s l)
      = ∏ l ∈ Finset.univ.erase i, (P l).eval (x l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [this]
  exact (Polynomial.hasDerivAt (P i) s).mul_const _

end Dec

/-! ### Exponentially dominated functions -/

/-- `f` is bounded by `C exp(K Σ|xᵢ|)`. -/
def Dom (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ C K : ℝ, 0 ≤ K ∧ ∀ x, |f x| ≤ C * Real.exp (K * ∑ i, |x i|)

lemma sum_abs_nonneg (x : ι → ℝ) : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _

lemma Dom.of_le {f g : (ι → ℝ) → ℝ} (hf : Dom f) (h : ∀ x, |g x| ≤ |f x|) : Dom g := by
  obtain ⟨C, K, hK, hb⟩ := hf
  exact ⟨C, K, hK, fun x => (h x).trans (hb x)⟩

lemma Dom.of_le' {f g : (ι → ℝ) → ℝ} (hf : Dom f) (h : ∀ x, |g x| ≤ f x) : Dom g :=
  hf.of_le fun x => (h x).trans (le_abs_self _)

lemma dom_const (c : ℝ) : Dom (ι := ι) fun _ => c :=
  ⟨|c|, 0, le_rfl, fun x => by simp⟩

lemma Dom.add {f g : (ι → ℝ) → ℝ} (hf : Dom f) (hg : Dom g) : Dom fun x => f x + g x := by
  obtain ⟨C1, K1, hK1, h1⟩ := hf
  obtain ⟨C2, K2, hK2, h2⟩ := hg
  refine ⟨|C1| + |C2|, K1 + K2, add_nonneg hK1 hK2, fun x => ?_⟩
  have hS := sum_abs_nonneg x
  have e1 : Real.exp (K1 * ∑ i, |x i|) ≤ Real.exp ((K1 + K2) * ∑ i, |x i|) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (K2 * ∑ i, |x i|) ≤ Real.exp ((K1 + K2) * ∑ i, |x i|) :=
    Real.exp_le_exp.2 (by nlinarith)
  have b1 : C1 * Real.exp (K1 * ∑ i, |x i|) ≤ |C1| * Real.exp ((K1 + K2) * ∑ i, |x i|) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C1) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
  have b2 : C2 * Real.exp (K2 * ∑ i, |x i|) ≤ |C2| * Real.exp ((K1 + K2) * ∑ i, |x i|) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
  have a1 := h1 x
  have a2 := h2 x
  have := abs_add_le (f x) (g x)
  rw [add_mul]; linarith

lemma Dom.mul {f g : (ι → ℝ) → ℝ} (hf : Dom f) (hg : Dom g) : Dom fun x => f x * g x := by
  obtain ⟨C1, K1, hK1, h1⟩ := hf
  obtain ⟨C2, K2, hK2, h2⟩ := hg
  refine ⟨C1 * C2, K1 + K2, add_nonneg hK1 hK2, fun x => ?_⟩
  rw [abs_mul, add_mul, Real.exp_add]
  calc |f x| * |g x|
      ≤ (C1 * Real.exp (K1 * ∑ i, |x i|)) * (C2 * Real.exp (K2 * ∑ i, |x i|)) :=
        mul_le_mul (h1 x) (h2 x) (abs_nonneg _) ((abs_nonneg _).trans (h1 x))
    _ = _ := by ring

lemma Dom.abs {f : (ι → ℝ) → ℝ} (hf : Dom f) : Dom fun x => |f x| :=
  hf.of_le fun x => by rw [abs_abs]

lemma Dom.pow {f : (ι → ℝ) → ℝ} (hf : Dom f) (n : ℕ) : Dom fun x => f x ^ n := by
  induction n with
  | zero => simpa using dom_const (ι := ι) 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma Dom.sum {κ : Type} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ} (h : ∀ j ∈ s, Dom (f j)) :
    Dom fun x => ∑ j ∈ s, f j x := by
  have := Finset.sum_induction f (fun g => Dom g) (fun a b ha hb => ha.add hb)
    (dom_const (ι := ι) 0) h
  have e : (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, f j := by
    funext x; simp [Finset.sum_apply]
  rw [e]; exact this

lemma dom_Pr (P : ι → Polynomial ℝ) : Dom (Pr P) := by
  choose C hC hb using fun l => poly_bound (P l)
  refine ⟨∏ l, C l, 1, zero_le_one, fun x => ?_⟩
  rw [Pr, Finset.abs_prod, one_mul, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun l _ => abs_nonneg _) fun l _ => hb l (x l)

lemma dom_coord (i : ι) : Dom fun x : ι → ℝ => x i :=
  ⟨1, 1, zero_le_one, fun x => by
    have h1 : |x i| ≤ ∑ l, |x l| :=
      Finset.single_le_sum (f := fun l => |x l|) (fun l _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := Real.add_one_le_exp (∑ l, |x l|)
    rw [one_mul, one_mul]; linarith⟩

lemma integrable_expSum (K : ℝ) :
    Integrable (fun x : ι → ℝ => Real.exp (K * ∑ i, |x i|)) (γ ι) := by
  have : (fun x : ι → ℝ => Real.exp (K * ∑ i, |x i|)) = fun x => ∏ i, Real.exp (K * |x i|) := by
    funext x; rw [Finset.mul_sum, Real.exp_sum]
  rw [this]
  exact Integrable.fintype_prod (f := fun _ s => Real.exp (K * |s|)) fun _ => integrable_exp_abs K

lemma Dom.integrable {f : (ι → ℝ) → ℝ} (hf : Dom f) (hm : Continuous f) : Integrable f (γ ι) := by
  obtain ⟨C, K, -, h⟩ := hf
  exact ((integrable_expSum K).const_mul C).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x)

/-! ### Real-number inequalities -/

lemma rpow_le_aux {w ε r : ℝ} {N : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hw : ε ≤ w) (hr : |r| ≤ N) :
    w ^ r ≤ (1/ε) ^ N + (1 + w) ^ N := by
  have hw0 : 0 < w := hε.trans_le hw
  rcases le_total 0 r with h | h
  · have h1 : w ^ r ≤ (1 + w) ^ r := Real.rpow_le_rpow hw0.le (by linarith) h
    have h2 : (1 + w) ^ r ≤ (1 + w) ^ (N:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [abs_of_nonneg h] at hr; exact hr)
    rw [Real.rpow_natCast] at h2
    have : 0 ≤ (1/ε) ^ N := by positivity
    linarith
  · have h1 : w ^ r ≤ ε ^ r := Real.rpow_le_rpow_of_nonpos hε hw h
    have h2 : ε ^ r = (1/ε) ^ (-r) := by
      rw [one_div, Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv]
    have h3 : (1/ε) ^ (-r) ≤ (1/ε) ^ (N:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by rw [le_div_iff₀ hε]; linarith)
        (by rw [abs_of_nonpos h] at hr; exact hr)
    rw [Real.rpow_natCast] at h3
    have : 0 ≤ (1 + w) ^ N := by positivity
    linarith

lemma abs_log_le {w ε : ℝ} (hε : 0 < ε) (hw : ε ≤ w) : |Real.log w| ≤ w + |Real.log ε| := by
  have hw0 : 0 < w := hε.trans_le hw
  have h1 := Real.log_le_sub_one_of_pos hw0
  have h2 := Real.log_le_log hε hw
  have h3 := neg_abs_le (Real.log ε)
  have h4 := abs_nonneg (Real.log ε)
  rw [abs_le]; constructor <;> linarith

lemma mul_le_mul3 {a b c A B C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C) : a * b * c ≤ A * B * C := by
  have hA := ha.trans h1
  have hB := hb.trans h2
  exact mul_le_mul (mul_le_mul h1 h2 hb hA) h3 hc (mul_nonneg hA hB)

lemma mul_le_mul5 {a b c d e A B C D E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C) (h4 : d ≤ D) (h5 : e ≤ E) :
    a * b * c * d * e ≤ A * B * C * D * E := by
  have hA := ha.trans h1
  have hB := hb.trans h2
  have hC := hc.trans h3
  have hD := hd.trans h4
  refine mul_le_mul ?_ h5 he (mul_nonneg (mul_nonneg (mul_nonneg hA hB) hC) hD)
  refine mul_le_mul ?_ h4 hd (mul_nonneg (mul_nonneg hA hB) hC)
  exact mul_le_mul (mul_le_mul h1 h2 hb hA) h3 hc (mul_nonneg hA hB)

/-! ### Integration by parts in one coordinate -/

section Fubini
variable [DecidableEq ι]

lemma mp_update (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((γ ι).prod (gaussianReal 0 1)) (γ ι) := by
  refine ⟨measurable_update', ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (Function.update s i Set.univ) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [this, Measure.prod_prod, Measure.pi_pi,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul Finset.univ (fun j => (gaussianReal 0 1) (s j)) (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma integrable_comp_update (i : ι) {F : (ι → ℝ) → ℝ} (hF : Integrable F (γ ι)) :
    Integrable (fun p : (ι → ℝ) × ℝ => F (Function.update p.1 i p.2))
      ((γ ι).prod (gaussianReal 0 1)) :=
  ((mp_update i).integrable_comp hF.aestronglyMeasurable).2 hF

lemma integral_update_eq (i : ι) {F : (ι → ℝ) → ℝ} (hF : Integrable F (γ ι)) :
    ∫ x, ∫ t, F (Function.update x i t) ∂(gaussianReal 0 1) ∂(γ ι) = ∫ x, F x ∂(γ ι) := by
  have hmp := mp_update (ι := ι) i
  rw [← integral_prod _ (integrable_comp_update i hF)]
  calc ∫ p, F (Function.update p.1 i p.2) ∂((γ ι).prod (gaussianReal 0 1))
      = ∫ x, F x ∂(Measure.map (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
          ((γ ι).prod (gaussianReal 0 1))) :=
        (integral_map hmp.measurable.aemeasurable
          (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)).symm
    _ = ∫ x, F x ∂(γ ι) := by rw [hmp.map_eq]

lemma integrable_section_ae (i : ι) {F : (ι → ℝ) → ℝ} (hF : Integrable F (γ ι)) :
    ∀ᵐ x ∂(γ ι), Integrable (fun t => F (Function.update x i t)) (gaussianReal 0 1) :=
  (integrable_comp_update i hF).prod_right_ae

lemma ibp_coord (i : ι) (f f' : (ι → ℝ) → ℝ)
    (hd : ∀ x s, HasDerivAt (fun s => f (Function.update x i s)) (f' (Function.update x i s)) s)
    (h1 : Integrable (fun x => x i * f x) (γ ι)) (h2 : Integrable f' (γ ι))
    (h3 : Integrable f (γ ι)) :
    ∫ x, x i * f x ∂(γ ι) = ∫ x, f' x ∂(γ ι) := by
  rw [← integral_update_eq i h1, ← integral_update_eq i h2]
  refine integral_congr_ae ?_
  filter_upwards [integrable_section_ae i h1, integrable_section_ae i h2,
    integrable_section_ae i h3] with x hx1 hx2 hx3
  simp only [Function.update_self] at hx1 ⊢
  exact ibp1 (fun s => f (Function.update x i s)) (fun s => f' (Function.update x i s))
    (hd x) hx1 hx2 hx3

end Fubini

/-! ### The Ornstein–Uhlenbeck flow on a finite Hermite combination -/

section Flow
variable {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ι → ℕ)

def kk (j : Fin n) : ℝ := ∑ i, (α j i : ℝ)

def P0 (j : Fin n) : ι → Polynomial ℝ := fun l => He (α j l)

def U (t : ℝ) (x : ι → ℝ) : ℝ := ∑ j, a j * Real.exp (-(kk α j) * t) * Pr (P0 α j) x

def V (t : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ j, a j * (-(kk α j) * Real.exp (-(kk α j) * t)) * Pr (P0 α j) x

lemma U_continuous (t : ℝ) : Continuous (U a α t) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul (Pr_continuous _)

lemma V_continuous (t : ℝ) : Continuous (V a α t) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul (Pr_continuous _)

lemma U_contDiff (t : ℝ) : ContDiff ℝ 1 (U a α t) :=
  show ContDiff ℝ 1 fun x => ∑ j, a j * Real.exp (-(kk α j) * t) * Pr (P0 α j) x by
    refine ContDiff.sum fun j _ => ?_
    exact (contDiff_const (𝕜 := ℝ) (c := a j * Real.exp (-(kk α j) * t))).mul (Pr_contDiff _)

lemma dom_U (t : ℝ) : Dom (U a α t) :=
  Dom.sum _ fun j _ => (dom_const _).mul (dom_Pr _)

lemma dom_V (t : ℝ) : Dom (V a α t) :=
  Dom.sum _ fun j _ => (dom_const _).mul (dom_Pr _)

lemma U_hasDerivAt_t (x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => U a α t x) (V a α t x) t := by
  unfold U V
  refine HasDerivAt.fun_sum fun j _ => ?_
  have h := ((hasDerivAt_id' t).const_mul (-(kk α j))).exp
  exact ((h.const_mul (a j)).mul_const (Pr (P0 α j) x)).congr_deriv (by ring)

section Dec
variable [DecidableEq ι]

def P1 (j : Fin n) (i : ι) : ι → Polynomial ℝ :=
  Function.update (P0 α j) i (Polynomial.derivative (He (α j i)))

def P2 (j : Fin n) (i : ι) : ι → Polynomial ℝ :=
  Function.update (P0 α j) i (Polynomial.derivative (Polynomial.derivative (He (α j i))))

def D1 (t : ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  ∑ j, a j * Real.exp (-(kk α j) * t) * Pr (P1 α j i) x

def D2 (t : ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  ∑ j, a j * Real.exp (-(kk α j) * t) * Pr (P2 α j i) x

lemma D1_continuous (t : ℝ) (i : ι) : Continuous (D1 a α t i) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul (Pr_continuous _)

lemma D2_continuous (t : ℝ) (i : ι) : Continuous (D2 a α t i) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul (Pr_continuous _)

lemma dom_D1 (t : ℝ) (i : ι) : Dom (D1 a α t i) :=
  Dom.sum _ fun j _ => (dom_const _).mul (dom_Pr _)

lemma dom_D2 (t : ℝ) (i : ι) : Dom (D2 a α t i) :=
  Dom.sum _ fun j _ => (dom_const _).mul (dom_Pr _)

lemma U_sec (t : ℝ) (i : ι) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s => U a α t (Function.update x i s))
      (D1 a α t i (Function.update x i s)) s := by
  unfold U D1 P1
  refine HasDerivAt.fun_sum fun j _ => ?_
  exact (Pr_hasDerivAt (P0 α j) x i s).const_mul (a j * Real.exp (-(kk α j) * t))

lemma D1_sec (t : ℝ) (i : ι) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s => D1 a α t i (Function.update x i s))
      (D2 a α t i (Function.update x i s)) s := by
  have e : ∀ j, Function.update (P1 α j i) i (Polynomial.derivative (P1 α j i i)) = P2 α j i := by
    intro j; simp only [P1, P2, Function.update_idem, Function.update_self]
  unfold D1 D2
  simp_rw [← e]
  refine HasDerivAt.fun_sum fun j _ => ?_
  exact (Pr_hasDerivAt (P1 α j i) x i s).const_mul (a j * Real.exp (-(kk α j) * t))

lemma gen_identity (t : ℝ) (x : ι → ℝ) :
    ∑ i, (D2 a α t i x - x i * D1 a α t i x) = V a α t x := by
  have key : ∀ j i, Pr (P2 α j i) x - x i * Pr (P1 α j i) x
      = -(α j i : ℝ) * Pr (P0 α j) x := by
    intro j i
    rw [P2, P1, Pr_update_P, Pr_update_P, Pr_split (P0 α j) x i]
    have h := congrArg (fun p => Polynomial.eval (x i) p) (He_ode (α j i))
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_neg,
      Polynomial.eval_C] at h
    simp only [P0]
    linear_combination (∏ l ∈ Finset.univ.erase i, (He (α j l)).eval (x l)) * h
  unfold D1 D2 V
  have h1 : ∀ i, (∑ j, a j * Real.exp (-(kk α j) * t) * Pr (P2 α j i) x
      - x i * ∑ j, a j * Real.exp (-(kk α j) * t) * Pr (P1 α j i) x)
      = ∑ j, a j * Real.exp (-(kk α j) * t) * (-(α j i : ℝ) * Pr (P0 α j) x) := by
    intro i
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← key j i]; ring
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [Finset.sum_neg_distrib, kk]
  ring

lemma gen_ibp (t : ℝ) (ψ : (ι → ℝ) → ℝ) (ψ' : ι → (ι → ℝ) → ℝ)
    (hd : ∀ i x s, HasDerivAt (fun s => ψ (Function.update x i s)) (ψ' i (Function.update x i s)) s)
    (hi1 : ∀ i, Integrable (fun x => x i * (ψ x * D1 a α t i x)) (γ ι))
    (hi2 : ∀ i, Integrable (fun x => ψ' i x * D1 a α t i x) (γ ι))
    (hi3 : ∀ i, Integrable (fun x => ψ x * D2 a α t i x) (γ ι))
    (hi4 : ∀ i, Integrable (fun x => ψ x * D1 a α t i x) (γ ι)) :
    ∫ x, ψ x * V a α t x ∂(γ ι) = -∑ i, ∫ x, ψ' i x * D1 a α t i x ∂(γ ι) := by
  have e : ∀ x, ψ x * V a α t x
      = ∑ i, (ψ x * D2 a α t i x - x i * (ψ x * D1 a α t i x)) := by
    intro x; rw [← gen_identity a α t x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => by exact (hi3 i).sub (hi1 i), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_sub (hi3 i) (hi1 i)]
  rw [ibp_coord i (fun x => ψ x * D1 a α t i x)
    (fun x => ψ' i x * D1 a α t i x + ψ x * D2 a α t i x)
    (fun x s => (hd i x s).mul (D1_sec a α t i x s)) (hi1 i) ((hi2 i).add (hi3 i)) (hi4 i)]
  rw [integral_add (hi2 i) (hi3 i)]; ring

end Dec

/-! The `L^{q(t)}` norm functional along the flow. -/

def qf (t : ℝ) : ℝ := 1 + Real.exp (2 * t)

def W (ε t : ℝ) (x : ι → ℝ) : ℝ := U a α t x ^ 2 + ε

def F (ε t : ℝ) (x : ι → ℝ) : ℝ := W a α ε t x ^ (qf t / 2)

def F' (ε t : ℝ) (x : ι → ℝ) : ℝ :=
  2 * U a α t x * V a α t x * (qf t / 2) * W a α ε t x ^ (qf t / 2 - 1)
    + Real.exp (2 * t) * W a α ε t x ^ (qf t / 2) * Real.log (W a α ε t x)

def G (ε t : ℝ) : ℝ := ∫ x, F a α ε t x ∂(γ ι)

variable {a α}
variable {ε : ℝ}

lemma W_ge (hε : 0 < ε) (t : ℝ) (x : ι → ℝ) : ε ≤ W a α ε t x := by
  unfold W; nlinarith [sq_nonneg (U a α t x)]

lemma W_pos (hε : 0 < ε) (t : ℝ) (x : ι → ℝ) : 0 < W a α ε t x := hε.trans_le (W_ge hε t x)

lemma W_continuous (t : ℝ) : Continuous (W a α ε t) :=
  ((U_continuous a α t).pow 2).add continuous_const

lemma dom_W (t : ℝ) : Dom (W a α ε t) := ((dom_U a α t).pow 2).add (dom_const ε)

lemma dom_Wr (hε : 0 < ε) (hε1 : ε ≤ 1) (t r : ℝ) : Dom fun x => W a α ε t x ^ r := by
  have hN : |r| ≤ (⌈|r|⌉₊ : ℝ) := Nat.le_ceil _
  refine Dom.of_le' ((dom_const ((1/ε) ^ ⌈|r|⌉₊)).add
    (((dom_const 1).add (dom_W (a := a) (α := α) (ε := ε) t)).pow ⌈|r|⌉₊)) fun x => ?_
  rw [abs_of_pos (Real.rpow_pos_of_pos (W_pos hε t x) _)]
  exact rpow_le_aux hε hε1 (W_ge hε t x) hN

lemma Wr_continuous (hε : 0 < ε) (t r : ℝ) : Continuous fun x => W a α ε t x ^ r :=
  (W_continuous t).rpow_const fun x => Or.inl (W_pos hε t x).ne'

lemma dom_logW (hε : 0 < ε) (t : ℝ) : Dom fun x => Real.log (W a α ε t x) :=
  Dom.of_le' ((dom_W t).add (dom_const |Real.log ε|)) fun x => abs_log_le hε (W_ge hε t x)

lemma logW_continuous (hε : 0 < ε) (t : ℝ) : Continuous fun x => Real.log (W a α ε t x) :=
  (W_continuous t).log fun x => (W_pos hε t x).ne'

lemma qf_pos (t : ℝ) : 1 < qf t := by unfold qf; linarith [Real.exp_pos (2 * t)]

lemma F_integrable (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) : Integrable (F a α ε t) (γ ι) :=
  (dom_Wr hε hε1 t _).integrable (Wr_continuous hε t _)

lemma F_hasDerivAt (hε : 0 < ε) (x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => F a α ε t x) (F' a α ε t x) t := by
  have hU := U_hasDerivAt_t a α x t
  have hw : HasDerivAt (fun t => W a α ε t x) (2 * U a α t x * V a α t x) t := by
    unfold W
    exact ((hU.pow 2).add_const ε).congr_deriv (by norm_num)
  have hq : HasDerivAt (fun t => qf t / 2) (Real.exp (2 * t)) t := by
    unfold qf
    exact ((((hasDerivAt_id' t).const_mul 2).exp.const_add 1).div_const 2).congr_deriv (by ring)
  exact hw.rpow hq (W_pos hε t x)

lemma F'_continuous (hε : 0 < ε) (t : ℝ) : Continuous (F' a α ε t) := by
  unfold F'
  exact ((((continuous_const.mul (U_continuous a α t)).mul (V_continuous a α t)).mul
    continuous_const).mul (Wr_continuous hε t _)).add
    ((continuous_const.mul (Wr_continuous hε t _)).mul (logW_continuous hε t))

lemma G_pos (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) : 0 < G a α ε t := by
  have h : ∫ _x, ε ^ (qf t / 2) ∂(γ ι) ≤ G a α ε t :=
    integral_mono (integrable_const _) (F_integrable hε hε1 t) fun x =>
      Real.rpow_le_rpow hε.le (W_ge hε t x) (by linarith [qf_pos t])
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hε _) h

lemma exp_neg_le {k t R : ℝ} (ht : |t| ≤ R) : Real.exp (-k * t) ≤ Real.exp (|k| * R) := by
  apply Real.exp_le_exp.2
  have h1 : -k * t ≤ |k| * |t| := by
    rw [← abs_mul]; exact (le_abs_self _).trans (by rw [neg_mul, abs_neg])
  exact h1.trans (mul_le_mul_of_nonneg_left ht (abs_nonneg k))

lemma G_hasDerivAt (hε : 0 < ε) (hε1 : ε ≤ 1) (t0 : ℝ) :
    HasDerivAt (G a α ε) (∫ x, F' a α ε t0 x ∂(γ ι)) t0 := by
  set R := |t0| + 1 with hR
  set Qm := 1 + Real.exp (2 * R) with hQm
  set N := ⌈Qm⌉₊ with hN
  set BU : (ι → ℝ) → ℝ := fun x => ∑ j, |a j| * Real.exp (|kk α j| * R) * |Pr (P0 α j) x|
    with hBU
  set BV : (ι → ℝ) → ℝ :=
    fun x => ∑ j, |a j| * (|kk α j| * Real.exp (|kk α j| * R)) * |Pr (P0 α j) x| with hBV
  set M : (ι → ℝ) → ℝ := fun x => (1/ε) ^ N + (1 + (BU x ^ 2 + ε)) ^ N with hM
  set bound : (ι → ℝ) → ℝ := fun x =>
    2 * BU x * BV x * Qm * M x + Qm * M x * (BU x ^ 2 + ε + |Real.log ε|) with hbound
  have hBUc : Continuous BU := continuous_finsetSum _ fun j _ =>
    continuous_const.mul (Pr_continuous _).abs
  have hBVc : Continuous BV := continuous_finsetSum _ fun j _ =>
    continuous_const.mul (Pr_continuous _).abs
  have hBUd : Dom BU := Dom.sum _ fun j _ => (dom_const _).mul (dom_Pr _).abs
  have hBVd : Dom BV := Dom.sum _ fun j _ => (dom_const _).mul (dom_Pr _).abs
  have hMd : Dom M := (dom_const _).add (((dom_const 1).add ((hBUd.pow 2).add (dom_const ε))).pow N)
  have hMc : Continuous M := continuous_const.add
    ((continuous_const.add ((hBUc.pow 2).add continuous_const)).pow N)
  have hbd : Dom bound :=
    ((((((dom_const 2).mul hBUd).mul hBVd).mul (dom_const Qm)).mul hMd)).add
      (((dom_const Qm).mul hMd).mul (((hBUd.pow 2).add (dom_const ε)).add (dom_const _)))
  have hbc : Continuous bound :=
    ((((continuous_const.mul hBUc).mul hBVc).mul continuous_const).mul hMc).add
      ((continuous_const.mul hMc).mul (((hBUc.pow 2).add continuous_const).add continuous_const))
  have hQm1 : 2 ≤ Qm := by
    have : 1 ≤ Real.exp (2 * R) := Real.one_le_exp (by positivity)
    linarith
  have hNQ : Qm ≤ N := Nat.le_ceil _
  have hbnd : ∀ x, ∀ t ∈ Metric.ball t0 1, ‖F' a α ε t x‖ ≤ bound x := by
    intro x t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have htR : |t| ≤ R := by
      have := abs_sub_abs_le_abs_sub t t0
      linarith
    have hU : |U a α t x| ≤ BU x := by
      unfold U
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exp_neg_le htR)
        (abs_nonneg _)) (abs_nonneg _)
    have hV : |V a α t x| ≤ BV x := by
      unfold V
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (exp_neg_le htR) (abs_nonneg _)) (abs_nonneg _))
        (abs_nonneg _)
    have hW1 := W_ge (a := a) (α := α) hε t x
    have hW2 : W a α ε t x ≤ BU x ^ 2 + ε := by
      unfold W
      have : U a α t x ^ 2 ≤ BU x ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hU 2
      linarith
    have hexp : Real.exp (2 * t) ≤ Qm := by
      have : Real.exp (2 * t) ≤ Real.exp (2 * R) :=
        Real.exp_le_exp.2 (by linarith [le_abs_self t])
      linarith
    have hq2 : qf t / 2 ≤ Qm := by unfold qf; linarith [Real.exp_pos (2 * t)]
    have hq0 : 0 < qf t / 2 := by linarith [qf_pos t]
    have hM1 : ∀ r : ℝ, |r| ≤ N → W a α ε t x ^ r ≤ M x := by
      intro r hr
      refine (rpow_le_aux hε hε1 hW1 hr).trans ?_
      have hA : 0 ≤ 1 + W a α ε t x := by linarith
      have hB : 1 + W a α ε t x ≤ 1 + (BU x ^ 2 + ε) := by linarith
      calc (1/ε) ^ N + (1 + W a α ε t x) ^ N ≤ (1/ε) ^ N + (1 + (BU x ^ 2 + ε)) ^ N :=
            add_le_add le_rfl (pow_le_pow_left₀ hA hB N)
        _ = M x := rfl
    have hr1 : |qf t / 2 - 1| ≤ N := by
      rw [abs_le]; constructor <;> linarith [qf_pos t]
    have hr2 : |qf t / 2| ≤ N := by rw [abs_of_pos hq0]; linarith
    have hlog := abs_log_le hε hW1
    have hWp := W_pos (a := a) (α := α) hε t x
    rw [Real.norm_eq_abs]
    unfold F'
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_pos hq0, abs_of_pos (Real.rpow_pos_of_pos hWp _)]
      exact mul_le_mul5 (by norm_num) (abs_nonneg _) (abs_nonneg _) hq0.le
        (Real.rpow_pos_of_pos hWp _).le le_rfl hU hV hq2 (hM1 _ hr1)
    · rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.rpow_pos_of_pos hWp _)]
      exact mul_le_mul3 (Real.exp_pos _).le (Real.rpow_pos_of_pos hWp _).le (abs_nonneg _)
        hexp (hM1 _ hr2) (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ ι)
    (F := fun t x => F a α ε t x) (F' := fun t x => F' a α ε t x) (x₀ := t0) (bound := bound)
    (Metric.ball_mem_nhds t0 one_pos)
    (Eventually.of_forall fun t => (Wr_continuous hε t _).aestronglyMeasurable)
    (F_integrable hε hε1 t0) (F'_continuous hε t0).aestronglyMeasurable
    (Eventually.of_forall hbnd) (hbd.integrable hbc)
    (Eventually.of_forall fun x t _ => F_hasDerivAt hε x t)
  exact key.2

end Flow


/-! ### The derivative inequality from the logarithmic Sobolev inequality -/

section Key
variable {n : ℕ} {a : Fin n → ℝ} {α : Fin n → ι → ℕ} {ε : ℝ}
variable [DecidableEq ι]

lemma partial_eq (g g' : (ι → ℝ) → ℝ) (hg : Differentiable ℝ g) (i : ι) (x : ι → ℝ)
    (hsec : HasDerivAt (fun s => g (Function.update x i s)) (g' x) (x i)) :
    fderiv ℝ g x (Pi.single i 1) = g' x := by
  have h1 : HasFDerivAt g (fderiv ℝ g x) (Function.update x i (x i)) := by
    rw [Function.update_eq_self]; exact (hg x).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  exact h2.unique hsec

lemma W_sec (t : ℝ) (i : ι) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s => W a α ε t (Function.update x i s))
      (2 * U a α t (Function.update x i s) * D1 a α t i (Function.update x i s)) s := by
  unfold W
  exact (((U_sec a α t i x s).pow 2).add_const ε).congr_deriv (by norm_num)

lemma Wr_sec (hε : 0 < ε) (c t : ℝ) (i : ι) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s => W a α ε t (Function.update x i s) ^ c)
      (2 * U a α t (Function.update x i s) * D1 a α t i (Function.update x i s) * c
        * W a α ε t (Function.update x i s) ^ (c - 1)) s :=
  (W_sec t i x s).rpow_const (Or.inl (W_pos hε t _).ne')

lemma psi_alg {u dd w ε c : ℝ} (hw : w = u ^ 2 + ε) (hw0 : 0 < w) :
    2 * u * dd * (c - 1) * w ^ (c - 1 - 1) * u + w ^ (c - 1) * dd
      = w ^ (c - 2) * dd * ((2 * c - 1) * u ^ 2 + ε) := by
  rw [show c - 1 - 1 = c - 2 by ring, show c - 1 = c - 2 + 1 by ring,
    Real.rpow_add_one hw0.ne']
  rw [hw]; ring

lemma rpow_sq {w : ℝ} (hw : 0 < w) (c : ℝ) : (w ^ c) ^ 2 = w ^ (2 * c) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]; congr 1; push_cast; ring

lemma W_contDiff (t : ℝ) : ContDiff ℝ 1 (W a α ε t) :=
  show ContDiff ℝ 1 fun x => U a α t x ^ 2 + ε from
    ((U_contDiff a α t).pow 2).add contDiff_const

lemma key_ineq (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) :
    qf t * ∫ x, F' a α ε t x ∂(γ ι)
      ≤ (2 * Real.exp (2 * t)) * (G a α ε t * Real.log (G a α ε t)) := by
  have hr0 : 1/2 < qf t / 2 := by have := qf_pos t; linarith
  set r := qf t / 2 with hr
  have hqr : qf t = 2 * r := by rw [hr]; ring
  have hexp : Real.exp (2 * t) = 2 * r - 1 := by rw [hr]; unfold qf; ring
  -- basic dominations and continuity
  have dU := dom_U a α t
  have cU := U_continuous a α t
  have dV := dom_V a α t
  have cV := V_continuous a α t
  have dD1 := dom_D1 a α t
  have cD1 := D1_continuous a α t
  have dD2 := dom_D2 a α t
  have cD2 := D2_continuous a α t
  have dWr := dom_Wr (a := a) (α := α) hε hε1 t
  have cWr := Wr_continuous (a := a) (α := α) hε t
  have dlog := dom_logW (a := a) (α := α) hε t
  have clog := logW_continuous (a := a) (α := α) hε t
  -- the integrals
  set EL := ∫ x, W a α ε t x ^ r * Real.log (W a α ε t x) ∂(γ ι) with hEL
  set EA := ∫ x, ∑ i, W a α ε t x ^ (r - 2) * U a α t x ^ 2 * D1 a α t i x ^ 2 ∂(γ ι) with hEA
  set EB := ∫ x, ∑ i, W a α ε t x ^ (r - 2) * ε * D1 a α t i x ^ 2 ∂(γ ι) with hEB
  set EI := ∫ x, W a α ε t x ^ (r - 1) * U a α t x * V a α t x ∂(γ ι) with hEI
  have iL : Integrable (fun x => W a α ε t x ^ r * Real.log (W a α ε t x)) (γ ι) :=
    ((dWr r).mul dlog).integrable ((cWr r).mul clog)
  have iA : Integrable (fun x => ∑ i, W a α ε t x ^ (r - 2) * U a α t x ^ 2 * D1 a α t i x ^ 2)
      (γ ι) :=
    (Dom.sum _ fun i _ => ((dWr _).mul (dU.pow 2)).mul ((dD1 i).pow 2)).integrable
      (continuous_finsetSum _ fun i _ => ((cWr _).mul (cU.pow 2)).mul ((cD1 i).pow 2))
  have iB : Integrable (fun x => ∑ i, W a α ε t x ^ (r - 2) * ε * D1 a α t i x ^ 2) (γ ι) :=
    (Dom.sum _ fun i _ => ((dWr _).mul (dom_const ε)).mul ((dD1 i).pow 2)).integrable
      (continuous_finsetSum _ fun i _ => ((cWr _).mul continuous_const).mul ((cD1 i).pow 2))
  have iI : Integrable (fun x => W a α ε t x ^ (r - 1) * U a α t x * V a α t x) (γ ι) :=
    (((dWr _).mul dU).mul dV).integrable (((cWr _).mul cU).mul cV)
  have hB : 0 ≤ EB := integral_nonneg fun x => Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos (W_pos hε t x) _).le hε.le) (sq_nonneg _)
  -- (a) decomposition of the derivative
  have hF' : ∫ x, F' a α ε t x ∂(γ ι) = 2 * r * EI + (2 * r - 1) * EL := by
    have e : ∀ x, F' a α ε t x = 2 * r * (W a α ε t x ^ (r - 1) * U a α t x * V a α t x)
        + (2 * r - 1) * (W a α ε t x ^ r * Real.log (W a α ε t x)) := by
      intro x; unfold F'; rw [hexp]; ring
    rw [integral_congr_ae (ae_of_all _ e), integral_add (iI.const_mul _) (iL.const_mul _),
      integral_const_mul, integral_const_mul]
  -- (b) integration by parts
  have hI : EI = -((2 * r - 1) * EA + EB) := by
    have hd : ∀ i x s, HasDerivAt
        (fun s => W a α ε t (Function.update x i s) ^ (r - 1) * U a α t (Function.update x i s))
        (W a α ε t (Function.update x i s) ^ (r - 2) * D1 a α t i (Function.update x i s)
          * ((2 * r - 1) * U a α t (Function.update x i s) ^ 2 + ε)) s := by
      intro i x s
      exact ((Wr_sec hε (r - 1) t i x s).mul (U_sec a α t i x s)).congr_deriv
        (psi_alg rfl (W_pos hε t _))
    have h := gen_ibp a α t (fun x => W a α ε t x ^ (r - 1) * U a α t x)
      (fun i x => W a α ε t x ^ (r - 2) * D1 a α t i x * ((2 * r - 1) * U a α t x ^ 2 + ε)) hd
      (fun i => ((dom_coord i).mul (((dWr _).mul dU).mul (dD1 i))).integrable
        (((continuous_apply i).mul (((cWr _).mul cU).mul (cD1 i)))))
      (fun i => ((((dWr _).mul (dD1 i)).mul (((dom_const _).mul (dU.pow 2)).add (dom_const ε))).mul
        (dD1 i)).integrable ((((cWr _).mul (cD1 i)).mul ((continuous_const.mul (cU.pow 2)).add
          continuous_const)).mul (cD1 i)))
      (fun i => (((dWr _).mul dU).mul (dD2 i)).integrable (((cWr _).mul cU).mul (cD2 i)))
      (fun i => (((dWr _).mul dU).mul (dD1 i)).integrable (((cWr _).mul cU).mul (cD1 i)))
    have e1 : EI = ∫ x, (W a α ε t x ^ (r - 1) * U a α t x) * V a α t x ∂(γ ι) := rfl
    rw [e1, h]
    rw [← integral_finsetSum _ fun i _ => by
      exact ((((dWr _).mul (dD1 i)).mul (((dom_const _).mul (dU.pow 2)).add (dom_const ε))).mul
        (dD1 i)).integrable ((((cWr _).mul (cD1 i)).mul ((continuous_const.mul (cU.pow 2)).add
          continuous_const)).mul (cD1 i))]
    have e2 : ∀ x, ∑ i, W a α ε t x ^ (r - 2) * D1 a α t i x * ((2 * r - 1) * U a α t x ^ 2 + ε)
          * D1 a α t i x
        = (2 * r - 1) * (∑ i, W a α ε t x ^ (r - 2) * U a α t x ^ 2 * D1 a α t i x ^ 2)
          + ∑ i, W a α ε t x ^ (r - 2) * ε * D1 a α t i x ^ 2 := by
      intro x
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [integral_congr_ae (ae_of_all _ e2), integral_add (iA.const_mul _) iB, integral_const_mul]
  -- (c) the logarithmic Sobolev inequality for `W ^ (r/2)`
  have hLSI : r * EL - G a α ε t * Real.log (G a α ε t) ≤ 2 * (r ^ 2 * EA) := by
    set g : (ι → ℝ) → ℝ := fun x => W a α ε t x ^ (r / 2) with hg
    have gC : ContDiff ℝ 1 g :=
      (W_contDiff t).rpow_const_of_ne fun x => (W_pos hε t x).ne'
    have hsq : ∀ x, g x ^ 2 = W a α ε t x ^ r := by
      intro x; simp only [hg]; rw [rpow_sq (W_pos hε t x)]; congr 1; ring
    have hlog : ∀ x, g x ^ 2 * Real.log (g x ^ 2)
        = r * (W a α ε t x ^ r * Real.log (W a α ε t x)) := by
      intro x; rw [hsq, Real.log_rpow (W_pos hε t x)]; ring
    have hpart : ∀ x i, fderiv ℝ g x (Pi.single i 1)
        = 2 * U a α t x * D1 a α t i x * (r / 2) * W a α ε t x ^ (r / 2 - 1) := by
      intro x i
      refine partial_eq g (fun x => 2 * U a α t x * D1 a α t i x * (r / 2)
        * W a α ε t x ^ (r / 2 - 1)) (gC.differentiable one_ne_zero) i x ?_
      have := Wr_sec (a := a) (α := α) hε (r / 2) t i x (x i)
      rw [Function.update_eq_self] at this
      exact this
    have hgrad : ∀ x, ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2
        = r ^ 2 * ∑ i, W a α ε t x ^ (r - 2) * U a α t x ^ 2 * D1 a α t i x ^ 2 := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hpart x i]
      have h2 : (W a α ε t x ^ (r / 2 - 1)) ^ 2 = W a α ε t x ^ (r - 2) := by
        rw [rpow_sq (W_pos hε t x)]; congr 1; ring
      calc (2 * U a α t x * D1 a α t i x * (r / 2) * W a α ε t x ^ (r / 2 - 1)) ^ 2
          = r ^ 2 * ((W a α ε t x ^ (r / 2 - 1)) ^ 2 * U a α t x ^ 2 * D1 a α t i x ^ 2) := by
            ring
        _ = _ := by rw [h2]
    have i2 : Integrable (fun x => g x ^ 2) (γ ι) := by
      simp_rw [hsq]; exact (dWr r).integrable (cWr r)
    have i3 : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (γ ι) := by
      simp_rw [hlog]; exact iL.const_mul r
    have i4 : Integrable (fun x => ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2) (γ ι) := by
      simp_rw [hgrad]; exact iA.const_mul _
    have L := GaussianMatrix.gaussian_logsobolev g gC i2 i3 i4
    simp_rw [hlog, hgrad, hsq] at L
    rw [integral_const_mul, integral_const_mul] at L
    have hGdef : G a α ε t = ∫ x, W a α ε t x ^ r ∂(γ ι) := rfl
    rw [hGdef]; exact L
  rw [hF', hI, hqr, hexp]
  nlinarith [mul_le_mul_of_nonneg_left hLSI (by linarith : (0:ℝ) ≤ 2 * r - 1),
    mul_nonneg (sq_nonneg r) hB]

lemma Phi_antitone (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Antitone fun t => Real.log (G a α ε t) / qf t := by
  have hd : ∀ t, HasDerivAt (fun t => Real.log (G a α ε t) / qf t)
      (((∫ x, F' a α ε t x ∂(γ ι)) / G a α ε t * qf t
        - Real.log (G a α ε t) * (2 * Real.exp (2 * t))) / qf t ^ 2) t := by
    intro t
    have hq : HasDerivAt qf (2 * Real.exp (2 * t)) t := by
      show HasDerivAt (fun t => 1 + Real.exp (2 * t)) _ t
      exact (((hasDerivAt_id' t).const_mul 2).exp.const_add 1).congr_deriv (by ring)
    exact ((G_hasDerivAt hε hε1 t).log (G_pos hε hε1 t).ne').div hq (by linarith [qf_pos t])
  refine antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt) fun t => ?_
  rw [(hd t).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hG := G_pos (a := a) (α := α) hε hε1 t
  have hk := key_ineq (a := a) (α := α) hε hε1 t
  have e : (∫ x, F' a α ε t x ∂(γ ι)) / G a α ε t * qf t
      = (qf t * ∫ x, F' a α ε t x ∂(γ ι)) / G a α ε t := by ring
  rw [e, sub_nonpos, div_le_iff₀ hG]
  nlinarith [hk]

omit [DecidableEq ι] in
lemma dom_abs_rpow {g : (ι → ℝ) → ℝ} (hg : Dom g) {p : ℝ} (hp : 0 ≤ p) :
    Dom fun x => |g x| ^ p := by
  refine Dom.of_le' (((dom_const 1).add hg.abs).pow ⌈p⌉₊) fun x => ?_
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have h1 : |g x| ^ p ≤ (1 + |g x|) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) (by linarith) hp
  have h2 : (1 + |g x|) ^ p ≤ (1 + |g x|) ^ (⌈p⌉₊ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (g x)]) (Nat.le_ceil p)
  rw [Real.rpow_natCast] at h2
  exact h1.trans h2

lemma flow_bound (hε : 0 < ε) (hε1 : ε ≤ 1) (T : ℝ) (hT : 0 ≤ T) :
    ∫ x, |U a α T x| ^ qf T ∂(γ ι) ≤ (∫ x, U a α 0 x ^ 2 ∂(γ ι) + ε) ^ (qf T / 2) := by
  have hmono := Phi_antitone (a := a) (α := α) hε hε1 hT
  simp only at hmono
  have hq0 : qf 0 = 2 := by unfold qf; norm_num
  have hG0 : G a α ε 0 = ∫ x, U a α 0 x ^ 2 ∂(γ ι) + ε := by
    have e : ∀ x, F a α ε 0 x = U a α 0 x ^ 2 + ε := by
      intro x; unfold F W; rw [hq0]; norm_num
    unfold G
    simp_rw [e]
    rw [integral_add (((dom_U a α 0).pow 2).integrable ((U_continuous a α 0).pow 2))
      (integrable_const ε), integral_const]
    simp
  have hGT := G_pos (a := a) (α := α) hε hε1 T
  have hG0p := G_pos (a := a) (α := α) hε hε1 0
  rw [hq0] at hmono
  have hqT := qf_pos T
  have h1 : Real.log (G a α ε T) ≤ Real.log (G a α ε 0) * (qf T / 2) := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)] at hmono
    nlinarith
  have h2 : G a α ε T ≤ G a α ε 0 ^ (qf T / 2) := by
    rw [Real.rpow_def_of_pos hG0p, ← Real.exp_log hGT]
    exact Real.exp_le_exp.2 h1
  rw [← hG0]
  refine le_trans ?_ h2
  refine integral_mono ((dom_abs_rpow (dom_U a α T) (by linarith)).integrable
    ((U_continuous a α T).abs.rpow_const fun _ => Or.inr (by linarith)))
    (F_integrable hε hε1 T) fun x => ?_
  show |U a α T x| ^ qf T ≤ (U a α T x ^ 2 + ε) ^ (qf T / 2)
  have e : |U a α T x| ^ qf T = (U a α T x ^ 2) ^ (qf T / 2) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1; push_cast; ring
  rw [e]
  exact Real.rpow_le_rpow (sq_nonneg _) (by linarith) (by linarith)

end Key

/-! ### Orthogonality of Hermite products of different degrees -/

section Orth
variable {n : ℕ}

def Mx (α : Fin n → ι → ℕ) (j j' : Fin n) : ℝ :=
  ∫ x, Pr (P0 α j) x * Pr (P0 α j') x ∂(γ ι)

lemma orth (α : Fin n → ι → ℕ) (j j' : Fin n) (h : kk α j ≠ kk α j') : Mx α j j' = 0 := by
  have : ∃ i, α j i ≠ α j' i := by
    by_contra hc
    push_neg at hc
    exact h (by unfold kk; exact Finset.sum_congr rfl fun i _ => by rw [hc i])
  obtain ⟨i, hi⟩ := this
  unfold Mx Pr
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun i s => (P0 α j i).eval s * (P0 α j' i).eval s)]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (He_orth hi)

lemma sq_expand (s : Finset (Fin n)) (β : Fin n → ℝ) (α : Fin n → ι → ℕ) :
    ∫ x, (∑ j ∈ s, β j * Pr (P0 α j) x) ^ 2 ∂(γ ι)
      = ∑ j ∈ s, ∑ j' ∈ s, β j * β j' * Mx α j j' := by
  have hint : ∀ j j', Integrable (fun x => Pr (P0 α j) x * Pr (P0 α j') x) (γ ι) :=
    fun j j' => ((dom_Pr _).mul (dom_Pr _)).integrable ((Pr_continuous _).mul (Pr_continuous _))
  have e : ∀ x, (∑ j ∈ s, β j * Pr (P0 α j) x) ^ 2
      = ∑ j ∈ s, ∑ j' ∈ s, β j * β j' * (Pr (P0 α j) x * Pr (P0 α j') x) := by
    intro x; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  rw [integral_congr_ae (ae_of_all _ e),
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => (hint j j').const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun j' _ => (hint j j').const_mul _]
  exact Finset.sum_congr rfl fun j' _ => integral_const_mul _ _

lemma weighted (b : ℝ → ℝ) (c : Fin n → ℝ) (α : Fin n → ι → ℕ) :
    ∫ x, (∑ j, (b (kk α j) * c j) * Pr (P0 α j) x) ^ 2 ∂(γ ι)
      = ∑ v ∈ Finset.univ.image (kk α), b v ^ 2 *
          ∫ x, (∑ j ∈ Finset.univ.filter (fun j => kk α j = v), c j * Pr (P0 α j) x) ^ 2
            ∂(γ ι) := by
  classical
  rw [sq_expand]
  have h2 : ∀ j, ∑ j', b (kk α j) * c j * (b (kk α j') * c j') * Mx α j j'
      = b (kk α j) ^ 2 * ∑ j' ∈ Finset.univ.filter (fun j' => kk α j' = kk α j),
          c j * c j' * Mx α j j' := by
    intro j
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j' => kk α j' = kk α j)]
    have hz : ∑ j' ∈ Finset.univ.filter (fun j' => ¬ kk α j' = kk α j),
        b (kk α j) * c j * (b (kk α j') * c j') * Mx α j j' = 0 :=
      Finset.sum_eq_zero fun j' hj' => by
        rw [Finset.mem_filter] at hj'
        rw [orth α j j' (Ne.symm hj'.2)]; ring
    rw [hz, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' hj' => ?_
    rw [Finset.mem_filter] at hj'
    rw [hj'.2]; ring
  rw [Finset.sum_congr rfl fun j _ => h2 j]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image (kk α))
    (g := kk α) (fun j _ => Finset.mem_image_of_mem _ (Finset.mem_univ j))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [sq_expand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_filter] at hj
  rw [hj.2]

lemma parseval_le (c : Fin n → ℝ) (α : Fin n → ι → ℕ) (d : ℕ) (hk : ∀ j, kk α j ≤ d)
    (T : ℝ) (hT : 0 ≤ T) :
    ∫ x, (∑ j, (c j * Real.exp (kk α j * T)) * Pr (P0 α j) x) ^ 2 ∂(γ ι)
      ≤ Real.exp (d * T) ^ 2 * ∫ x, (∑ j, c j * Pr (P0 α j) x) ^ 2 ∂(γ ι) := by
  classical
  have w1 := weighted (fun v => Real.exp (v * T)) c α
  have w2 := weighted (fun _ => (1:ℝ)) c α
  beta_reduce at w1 w2
  simp only [one_mul] at w2
  have e1 : ∀ x, (∑ j, (c j * Real.exp (kk α j * T)) * Pr (P0 α j) x) ^ 2
      = (∑ j, (Real.exp (kk α j * T) * c j) * Pr (P0 α j) x) ^ 2 := by
    intro x; congr 1; exact Finset.sum_congr rfl fun j _ => by ring
  rw [integral_congr_ae (ae_of_all _ e1), w1, w2, Finset.mul_sum]
  refine Finset.sum_le_sum fun v hv => ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
  have hS : 0 ≤ ∫ x, (∑ j' ∈ Finset.univ.filter (fun j' => kk α j' = kk α j),
      c j' * Pr (P0 α j') x) ^ 2 ∂(γ ι) := integral_nonneg fun x => sq_nonneg _
  have hb : Real.exp (kk α j * T) ^ 2 ≤ Real.exp (d * T) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hk j) hT)) 2
  try simp only [one_pow, one_mul]
  exact mul_le_mul_of_nonneg_right hb hS

end Orth

/-! ### Assembly -/

lemma eLpNorm_bound (g : (ι → ℝ) → ℝ) (hgc : Continuous g) (hgd : Dom g) (q K : ℝ)
    (hq : 2 ≤ q) (hK : 0 ≤ K)
    (h : ∫ x, |g x| ^ q ∂(γ ι) ≤ (K * ∫ x, g x ^ 2 ∂(γ ι)) ^ (q / 2)) :
    eLpNorm g (ENNReal.ofReal q) (γ ι) ≤ ENNReal.ofReal (K ^ (1/2 : ℝ)) * eLpNorm g 2 (γ ι) := by
  have hq0 : 0 < q := by linarith
  have hmem : ∀ p : ℝ, 0 < p → MemLp g (ENNReal.ofReal p) (γ ι) := by
    intro p hp
    rw [← integrable_norm_rpow_iff hgc.aestronglyMeasurable (ENNReal.ofReal_pos.2 hp).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
    simp only [Real.norm_eq_abs]
    exact (dom_abs_rpow hgd hp.le).integrable (hgc.abs.rpow_const fun _ => Or.inr hp.le)
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hA : 0 ≤ ∫ x, g x ^ 2 ∂(γ ι) := integral_nonneg fun x => sq_nonneg _
  rw [h2, (hmem q hq0).eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.2 hq0).ne'
    ENNReal.ofReal_ne_top, (hmem 2 two_pos).eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_pos.2 two_pos).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le, ENNReal.toReal_ofReal zero_le_two,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hK _)]
  apply ENNReal.ofReal_le_ofReal
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  calc (∫ x, |g x| ^ q ∂(γ ι)) ^ q⁻¹
      ≤ ((K * ∫ x, g x ^ 2 ∂(γ ι)) ^ (q / 2)) ^ q⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) h
          (inv_nonneg.2 hq0.le)
    _ = (K * ∫ x, g x ^ 2 ∂(γ ι)) ^ (1/2 : ℝ) := by
        rw [← Real.rpow_mul (mul_nonneg hK hA)]; congr 1; field_simp
    _ = K ^ (1/2 : ℝ) * (∫ x, g x ^ 2 ∂(γ ι)) ^ (2:ℝ)⁻¹ := by
        rw [Real.mul_rpow hK hA]; norm_num

theorem hyper_comb {n : ℕ} (c : Fin n → ℝ) (α : Fin n → ι → ℕ) (d : ℕ)
    (hk : ∀ j, kk α j ≤ d) (q : ℝ) (hq : 2 ≤ q) :
    ∫ x, |∑ j, c j * Pr (P0 α j) x| ^ q ∂(γ ι)
      ≤ ((q - 1) ^ d * ∫ x, (∑ j, c j * Pr (P0 α j) x) ^ 2 ∂(γ ι)) ^ (q / 2) := by
  classical
  set T := Real.log (q - 1) / 2 with hTdef
  have hT : 0 ≤ T := by
    have := Real.log_nonneg (show (1:ℝ) ≤ q - 1 by linarith); positivity
  have hexpT : Real.exp (2 * T) = q - 1 := by
    rw [hTdef, show 2 * (Real.log (q - 1) / 2) = Real.log (q - 1) by ring,
      Real.exp_log (by linarith)]
  have hqT : qf T = q := by unfold qf; rw [hexpT]; ring
  set a : Fin n → ℝ := fun j => c j * Real.exp (kk α j * T) with ha
  have hUT : ∀ x, U a α T x = ∑ j, c j * Pr (P0 α j) x := by
    intro x; unfold U
    refine Finset.sum_congr rfl fun j _ => ?_
    have : kk α j * T + -(kk α j) * T = 0 := by ring
    rw [ha, mul_assoc (c j), ← Real.exp_add, this, Real.exp_zero, mul_one]
  have hU0 : ∀ x, U a α 0 x = ∑ j, (c j * Real.exp (kk α j * T)) * Pr (P0 α j) x := by
    intro x; unfold U
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_zero, Real.exp_zero, mul_one]
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∫ x, |∑ j, c j * Pr (P0 α j) x| ^ q ∂(γ ι)
        ≤ (∫ x, (∑ j, (c j * Real.exp (kk α j * T)) * Pr (P0 α j) x) ^ 2 ∂(γ ι) + ε)
          ^ (q / 2) := by
    intro ε hε hε1
    have := flow_bound (a := a) (α := α) hε hε1 T hT
    simp_rw [hUT, hU0, hqT] at this
    exact this
  set A := ∫ x, (∑ j, (c j * Real.exp (kk α j * T)) * Pr (P0 α j) x) ^ 2 ∂(γ ι) with hA
  have hlim : ∫ x, |∑ j, c j * Pr (P0 α j) x| ^ q ∂(γ ι) ≤ A ^ (q / 2) := by
    have ht : Tendsto (fun ε : ℝ => (A + ε) ^ (q / 2)) (𝓝[>] 0) (𝓝 ((A + 0) ^ (q / 2))) :=
      (((continuous_const.add continuous_id).rpow_const
        fun _ => Or.inr (by linarith)).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [add_zero] at ht
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
    exact hbound ε hε.1 hε.2.le
  have hP := parseval_le c α d hk T hT
  have hd : Real.exp (d * T) ^ 2 = (q - 1) ^ d := by
    rw [← hexpT, ← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hd] at hP
  refine hlim.trans (Real.rpow_le_rpow (integral_nonneg fun x => sq_nonneg _) hP (by linarith))

theorem hyper_finite' (ι : Type) [Fintype ι] (d : ℕ) (g : (ι → ℝ) → ℝ)
    (hg : g ∈ finPolySpan ι d) (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm g (ENNReal.ofReal q) (Measure.pi fun _ : ι => gaussianReal 0 1) ≤
      ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) *
        eLpNorm g 2 (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  obtain ⟨m, f, gg, hsum⟩ := Submodule.mem_span_set'.1 hg
  have hα : ∀ j, ∃ β : ι → ℕ, ∑ i, β i ≤ d ∧
      (gg j : (ι → ℝ) → ℝ) = fun y => ∏ i, hermite (β i) (y i) := fun j => (gg j).2
  choose β hβd hβ using hα
  have hgx : g = fun x => ∑ j, f j * Pr (P0 β j) x := by
    rw [← hsum]; funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hβ, Pr, P0, hermite_eq]
  have hk : ∀ j, kk β j ≤ d := fun j => by unfold kk; exact_mod_cast hβd j
  have hb := hyper_comb f β d hk q hq
  have hc : Continuous fun x => ∑ j, f j * Pr (P0 β j) x :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (Pr_continuous _)
  have hdm : Dom fun x => ∑ j, f j * Pr (P0 β j) x :=
    Dom.sum _ fun j _ => (dom_const _).mul (dom_Pr _)
  have := eLpNorm_bound _ hc hdm q ((q - 1) ^ d) hq (pow_nonneg (by linarith) d) hb
  have e : (((q - 1) ^ d : ℝ)) ^ (1/2 : ℝ) = (q - 1) ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; ring
  rw [e] at this
  rw [hgx]; exact this

end Hyper

/-- Step 1: finite-dimensional Gaussian hypercontractivity (Nelson) for finite linear
combinations of Hermite products of degree ≤ d, via Gross's log-Sobolev argument. -/
lemma hyper_finite (ι : Type) [Fintype ι] (d : ℕ) (g : (ι → ℝ) → ℝ)
    (hg : g ∈ finPolySpan ι d) (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm g (ENNReal.ofReal q) (Measure.pi fun _ : ι => gaussianReal 0 1) ≤
      ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) *
        eLpNorm g 2 (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  Hyper.hyper_finite' ι d g hg q hq

lemma finPolySpan_continuous {ι : Type} [Fintype ι] {d : ℕ} {g : (ι → ℝ) → ℝ}
    (hg : g ∈ finPolySpan ι d) : Continuous g := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, -, rfl⟩ := hg
    exact continuous_finsetProd _ fun i _ =>
      (Polynomial.continuous_aeval (Polynomial.hermite (α i))).comp (continuous_apply i)
  | zero => exact continuous_const
  | add _ _ _ _ h1 h2 => exact h1.add h2
  | smul a _ _ h => exact h.const_smul a

/-- Every element of the algebraic span is, a.e., a finite-coordinate Hermite combination,
for every sufficiently large finite coordinate set. -/
lemma polySpan_repr (d : ℕ) (p : Original) (hp : p ∈ polySpanLE d) :
    ∃ I₀ : Finset ℕ, ∀ I : Finset ℕ, I₀ ⊆ I → ∃ g ∈ finPolySpan I d,
      (p : Sample → ℝ) =ᵐ[gaussianProduct ℕ] fun x => g (I.restrict x) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨α, hα, hpα⟩ := hp
    refine ⟨α.support, fun I hI => ⟨fun y => ∏ i : I, hermite (α i) (y i),
      Submodule.subset_span ⟨fun i => α i, ?_, rfl⟩, hpα.trans (Eventually.of_forall fun x => ?_)⟩⟩
    · calc ∑ i : I, α i = ∑ i ∈ I, α i := Finset.sum_coe_sort I (fun i => α i)
        _ = ∑ i ∈ α.support, α i :=
          (Finset.sum_subset hI (fun i _ hi => by simpa using hi)).symm
        _ = multiDegree α := rfl
        _ ≤ d := hα
    · show heMulti α x = ∏ i : I, hermite (α i) (I.restrict x i)
      simp only [Finset.restrict]
      rw [Finset.prod_coe_sort I (fun i => hermite (α i) (x i))]
      unfold heMulti Finsupp.prod
      exact Finset.prod_subset hI (fun i _ hi => by
        simp [Finsupp.notMem_support_iff.mp hi, hermite])
  | zero =>
    refine ⟨∅, fun I _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := gaussianProduct ℕ)] with x hx
    simp [hx]
  | add p₁ p₂ _ _ ih₁ ih₂ =>
    obtain ⟨I₁, h₁⟩ := ih₁
    obtain ⟨I₂, h₂⟩ := ih₂
    refine ⟨I₁ ∪ I₂, fun I hI => ?_⟩
    obtain ⟨g₁, hg₁, e₁⟩ := h₁ I (Finset.subset_union_left.trans hI)
    obtain ⟨g₂, hg₂, e₂⟩ := h₂ I (Finset.subset_union_right.trans hI)
    refine ⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂, ?_⟩
    filter_upwards [Lp.coeFn_add p₁ p₂, e₁, e₂] with x hx h1 h2
    rw [hx, Pi.add_apply, h1, h2]
    rfl
  | smul a p _ ih =>
    obtain ⟨I₀, h⟩ := ih
    refine ⟨I₀, fun I hI => ?_⟩
    obtain ⟨g, hg, e⟩ := h I hI
    refine ⟨a • g, Submodule.smul_mem _ a hg, ?_⟩
    filter_upwards [Lp.coeFn_smul a p, e] with x hx h1
    rw [hx, Pi.smul_apply, h1]
    rfl

/-- Step 2: transfer to elements of the algebraic span. -/
lemma hyper_polySpan (d : ℕ) (p : Original) (hp : p ∈ polySpanLE d)
    (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm (fun x => p x) (ENNReal.ofReal q) (gaussianProduct ℕ) ≤
      ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) * ENNReal.ofReal ‖p‖ := by
  obtain ⟨I, hI⟩ := polySpan_repr d p hp
  obtain ⟨g, hg, e⟩ := hI I subset_rfl
  have hmap : (gaussianProduct ℕ).map I.restrict = Measure.pi fun _ : I => gaussianReal 0 1 :=
    Measure.infinitePi_map_restrict (fun _ : ℕ => gaussianReal 0 1)
  have hgc := finPolySpan_continuous hg
  have key : ∀ r, eLpNorm (fun x => p x) r (gaussianProduct ℕ) =
      eLpNorm g r (Measure.pi fun _ : I => gaussianReal 0 1) := by
    intro r
    rw [eLpNorm_congr_ae e, ← hmap, eLpNorm_map_measure hgc.aestronglyMeasurable
      (Finset.measurable_restrict I).aemeasurable]
    rfl
  have hn : ENNReal.ofReal ‖p‖ = eLpNorm (fun x => p x) 2 (gaussianProduct ℕ) := by
    rw [ofReal_norm, Lp.enorm_def]
  rw [hn, key, key]
  exact hyper_finite I d g hg q hq

/-- Step 3: closure by Fatou along an a.e. convergent subsequence. -/
lemma hyper_closure (d : ℕ) (p : Original) (hp : p ∈ chaosLE d)
    (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm (fun x => p x) (ENNReal.ofReal q) (gaussianProduct ℕ) ≤
      ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) * ENNReal.ofReal ‖p‖ := by
  have hcl : chaosLE d = (polySpanLE d).topologicalClosure := rfl
  rw [hcl] at hp
  have hp' : p ∈ closure (polySpanLE d : Set Original) := by
    rw [← Submodule.topologicalClosure_coe] at *; exact hp
  rw [mem_closure_iff_seq_limit] at hp'
  clear hp
  obtain ⟨u, hu, hlim⟩ := hp'
  have hq0 : ENNReal.ofReal q ≠ 0 := by
    simpa using (by linarith : (0:ℝ) < q)
  -- convergence in measure, then a.e. along a subsequence
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => (u n : Original) x) (gaussianProduct ℕ) :=
    fun n => (Lp.aestronglyMeasurable (u n))
  have hnorm : Tendsto (fun n => eLpNorm ((fun x => (u n : Original) x) - fun x => p x) 2
      (gaussianProduct ℕ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ‖u n - p‖) atTop (𝓝 0) := by
      simpa [tendsto_iff_norm_sub_tendsto_zero] using hlim
    have h2 : ∀ n, eLpNorm ((fun x => (u n : Original) x) - fun x => p x) 2
        (gaussianProduct ℕ) = ENNReal.ofReal ‖u n - p‖ := by
      intro n
      rw [eLpNorm_congr_ae (Lp.coeFn_sub (u n) p).symm, ← Lp.enorm_def, ← ofReal_norm]
    simp_rw [h2]
    simpa using ENNReal.tendsto_ofReal h1
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2:ℝ≥0∞) ≠ 0) hmeas
    (Lp.aestronglyMeasurable p) hnorm
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hle := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal q)
    (fun k => hmeas (ns k)) (fun x => p x) hae
  have hbound : ∀ k, eLpNorm (fun x => (u (ns k) : Original) x) (ENNReal.ofReal q)
      (gaussianProduct ℕ) ≤ ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) * ENNReal.ofReal ‖u (ns k)‖ :=
    fun k => hyper_polySpan d _ (hu (ns k)) q hq
  have hconv : Tendsto (fun k => ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) *
      ENNReal.ofReal ‖u (ns k)‖) atTop
      (𝓝 (ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) * ENNReal.ofReal ‖p‖)) := by
    have : Tendsto (fun k => ‖u (ns k)‖) atTop (𝓝 ‖p‖) :=
      ((continuous_norm.tendsto p).comp hlim).comp hns.tendsto_atTop
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal this) (Or.inr ENNReal.ofReal_ne_top)
  refine hle.trans ?_
  calc _ ≤ atTop.liminf fun k => ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) * ENNReal.ofReal ‖u (ns k)‖ :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = _ := hconv.liminf_eq

theorem lemma_A_3 (d : ℕ) (p : Original) (hp : p ∈ chaosLE d)
    (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm (fun x => p x) (ENNReal.ofReal q) (gaussianProduct ℕ) ≤
      ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) * ENNReal.ofReal ‖p‖ :=
  hyper_closure d p hp q hq

end GaussPolyReg.Approx

theorem solution (d : ℕ) (p : GaussPolyReg.Approx.Original)
    (hp : p ∈ GaussPolyReg.Approx.chaosLE d) (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm (fun x => p x) (ENNReal.ofReal q) (GaussPolyReg.Approx.gaussianProduct ℕ) ≤
      ENNReal.ofReal ((q-1) ^ ((d : ℝ)/2)) * ENNReal.ofReal ‖p‖ :=
  GaussPolyReg.Approx.lemma_A_3 d p hp q hq
