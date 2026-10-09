-- Prove2me | solution 1 for GaussianMatrix.frobenius_fourth_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:25:36.646618+00:00
-- url     : https://prove2.me/submissions/96522d7c-98de-476b-bad7-b7a2bc4f29c1

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix.FourthMomentAux

lemma gint (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (k : NNReal)).integrable_norm_pow'
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [norm_pow]

lemma gm1 : ∫ x, x ^ 1 ∂(gaussianReal 0 1) = 0 := by
  simp [integral_id_gaussianReal (μ := 0) (v := 1)]

lemma gm2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero aemeasurable_id (by simp [ integral_id_gaussianReal (μ := 0) (v := 1)])] at h
  simpa using h

lemma gm3 : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = 0 := by
  have h : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = ∫ x, (-x) ^ 3 ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← neg_zero, ← gaussianReal_map_neg (μ := 0) (v := 1)]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have h2 : ∫ x, (-x) ^ 3 ∂(gaussianReal 0 1) = - ∫ x, x ^ 3 ∂(gaussianReal 0 1) := by
    rw [← integral_neg]; congr 1; ext x; ring
  linarith

lemma gm4 : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h1 : ∀ x : ℝ, gaussianPDFReal 0 1 x • x ^ 4
      = (fun y : ℝ => (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))) |x| := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    have e4 : |x| ^ (4:ℝ) = x ^ 4 := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, pow_abs]
      exact abs_of_nonneg (by positivity)
    have e2 : |x| ^ (2:ℝ) = x ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [e4, e2]; ring_nf
  rw [integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_comp_abs (f := fun y : ℝ => (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))),
    integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  have hg : Real.Gamma ((4 + 1) / 2) = 3 / 4 * √Real.pi := by
    have := Real.Gamma_nat_add_one_add_half 1
    norm_num [Nat.doubleFactorial] at this
    rw [show ((4:ℝ) + 1) / 2 = 5 / 2 by norm_num, this]; ring
  rw [hg]
  have hb : (1/2 : ℝ) ^ (-(4 + 1) / 2 : ℝ) = 4 * √2 := by
    rw [show (-(4 + 1) / 2 : ℝ) = -(2 + 1/2) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_add (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, ← Real.sqrt_eq_rpow]
    norm_num
    field_simp
  rw [hb, Real.sqrt_mul (by norm_num)]
  have : (0:ℝ) < √2 := by positivity
  have : (0:ℝ) < √Real.pi := by positivity
  field_simp

/-- `k`-th moment of the standard Gaussian. -/
noncomputable def mom (k : ℕ) : ℝ := ∫ x, x ^ k ∂(gaussianReal 0 1)

@[simp] lemma mom0 : mom 0 = 1 := by simp [mom]
@[simp] lemma mom1 : mom 1 = 0 := gm1
@[simp] lemma mom2 : mom 2 = 1 := gm2
@[simp] lemma mom3 : mom 3 = 0 := gm3
@[simp] lemma mom4 : mom 4 = 3 := gm4

variable {p m : ℕ}

lemma integral_prod_coord (f : Fin p × Fin m → ℝ → ℝ) :
    ∫ G, ∏ e : Fin p × Fin m, f e (G e.1 e.2) ∂(gaussianMatrix p m)
      = ∏ e : Fin p × Fin m, ∫ x, f e x ∂(gaussianReal 0 1) := by
  simp_rw [Fintype.prod_prod_type]
  unfold gaussianMatrix
  rw [integral_fintype_prod_eq_prod (fun (a : Fin p) (g : Fin m → ℝ) => ∏ b, f (a, b) (g b))]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact integral_fintype_prod_eq_prod (fun b x => f (a, b) x)

lemma integrable_prod_coord (f : Fin p × Fin m → ℝ → ℝ)
    (hf : ∀ e, Integrable (f e) (gaussianReal 0 1)) :
    Integrable (fun G : Fin p → Fin m → ℝ => ∏ e : Fin p × Fin m, f e (G e.1 e.2))
      (gaussianMatrix p m) := by
  simp_rw [Fintype.prod_prod_type]
  unfold gaussianMatrix
  exact Integrable.fintype_prod (f := fun (a : Fin p) (g : Fin m → ℝ) => ∏ b, f (a, b) (g b))
    (fun a => Integrable.fintype_prod (fun b => hf (a, b)))

/-- multiplicity count of index `e` among `e1,e2,e3,e4` -/
def cnt4 (e1 e2 e3 e4 e : Fin p × Fin m) : ℕ :=
  (if e1 = e then 1 else 0) + (if e2 = e then 1 else 0) + (if e3 = e then 1 else 0)
    + (if e4 = e then 1 else 0)

lemma mono4 (G : Fin p → Fin m → ℝ) (e1 e2 e3 e4 : Fin p × Fin m) :
    G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2
      = ∏ e, G e.1 e.2 ^ cnt4 e1 e2 e3 e4 e := by
  simp only [cnt4, pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ,
    if_true]

lemma integrable_mono4 (e1 e2 e3 e4 : Fin p × Fin m) :
    Integrable (fun G : Fin p → Fin m → ℝ => G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2)
      (gaussianMatrix p m) := by
  simp_rw [mono4]
  exact integrable_prod_coord (fun e x => x ^ cnt4 e1 e2 e3 e4 e) (fun e => gint _)

lemma prod_mom_cnt4 (e1 e2 e3 e4 : Fin p × Fin m) :
    ∏ e, mom (cnt4 e1 e2 e3 e4 e) = ∏ e ∈ {e1, e2, e3, e4}, mom (cnt4 e1 e2 e3 e4 e) := by
  symm
  refine Finset.prod_subset (Finset.subset_univ _) fun e _ he => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
  obtain ⟨h1, h2, h3, h4⟩ := he
  simp [cnt4, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

lemma isserlis_idx (e1 e2 e3 e4 : Fin p × Fin m) :
    ∫ G, G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2 ∂(gaussianMatrix p m)
      = (if e1 = e2 then 1 else 0) * (if e3 = e4 then 1 else 0)
        + (if e1 = e3 then 1 else 0) * (if e2 = e4 then 1 else 0)
        + (if e1 = e4 then 1 else 0) * (if e2 = e3 then 1 else 0) := by
  simp_rw [mono4]
  rw [integral_prod_coord (fun e x => x ^ cnt4 e1 e2 e3 e4 e)]
  change ∏ e, mom (cnt4 e1 e2 e3 e4 e) = _
  rw [prod_mom_cnt4]
  by_cases h12 : e1 = e2 <;> by_cases h13 : e1 = e3 <;> by_cases h14 : e1 = e4 <;>
    by_cases h23 : e2 = e3 <;> by_cases h24 : e2 = e4 <;> by_cases h34 : e3 = e4 <;>
    subst_vars <;> (simp_all [Finset.prod_insert, cnt4, eq_comm]; try norm_num)

lemma mono2 (G : Fin p → Fin m → ℝ) (e1 e2 : Fin p × Fin m) :
    G e1.1 e1.2 * G e2.1 e2.2
      = ∏ e, G e.1 e.2 ^ ((if e1 = e then 1 else 0) + (if e2 = e then 1 else 0)) := by
  simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ, if_true]

lemma integrable_mono2 (e1 e2 : Fin p × Fin m) :
    Integrable (fun G : Fin p → Fin m → ℝ => G e1.1 e1.2 * G e2.1 e2.2) (gaussianMatrix p m) := by
  simp_rw [mono2]
  exact integrable_prod_coord _ (fun e => gint _)

lemma integral_mono2 (e1 e2 : Fin p × Fin m) :
    ∫ G, G e1.1 e1.2 * G e2.1 e2.2 ∂(gaussianMatrix p m) = if e1 = e2 then 1 else 0 := by
  simp_rw [mono2]
  rw [integral_prod_coord (fun e x => x ^ ((if e1 = e then 1 else 0) + (if e2 = e then 1 else 0)))]
  change ∏ e, mom _ = _
  by_cases h : e1 = e2
  · subst h
    rw [Finset.prod_eq_single e1]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ e1) (by simp [Ne.symm h])

/-- linear form `G ↦ ∑ₑ u e * G e` -/
def L (u : Fin p × Fin m → ℝ) (G : Fin p → Fin m → ℝ) : ℝ := ∑ e, u e * G e.1 e.2

/-- Euclidean inner product of coefficient vectors -/
def ip (u v : Fin p × Fin m → ℝ) : ℝ := ∑ e, u e * v e

lemma L2_expand (u v : Fin p × Fin m → ℝ) (G : Fin p → Fin m → ℝ) :
    L u G * L v G = ∑ e2, ∑ e1, (u e1 * v e2) * (G e1.1 e1.2 * G e2.1 e2.2) := by
  simp only [L, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma L4_expand (u v w z : Fin p × Fin m → ℝ) (G : Fin p → Fin m → ℝ) :
    L u G * L v G * L w G * L z G = ∑ e4, ∑ e3, ∑ e2, ∑ e1, (u e1 * v e2 * w e3 * z e4) *
      (G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2) := by
  simp only [L, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

lemma integrable_L2 (u v : Fin p × Fin m → ℝ) :
    Integrable (fun G => L u G * L v G) (gaussianMatrix p m) := by
  simp_rw [L2_expand]
  exact integrable_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ =>
    (integrable_mono2 e1 e2).const_mul _

lemma integrable_L4 (u v w z : Fin p × Fin m → ℝ) :
    Integrable (fun G => L u G * L v G * L w G * L z G) (gaussianMatrix p m) := by
  simp_rw [L4_expand]
  exact integrable_finsetSum _ fun e4 _ => integrable_finsetSum _ fun e3 _ =>
    integrable_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ =>
    (integrable_mono4 e1 e2 e3 e4).const_mul _

lemma integral_L2 (u v : Fin p × Fin m → ℝ) :
    ∫ G, L u G * L v G ∂(gaussianMatrix p m) = ip u v := by
  simp_rw [L2_expand]
  rw [integral_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ =>
    (integrable_mono2 e1 e2).const_mul _]
  have : ∀ e2, ∫ G, ∑ e1, (u e1 * v e2) * (G e1.1 e1.2 * G e2.1 e2.2) ∂(gaussianMatrix p m)
      = ∑ e1, (u e1 * v e2) * (if e1 = e2 then 1 else 0) := by
    intro e2
    rw [integral_finsetSum _ fun e1 _ => (integrable_mono2 e1 e2).const_mul _]
    exact Finset.sum_congr rfl fun e1 _ => by rw [integral_const_mul, integral_mono2]
  simp_rw [this]
  simp [ip, mul_ite]

lemma integral_L4 (u v w z : Fin p × Fin m → ℝ) :
    ∫ G, L u G * L v G * L w G * L z G ∂(gaussianMatrix p m)
      = ip u v * ip w z + ip u w * ip v z + ip u z * ip v w := by
  simp_rw [L4_expand]
  have hI : ∀ e1 e2 e3 e4 : Fin p × Fin m, Integrable (fun G : Fin p → Fin m → ℝ =>
      (u e1 * v e2 * w e3 * z e4) * (G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2))
      (gaussianMatrix p m) := fun e1 e2 e3 e4 => (integrable_mono4 e1 e2 e3 e4).const_mul _
  rw [integral_finsetSum _ fun e4 _ => integrable_finsetSum _ fun e3 _ =>
    integrable_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ => hI e1 e2 e3 e4]
  have : ∀ e4, ∫ G, ∑ e3, ∑ e2, ∑ e1, (u e1 * v e2 * w e3 * z e4) *
      (G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2) ∂(gaussianMatrix p m)
      = ∑ e3, ∑ e2, ∑ e1, (u e1 * v e2 * w e3 * z e4) *
      ((if e1 = e2 then 1 else 0) * (if e3 = e4 then 1 else 0)
        + (if e1 = e3 then 1 else 0) * (if e2 = e4 then 1 else 0)
        + (if e1 = e4 then 1 else 0) * (if e2 = e3 then 1 else 0)) := by
    intro e4
    rw [integral_finsetSum _ fun e3 _ => integrable_finsetSum _ fun e2 _ =>
      integrable_finsetSum _ fun e1 _ => hI e1 e2 e3 e4]
    refine Finset.sum_congr rfl fun e3 _ => ?_
    rw [integral_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ => hI e1 e2 e3 e4]
    refine Finset.sum_congr rfl fun e2 _ => ?_
    rw [integral_finsetSum _ fun e1 _ => hI e1 e2 e3 e4]
    refine Finset.sum_congr rfl fun e1 _ => ?_
    rw [integral_const_mul, isserlis_idx]
  simp_rw [this]
  simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq']
  simp only [ip, Finset.sum_mul_sum]
  congr 1; congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma gram_swap {ι κ : Type*} [Fintype ι] [Fintype κ] (S : ι → κ → ℝ) :
    ∑ i, ∑ k, (∑ c, S i c * S k c) ^ 2 = ∑ c, ∑ d, (∑ i, S i c * S i d) ^ 2 := by
  simp only [sq, Finset.sum_mul_sum]
  calc _ = ∑ i, ∑ c, ∑ k, ∑ d, S i c * S k c * (S i d * S k d) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ k, ∑ d, S i c * S k c * (S i d * S k d) := Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ d, ∑ k, S i c * S k c * (S i d * S k d) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ i, ∑ k, S i c * S k c * (S i d * S k d) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable {a n : ℕ}

/-- coefficient vector of the entry `(S G T)_{x}` as a linear form in `G` -/
def uST (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) (x : Fin a × Fin n) :
    Fin p × Fin m → ℝ :=
  fun e => S x.1 e.1 * T e.2 x.2

lemma entry_eq (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (G : Fin p → Fin m → ℝ) (i : Fin a) (j : Fin n) :
    (S * Matrix.of G * T) i j = L (uST S T (i, j)) G := by
  simp only [Matrix.mul_apply, Matrix.of_apply, L, uST, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma ip_uST (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) (x y : Fin a × Fin n) :
    ip (uST S T x) (uST S T y) = (∑ c, S x.1 c * S y.1 c) * (∑ b, T b x.2 * T b y.2) := by
  simp only [ip, uST, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma frobSq_sq_eq (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (G : Fin p → Fin m → ℝ) :
    frobSq (S * Matrix.of G * T) ^ 2 = ∑ x : Fin a × Fin n, ∑ y : Fin a × Fin n,
      L (uST S T x) G * L (uST S T x) G * L (uST S T y) G * L (uST S T y) G := by
  have : frobSq (S * Matrix.of G * T) = ∑ x : Fin a × Fin n, L (uST S T x) G ^ 2 := by
    simp only [frobSq, entry_eq, Fintype.sum_prod_type]
  rw [this, sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem fourth_moment_main (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, frobSq (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      = (frobSq S * frobSq T) ^ 2 + 2 * frobSq (Sᵀ * S) * frobSq (T * Tᵀ) := by
  simp_rw [frobSq_sq_eq]
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => integrable_L4 _ _ _ _]
  have h1 : ∀ x : Fin a × Fin n, ∫ G, ∑ y : Fin a × Fin n,
      L (uST S T x) G * L (uST S T x) G * L (uST S T y) G * L (uST S T y) G ∂(gaussianMatrix p m)
      = ∑ y : Fin a × Fin n, (ip (uST S T x) (uST S T x) * ip (uST S T y) (uST S T y)
          + 2 * ip (uST S T x) (uST S T y) ^ 2) := by
    intro x
    rw [integral_finsetSum _ fun y _ => integrable_L4 _ _ _ _]
    exact Finset.sum_congr rfl fun y _ => by rw [integral_L4]; ring
  simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ip_uST]
  have hS : ∑ i, ∑ c, S i c * S i c = frobSq S := by simp [frobSq, sq]
  have hT : ∑ j, ∑ b, T b j * T b j = frobSq T := by
    rw [Finset.sum_comm]; simp [frobSq, sq]
  have hP : ∑ x : Fin a × Fin n, (∑ c, S x.1 c * S x.1 c) * (∑ b, T b x.2 * T b x.2)
      = frobSq S * frobSq T := by
    rw [Fintype.sum_prod_type, ← hS, ← hT, Finset.sum_mul_sum]
  have hS2 : ∑ i, ∑ k, (∑ c, S i c * S k c) ^ 2 = frobSq (Sᵀ * S) := by
    have := gram_swap (fun i c => S i c)
    rw [this]; simp [frobSq, Matrix.mul_apply]
  have hT2 : ∑ j, ∑ l, (∑ b, T b j * T b l) ^ 2 = frobSq (T * Tᵀ) := by
    have := gram_swap (fun j b => T b j)
    rw [this]; simp [frobSq, Matrix.mul_apply]
  have hQ : ∑ x : Fin a × Fin n, ∑ y : Fin a × Fin n,
      ((∑ c, S x.1 c * S y.1 c) * (∑ b, T b x.2 * T b y.2)) ^ 2
      = frobSq (Sᵀ * S) * frobSq (T * Tᵀ) := by
    rw [← hS2, ← hT2]
    simp only [Fintype.sum_prod_type, mul_pow]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  rw [← Finset.sum_mul, hP, hQ]
  ring

end GaussianMatrix.FourthMomentAux

open GaussianMatrix

theorem solution {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, frobSq (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      = (frobSq S * frobSq T) ^ 2 + 2 * frobSq (Sᵀ * S) * frobSq (T * Tᵀ) :=
  GaussianMatrix.FourthMomentAux.fourth_moment_main S T
