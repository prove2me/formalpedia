-- Prove2me | solution 1 for GaussianMatrix.approx_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:23:45.766176+00:00
-- url     : https://prove2.me/submissions/6a6e7c4f-fee2-464b-8a13-7b51346f67f8

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix.ApproxMultAux

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

variable {a n : ℕ}

section approx

variable {t : ℕ}

/-- coefficient vector of `Ω ↦ ∑ₖ f k Ω k ℓ` (a linear form in column `ℓ`) -/
def col (f : Fin n → ℝ) (ℓ : Fin t) : Fin n × Fin t → ℝ := fun e => if e.2 = ℓ then f e.1 else 0

lemma L_col (f : Fin n → ℝ) (ℓ : Fin t) (Ω : Fin n → Fin t → ℝ) :
    L (col f ℓ) Ω = ∑ k, f k * Ω k ℓ := by
  simp [L, col, Fintype.sum_prod_type, ite_mul]

lemma ip_col (f g : Fin n → ℝ) (ℓ ℓ' : Fin t) :
    ip (col f ℓ) (col g ℓ') = if ℓ = ℓ' then ∑ k, f k * g k else 0 := by
  by_cases h : ℓ = ℓ'
  · subst h; simp [ip, col, Fintype.sum_prod_type]
  · simp [ip, col, Fintype.sum_prod_type, h]
    intro h'; exact absurd h'.symm h

lemma entry_sq_expand (f g : Fin n → ℝ) (r : ℝ) (Ω : Fin n → Fin t → ℝ) :
    (r * ∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω - ∑ k, f k * g k) ^ 2
      = r ^ 2 * (∑ ℓ, ∑ ℓ', L (col f ℓ) Ω * L (col g ℓ) Ω * L (col f ℓ') Ω * L (col g ℓ') Ω)
        - 2 * r * (∑ k, f k * g k) * (∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω)
        + (∑ k, f k * g k) ^ 2 := by
  have : (∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω) ^ 2
      = ∑ ℓ, ∑ ℓ', L (col f ℓ) Ω * L (col g ℓ) Ω * L (col f ℓ') Ω * L (col g ℓ') Ω := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; ring

lemma integrable_entry_sq (f g : Fin n → ℝ) (r : ℝ) :
    Integrable (fun Ω => (r * ∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω - ∑ k, f k * g k) ^ 2)
      (gaussianMatrix n t) := by
  simp_rw [entry_sq_expand]
  refine ((Integrable.const_mul ?_ _).sub (Integrable.const_mul ?_ _)).add (integrable_const _)
  · exact integrable_finsetSum _ fun ℓ _ => integrable_finsetSum _ fun ℓ' _ => integrable_L4 _ _ _ _
  · exact integrable_finsetSum _ fun ℓ _ => integrable_L2 _ _

lemma integral_entry_sq (ht : 1 ≤ t) (f g : Fin n → ℝ) :
    ∫ Ω, ((1 / (t : ℝ)) * ∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω - ∑ k, f k * g k) ^ 2
        ∂(gaussianMatrix n t)
      = ((∑ k, f k ^ 2) * (∑ k, g k ^ 2) + (∑ k, f k * g k) ^ 2) / t := by
  simp_rw [entry_sq_expand]
  have i4 := integrable_finsetSum (μ := gaussianMatrix n t) Finset.univ fun ℓ _ =>
    integrable_finsetSum Finset.univ fun ℓ' _ =>
      integrable_L4 (col f ℓ) (col g ℓ) (col f ℓ') (col g ℓ')
  have i2 := integrable_finsetSum (μ := gaussianMatrix n t) Finset.univ fun ℓ _ =>
      integrable_L2 (col f ℓ) (col g ℓ)
  rw [integral_add (by exact (i4.const_mul _).sub (i2.const_mul _)) (integrable_const _),
    integral_sub (by exact i4.const_mul _) (by exact i2.const_mul _), integral_const_mul,
    integral_const_mul, integral_finsetSum _ fun ℓ _ => integrable_finsetSum _ fun ℓ' _ => integrable_L4 _ _ _ _,
    integral_finsetSum _ fun ℓ _ => integrable_L2 _ _]
  have h4 : ∀ ℓ : Fin t, ∫ Ω, ∑ ℓ' : Fin t,
      L (col f ℓ) Ω * L (col g ℓ) Ω * L (col f ℓ') Ω * L (col g ℓ') Ω ∂(gaussianMatrix n t)
      = ∑ ℓ' : Fin t, ((∑ k, f k * g k) ^ 2 + (if ℓ = ℓ' then
          (∑ k, f k * f k) * (∑ k, g k * g k) + (∑ k, f k * g k) ^ 2 else 0)) := by
    intro ℓ
    rw [integral_finsetSum _ fun ℓ' _ => integrable_L4 _ _ _ _]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [integral_L4, ip_col, ip_col, ip_col, ip_col, ip_col, ip_col]
    by_cases h : ℓ = ℓ'
    · simp [h, mul_comm (g _) (f _)]; ring
    · simp [h]; ring
  simp_rw [h4, integral_L2, ip_col]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
  have : (t : ℝ) ≠ 0 := by positivity
  field_simp
  simp only [sq]
  ring

variable {b : ℕ}

lemma entryX (M : Matrix (Fin a) (Fin n) ℝ) (N : Matrix (Fin b) (Fin n) ℝ)
    (Ω : Fin n → Fin t → ℝ) (i : Fin a) (j : Fin b) :
    (M * ((1 / (t : ℝ)) • (Matrix.of Ω * (Matrix.of Ω)ᵀ)) * Nᵀ - M * Nᵀ) i j
      = (1 / (t : ℝ)) * ∑ ℓ, L (col (M i) ℓ) Ω * L (col (N j) ℓ) Ω - ∑ k, M i k * N j k := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply,
    Matrix.of_apply, smul_eq_mul, L_col]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ k', ∑ ℓ, ∑ k, M i k * (1 / (t : ℝ) * (Ω k ℓ * Ω k' ℓ)) * N j k' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ ℓ, ∑ k', ∑ k, M i k * (1 / (t : ℝ) * (Ω k ℓ * Ω k' ℓ)) * N j k' := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring

theorem approx_main {a b n t : ℕ} (ht : 1 ≤ t) (M : Matrix (Fin a) (Fin n) ℝ)
    (N : Matrix (Fin b) (Fin n) ℝ) :
    ∫ Ω, frobSq (M * ((1 / (t : ℝ)) • (Matrix.of Ω * (Matrix.of Ω)ᵀ)) * Nᵀ - M * Nᵀ)
        ∂(gaussianMatrix n t)
      = (frobSq M * frobSq N + frobSq (M * Nᵀ)) / t ∧
    (frobSq M * frobSq N + frobSq (M * Nᵀ)) / t ≤ 2 / t * (frobSq M * frobSq N) := by
  have hMN : frobSq (M * Nᵀ) = ∑ i, ∑ j, (∑ k, M i k * N j k) ^ 2 := by
    simp [frobSq, Matrix.mul_apply]
  have hMN' : frobSq M * frobSq N = ∑ i, ∑ j, (∑ k, M i k ^ 2) * (∑ k, N j k ^ 2) := by
    simp only [frobSq, Finset.sum_mul_sum]
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  constructor
  · have hX : ∀ Ω : Fin n → Fin t → ℝ,
        frobSq (M * ((1 / (t : ℝ)) • (Matrix.of Ω * (Matrix.of Ω)ᵀ)) * Nᵀ - M * Nᵀ)
        = ∑ i, ∑ j, ((1 / (t : ℝ)) * ∑ ℓ, L (col (M i) ℓ) Ω * L (col (N j) ℓ) Ω
            - ∑ k, M i k * N j k) ^ 2 := by
      intro Ω; simp only [frobSq, entryX]
    simp_rw [hX]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_entry_sq (M i) (N j) _]
    have hij : ∀ i, ∫ Ω, ∑ j, ((1 / (t : ℝ)) * ∑ ℓ, L (col (M i) ℓ) Ω * L (col (N j) ℓ) Ω
            - ∑ k, M i k * N j k) ^ 2 ∂(gaussianMatrix n t)
        = ∑ j, ((∑ k, M i k ^ 2) * (∑ k, N j k ^ 2) + (∑ k, M i k * N j k) ^ 2) / t := by
      intro i
      rw [integral_finsetSum _ fun j _ => integrable_entry_sq (M i) (N j) _]
      exact Finset.sum_congr rfl fun j _ => integral_entry_sq ht (M i) (N j)
    simp_rw [hij, hMN, hMN', ← Finset.sum_div, ← Finset.sum_add_distrib]
  · have hle : frobSq (M * Nᵀ) ≤ frobSq M * frobSq N := by
      rw [hMN, hMN']
      gcongr with i _ j _
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [show 2 / (t : ℝ) * (frobSq M * frobSq N) = (frobSq M * frobSq N + frobSq M * frobSq N) / t
      by ring]
    gcongr

end approx

end GaussianMatrix.ApproxMultAux

open GaussianMatrix

theorem solution {a b n t : ℕ} (ht : 1 ≤ t) (M : Matrix (Fin a) (Fin n) ℝ)
    (N : Matrix (Fin b) (Fin n) ℝ) :
    ∫ Ω, frobSq (M * ((1 / (t : ℝ)) • (Matrix.of Ω * (Matrix.of Ω)ᵀ)) * Nᵀ - M * Nᵀ)
        ∂(gaussianMatrix n t)
      = (frobSq M * frobSq N + frobSq (M * Nᵀ)) / t ∧
    (frobSq M * frobSq N + frobSq (M * Nᵀ)) / t ≤ 2 / t * (frobSq M * frobSq N) :=
  GaussianMatrix.ApproxMultAux.approx_main ht M N
