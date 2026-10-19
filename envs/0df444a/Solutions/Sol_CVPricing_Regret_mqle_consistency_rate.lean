-- Prove2me | solution 1 for CVPricing.Regret.mqle_consistency_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T16:54:52.071563+00:00
-- url     : https://prove2.me/submissions/13711b97-84eb-495f-9a84-f4a26935c3aa

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP
import Definitions.Def_CVPricing_Regret_Process

set_option autoImplicit false


open Matrix

namespace B38LW

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem dd_nonneg (z : ι → ℝ) : 0 ≤ z ⬝ᵥ z :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i))

theorem dd_eq_zero (z : ι → ℝ) (h : z ⬝ᵥ z = 0) : z = 0 := by
  ext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (z j))).mp h i
    (Finset.mem_univ _)
  simpa using mul_self_eq_zero.mp this

theorem dot_mulVec_symm (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (x y : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

/-- variational upper bound: `2 x⬝θ - θᵀAθ ≤ xᵀA⁻¹x` for symmetric invertible PSD `A`. -/
theorem var_le (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (hdet : IsUnit A.det)
    (hpsd : ∀ z, 0 ≤ z ⬝ᵥ (A *ᵥ z)) (x θ : ι → ℝ) :
    2 * (x ⬝ᵥ θ) - θ ⬝ᵥ (A *ᵥ θ) ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  set y := A⁻¹ *ᵥ x with hy
  have hx : A *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have h1 : x ⬝ᵥ θ = y ⬝ᵥ (A *ᵥ θ) := by
    rw [← hx, dotProduct_comm, dot_mulVec_symm A hA]
  have h2 : x ⬝ᵥ y = y ⬝ᵥ (A *ᵥ y) := by rw [hx, dotProduct_comm]
  have h3 := hpsd (y - θ)
  have e : (y - θ) ⬝ᵥ (A *ᵥ (y - θ)) =
      y ⬝ᵥ (A *ᵥ y) - 2 * (y ⬝ᵥ (A *ᵥ θ)) + θ ⬝ᵥ (A *ᵥ θ) := by
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dot_mulVec_symm A hA θ y]; ring
  rw [h1, h2]; linarith

theorem inv_psd (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (hdet : IsUnit A.det)
    (hpsd : ∀ z, 0 ≤ z ⬝ᵥ (A *ᵥ z)) (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have := var_le A hA hdet hpsd x 0
  simpa using this

/-- Cauchy-Schwarz in the `A`/`A⁻¹` pairing. -/
theorem cs_le (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (hdet : IsUnit A.det)
    (hpos : ∀ z, z ⬝ᵥ z ≤ z ⬝ᵥ (A *ᵥ z)) (x θ : ι → ℝ) :
    (x ⬝ᵥ θ) ^ 2 ≤ (x ⬝ᵥ (A⁻¹ *ᵥ x)) * (θ ⬝ᵥ (A *ᵥ θ)) := by
  have hpsd : ∀ z, 0 ≤ z ⬝ᵥ (A *ᵥ z) := fun z =>
    le_trans (dd_nonneg z) (hpos z)
  set q := θ ⬝ᵥ (A *ᵥ θ) with hq
  set Z := x ⬝ᵥ (A⁻¹ *ᵥ x) with hZ
  have hZ0 : 0 ≤ Z := inv_psd A hA hdet hpsd x
  rcases (hpsd θ).lt_or_eq with hq0 | hq0
  · have hs := var_le A hA hdet hpsd x (((x ⬝ᵥ θ) / q) • θ)
    rw [dotProduct_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, ← hq] at hs
    have : (x ⬝ᵥ θ) ^ 2 / q ≤ Z := by
      have e : 2 * ((x ⬝ᵥ θ) / q * (x ⬝ᵥ θ)) - (x ⬝ᵥ θ) / q * ((x ⬝ᵥ θ) / q * q) =
          (x ⬝ᵥ θ) ^ 2 / q := by field_simp; ring
      linarith
    rwa [div_le_iff₀ hq0] at this
  · have h1 : θ ⬝ᵥ θ ≤ 0 := by linarith [hpos θ, hq, hq0]
    have hθ : θ ⬝ᵥ θ = 0 := le_antisymm h1 (dd_nonneg θ)
    have : θ = 0 := dd_eq_zero θ hθ
    subst this
    have : q = 0 := by rw [hq]; simp
    rw [this]; simp

/-- anti-monotonicity of the inverse quadratic form. -/
theorem inv_anti (A B : Matrix ι ι ℝ) (hA : Aᵀ = A) (hB : Bᵀ = B) (hdA : IsUnit A.det)
    (hdB : IsUnit B.det) (hpsdA : ∀ z, 0 ≤ z ⬝ᵥ (A *ᵥ z)) (hAB : ∀ z, z ⬝ᵥ (A *ᵥ z) ≤ z ⬝ᵥ (B *ᵥ z))
    (x : ι → ℝ) : x ⬝ᵥ (B⁻¹ *ᵥ x) ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  set y := B⁻¹ *ᵥ x with hy
  have hx : B *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdB, Matrix.one_mulVec]
  have h2 : x ⬝ᵥ y = y ⬝ᵥ (B *ᵥ y) := by rw [hx, dotProduct_comm]
  have := var_le A hA hdA hpsdA x y
  have := hAB y
  rw [h2]; linarith

/-- the regularized design matrix `V_t = I + Σ_{i=1}^t g_i g_iᵀ`. -/
noncomputable def Vm (g : ℕ → ι → ℝ) (t : ℕ) : Matrix ι ι ℝ :=
  1 + ∑ i ∈ Finset.Icc 1 t, vecMulVec (g i) (g i)

theorem Vm_zero (g : ℕ → ι → ℝ) : Vm g 0 = 1 := by simp [Vm]

theorem Vm_succ (g : ℕ → ι → ℝ) (t : ℕ) :
    Vm g (t + 1) = Vm g t + vecMulVec (g (t + 1)) (g (t + 1)) := by
  simp only [Vm]
  rw [Finset.sum_Icc_succ_top (by omega)]; abel

theorem quad_vvm (g θ : ι → ℝ) : θ ⬝ᵥ (vecMulVec g g *ᵥ θ) = (g ⬝ᵥ θ) ^ 2 := by
  rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm θ g]; ring

theorem Vm_quad (g : ℕ → ι → ℝ) (t : ℕ) (θ : ι → ℝ) :
    θ ⬝ᵥ (Vm g t *ᵥ θ) = θ ⬝ᵥ θ + ∑ i ∈ Finset.Icc 1 t, (g i ⬝ᵥ θ) ^ 2 := by
  induction t with
  | zero => simp [Vm_zero]
  | succ n ih =>
    rw [Vm_succ, Matrix.add_mulVec, dotProduct_add, ih, quad_vvm,
      Finset.sum_Icc_succ_top (by omega)]; ring

theorem Vm_symm (g : ℕ → ι → ℝ) (t : ℕ) : (Vm g t)ᵀ = Vm g t := by
  induction t with
  | zero => simp [Vm_zero]
  | succ n ih =>
    rw [Vm_succ, Matrix.transpose_add, ih]
    congr 1
    ext i j; simp [vecMulVec, mul_comm]

theorem Vm_ge (g : ℕ → ι → ℝ) (t : ℕ) (z : ι → ℝ) : z ⬝ᵥ z ≤ z ⬝ᵥ (Vm g t *ᵥ z) := by
  rw [Vm_quad]
  have : 0 ≤ ∑ i ∈ Finset.Icc 1 t, (g i ⬝ᵥ z) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem Vm_psd (g : ℕ → ι → ℝ) (t : ℕ) (z : ι → ℝ) : 0 ≤ z ⬝ᵥ (Vm g t *ᵥ z) :=
  le_trans (dd_nonneg z) (Vm_ge g t z)

theorem Vm_unit (g : ℕ → ι → ℝ) (t : ℕ) : IsUnit (Vm g t).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := Vm_ge g t v
  rw [hV, dotProduct_zero] at h1
  have h2 : v ⬝ᵥ v = 0 := le_antisymm h1 (dd_nonneg v)
  exact hv (dd_eq_zero v h2)

theorem Vm_mono (g : ℕ → ι → ℝ) (t : ℕ) (z : ι → ℝ) :
    z ⬝ᵥ (Vm g t *ᵥ z) ≤ z ⬝ᵥ (Vm g (t + 1) *ᵥ z) := by
  rw [Vm_quad, Vm_quad, Finset.sum_Icc_succ_top (by omega)]
  nlinarith [sq_nonneg (g (t + 1) ⬝ᵥ z)]

/-- matrix determinant lemma for a rank-one update. -/
theorem det_rank_one (A : Matrix ι ι ℝ) (hA : IsUnit A.det) (u v : ι → ℝ) :
    (A + vecMulVec u v).det = A.det * (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  rw [vecMulVec_eq Unit, Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit) hA,
    Matrix.det_unique (n := Unit)]
  congr 1
  simp [Matrix.mul_apply, replicateRow, replicateCol, dotProduct, mulVec, Finset.mul_sum]
  simp only [Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-! ### pathwise Lai-Wei recursion -/

noncomputable def mv (η : ℕ → ℝ) (g : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  ∑ i ∈ Finset.Icc 1 t, η i • g i

noncomputable def Zq (η : ℕ → ℝ) (g : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  mv η g t ⬝ᵥ ((Vm g t)⁻¹ *ᵥ mv η g t)

noncomputable def aq (g : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  g t ⬝ᵥ ((Vm g t)⁻¹ *ᵥ g t)

noncomputable def bq (η : ℕ → ℝ) (g : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  g t ⬝ᵥ ((Vm g t)⁻¹ *ᵥ mv η g (t - 1))

theorem mv_zero (η : ℕ → ℝ) (g : ℕ → ι → ℝ) : mv η g 0 = 0 := by simp [mv]

theorem mv_succ (η : ℕ → ℝ) (g : ℕ → ι → ℝ) (t : ℕ) :
    mv η g (t + 1) = mv η g t + η (t + 1) • g (t + 1) := by
  simp only [mv]; rw [Finset.sum_Icc_succ_top (by omega)]

theorem Zq_zero (η : ℕ → ℝ) (g : ℕ → ι → ℝ) : Zq η g 0 = 0 := by simp [Zq, mv_zero]

theorem Zq_nonneg (η : ℕ → ℝ) (g : ℕ → ι → ℝ) (t : ℕ) : 0 ≤ Zq η g t :=
  inv_psd _ (Vm_symm g t) (Vm_unit g t) (Vm_psd g t) _

theorem Vinv_symm (g : ℕ → ι → ℝ) (t : ℕ) : ((Vm g t)⁻¹)ᵀ = (Vm g t)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, Vm_symm]

theorem Zq_succ_le (η : ℕ → ℝ) (g : ℕ → ι → ℝ) (t : ℕ) :
    Zq η g (t + 1) ≤ Zq η g t + 2 * η (t + 1) * bq η g (t + 1) + η (t + 1) ^ 2 * aq g (t + 1) := by
  have hmono : mv η g t ⬝ᵥ ((Vm g (t + 1))⁻¹ *ᵥ mv η g t) ≤ Zq η g t :=
    inv_anti (Vm g t) (Vm g (t + 1)) (Vm_symm g t) (Vm_symm g (t + 1)) (Vm_unit g t)
      (Vm_unit g (t + 1)) (Vm_psd g t) (Vm_mono g t) _
  have hs := dot_mulVec_symm _ (Vinv_symm g (t + 1)) (mv η g t) (g (t + 1))
  have e : Zq η g (t + 1) = mv η g t ⬝ᵥ ((Vm g (t + 1))⁻¹ *ᵥ mv η g t)
      + 2 * η (t + 1) * bq η g (t + 1) + η (t + 1) ^ 2 * aq g (t + 1) := by
    simp only [Zq, bq, aq, mv_succ, Nat.add_sub_cancel]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, hs]
    ring
  rw [e]; linarith

theorem aq_nonneg (g : ℕ → ι → ℝ) (t : ℕ) : 0 ≤ aq g t :=
  inv_psd _ (Vm_symm g t) (Vm_unit g t) (Vm_psd g t) _

theorem one_le_Vm (g : ℕ → ι → ℝ) (t : ℕ) (x : ι → ℝ) :
    x ⬝ᵥ ((Vm g t)⁻¹ *ᵥ x) ≤ x ⬝ᵥ x := by
  have := inv_anti (1 : Matrix ι ι ℝ) (Vm g t) (by simp) (Vm_symm g t) (by simp) (Vm_unit g t)
    (fun z => by simpa using dd_nonneg z) (fun z => by simpa using Vm_ge g t z) x
  simpa using this

theorem aq_le (g : ℕ → ι → ℝ) (t : ℕ) : aq g t ≤ g t ⬝ᵥ g t := one_le_Vm g t _

theorem bq_sq_le (η : ℕ → ℝ) (g : ℕ → ι → ℝ) (t : ℕ) :
    bq η g t ^ 2 ≤ (g t ⬝ᵥ g t) * (mv η g (t - 1) ⬝ᵥ mv η g (t - 1)) := by
  set V := Vm g t
  set m := mv η g (t - 1)
  have hc := cs_le V (Vm_symm g t) (Vm_unit g t) (Vm_ge g t) (g t) (V⁻¹ *ᵥ m)
  have e : (V⁻¹ *ᵥ m) ⬝ᵥ (V *ᵥ (V⁻¹ *ᵥ m)) = m ⬝ᵥ (V⁻¹ *ᵥ m) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Vm_unit g t), Matrix.one_mulVec,
      dotProduct_comm]
  rw [e] at hc
  have h1 := one_le_Vm g t (g t)
  have h2 := one_le_Vm g t m
  have h3 := aq_nonneg g t
  have h4 := inv_psd _ (Vm_symm g t) (Vm_unit g t) (Vm_psd g t) m
  simp only [bq]
  calc (g t ⬝ᵥ (V⁻¹ *ᵥ m)) ^ 2 ≤ (g t ⬝ᵥ (V⁻¹ *ᵥ g t)) * (m ⬝ᵥ (V⁻¹ *ᵥ m)) := hc
    _ ≤ (g t ⬝ᵥ g t) * (m ⬝ᵥ m) := mul_le_mul h1 h2 h4 (dd_nonneg _)

/-- the self-normalized Cauchy-Schwarz bound used downstream. -/
theorem mv_dot_sq_le (η : ℕ → ℝ) (g : ℕ → ι → ℝ) (t : ℕ) (θ : ι → ℝ) :
    (mv η g t ⬝ᵥ θ) ^ 2 ≤ Zq η g t * (θ ⬝ᵥ θ + ∑ i ∈ Finset.Icc 1 t, (g i ⬝ᵥ θ) ^ 2) := by
  rw [← Vm_quad]
  exact cs_le _ (Vm_symm g t) (Vm_unit g t) (Vm_ge g t) _ _

theorem det_Vm_succ (g : ℕ → ι → ℝ) (t : ℕ) :
    (Vm g (t + 1)).det = (Vm g t).det * (1 + g (t + 1) ⬝ᵥ ((Vm g t)⁻¹ *ᵥ g (t + 1))) := by
  rw [Vm_succ, det_rank_one _ (Vm_unit g t)]

theorem det_Vm_pos (g : ℕ → ι → ℝ) (t : ℕ) : 0 < (Vm g t).det := by
  induction t with
  | zero => simp [Vm_zero]
  | succ n ih =>
    rw [det_Vm_succ]
    have := inv_psd _ (Vm_symm g n) (Vm_unit g n) (Vm_psd g n) (g (n + 1))
    positivity

theorem det_Vm_back (g : ℕ → ι → ℝ) (t : ℕ) :
    (Vm g t).det = (Vm g (t + 1)).det * (1 - aq g (t + 1)) := by
  have h := det_rank_one (Vm g (t + 1)) (Vm_unit g (t + 1)) (-g (t + 1)) (g (t + 1))
  have e : Vm g (t + 1) + vecMulVec (-g (t + 1)) (g (t + 1)) = Vm g t := by
    rw [Vm_succ]; ext i j; simp [vecMulVec]
  rw [e] at h
  rw [h, Matrix.mulVec_neg, dotProduct_neg]; simp only [aq]; ring

theorem aq_le_logdet (g : ℕ → ι → ℝ) (t : ℕ) :
    aq g (t + 1) ≤ Real.log (Vm g (t + 1)).det - Real.log (Vm g t).det := by
  have h0 := det_Vm_pos g t
  have h1 := det_Vm_pos g (t + 1)
  have hb := det_Vm_back g t
  have hx : 0 < 1 - aq g (t + 1) := by
    by_contra hc
    push Not at hc
    have : (Vm g t).det ≤ 0 := by rw [hb]; exact mul_nonpos_of_nonneg_of_nonpos h1.le hc
    linarith
  have hl := Real.log_le_sub_one_of_pos hx
  rw [hb, Real.log_mul h1.ne' hx.ne']
  linarith

theorem sum_aq_le_logdet (g : ℕ → ι → ℝ) (N : ℕ) :
    ∑ t ∈ Finset.Icc 1 N, aq g t ≤ Real.log (Vm g N).det := by
  induction N with
  | zero => simp [Vm_zero]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := aq_le_logdet g n
    linarith

theorem det_Vm_le (g : ℕ → ι → ℝ) (G : ℝ) (hG : ∀ i j, |g i j| ≤ G) (N : ℕ) :
    (Vm g N).det ≤ (Fintype.card ι).factorial * (1 + N * G ^ 2) ^ Fintype.card ι := by
  have hent : ∀ j k, |Vm g N j k| ≤ 1 + N * G ^ 2 := by
    intro j k
    have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (hG 0 j)
    simp only [Vm, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply]
    have h1 : |(1 : Matrix ι ι ℝ) j k| ≤ 1 := by
      by_cases hjk : j = k <;> simp [Matrix.one_apply, hjk]
    have h2 : |∑ i ∈ Finset.Icc 1 N, g i j * g i k| ≤ N * G ^ 2 := by
      calc |∑ i ∈ Finset.Icc 1 N, g i j * g i k| ≤ ∑ i ∈ Finset.Icc 1 N, |g i j * g i k| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.Icc 1 N, G ^ 2 := by
            apply Finset.sum_le_sum; intro i _
            rw [abs_mul, sq]
            exact mul_le_mul (hG i j) (hG i k) (abs_nonneg _) hG0
        _ = N * G ^ 2 := by simp
    calc _ ≤ |(1 : Matrix ι ι ℝ) j k| + |∑ i ∈ Finset.Icc 1 N, g i j * g i k| := abs_add_le _ _
      _ ≤ _ := by linarith
  have := Matrix.det_le (abv := AbsoluteValue.abs) hent
  rw [nsmul_eq_mul] at this
  exact le_trans (le_abs_self _) this

theorem Zq_congr (η η' : ℕ → ℝ) (g g' : ℕ → ι → ℝ) (t : ℕ)
    (h : ∀ i ∈ Finset.Icc 1 t, η i = η' i ∧ g i = g' i) : Zq η g t = Zq η' g' t := by
  have hV : Vm g t = Vm g' t := by
    simp only [Vm]; congr 1; exact Finset.sum_congr rfl (fun i hi => by rw [(h i hi).2])
  have hm : mv η g t = mv η' g' t := by
    simp only [mv]; exact Finset.sum_congr rfl (fun i hi => by rw [(h i hi).1, (h i hi).2])
  simp only [Zq, hV, hm]

/-! ### probabilistic Lai-Wei bound -/

section Prob

open MeasureTheory

variable {Ω : Type*}

theorem meas_det {m : MeasurableSpace Ω} (A : Ω → Matrix ι ι ℝ)
    (h : ∀ i j, Measurable[m] (fun ω => A ω i j)) : Measurable[m] (fun ω => (A ω).det) := by
  simp_rw [Matrix.det_apply]
  refine Finset.measurable_sum _ (fun σ _ => ?_)
  have : Measurable[m] (fun ω => ∏ i, A ω (σ i) i) := Finset.measurable_prod _ (fun i _ => h _ _)
  simp_rw [Units.smul_def]
  have e : ∀ x : ℝ, ((Equiv.Perm.sign σ : ℤ) • x) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * x := fun x => by
    rw [zsmul_eq_mul]
  simp_rw [e]
  exact this.const_mul _

theorem meas_inv {m : MeasurableSpace Ω} (A : Ω → Matrix ι ι ℝ)
    (h : ∀ i j, Measurable[m] (fun ω => A ω i j)) (i j : ι) :
    Measurable[m] (fun ω => (A ω)⁻¹ i j) := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_apply]
  refine (meas_det A h).inv.mul (meas_det _ (fun k l => ?_))
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact measurable_const
  · exact h _ _

theorem meas_dot {m : MeasurableSpace Ω} (x y : Ω → ι → ℝ) (hx : ∀ j, Measurable[m] (fun ω => x ω j))
    (hy : ∀ j, Measurable[m] (fun ω => y ω j)) : Measurable[m] (fun ω => x ω ⬝ᵥ y ω) := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ (fun j _ => (hx j).mul (hy j))

theorem meas_mulVec {m : MeasurableSpace Ω} (A : Ω → Matrix ι ι ℝ) (x : Ω → ι → ℝ)
    (hA : ∀ i j, Measurable[m] (fun ω => A ω i j)) (hx : ∀ j, Measurable[m] (fun ω => x ω j))
    (i : ι) : Measurable[m] (fun ω => (A ω *ᵥ x ω) i) := by
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ (fun j _ => (hA i j).mul (hx j))

variable {m0 : MeasurableSpace Ω}

/-- hypotheses of the Lai-Wei bound: martingale differences `η` with conditional variance `≤ Vv`,
predictable weights `g` bounded by `G`. -/
structure LWHyp (P : Measure Ω) (ℱ : Filtration ℕ m0) (η : ℕ → Ω → ℝ) (g : ℕ → Ω → ι → ℝ)
    (Vv G : ℝ) : Prop where
  η_meas : ∀ t, 1 ≤ t → Measurable[ℱ t] (η t)
  η_sq : ∀ t, 1 ≤ t → Integrable (fun ω => η t ω ^ 2) P
  η_mean : ∀ t, 1 ≤ t → P[η t | ℱ (t - 1)] =ᵐ[P] 0
  η_var : ∀ t, 1 ≤ t → P[fun ω => η t ω ^ 2 | ℱ (t - 1)] ≤ᵐ[P] fun _ => Vv
  g_meas : ∀ t, 1 ≤ t → ∀ j, Measurable[ℱ (t - 1)] (fun ω => g t ω j)
  g_bdd : ∀ t ω j, |g t ω j| ≤ G
  Vv_nonneg : 0 ≤ Vv

/-- the dominating submartingale `G_t = Σ_{s ≤ t} (2 η_s b_s + η_s² a_s)`. -/
noncomputable def Gp (η : ℕ → Ω → ℝ) (g : ℕ → Ω → ι → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.Icc 1 t, (2 * η s ω * bq (fun k => η k ω) (fun k => g k ω) s +
    η s ω ^ 2 * aq (fun k => g k ω) s)

theorem Zq_le_Gp (η : ℕ → Ω → ℝ) (g : ℕ → Ω → ι → ℝ) (t : ℕ) (ω : Ω) :
    Zq (fun k => η k ω) (fun k => g k ω) t ≤ Gp η g t ω := by
  induction t with
  | zero => simp [Zq_zero, Gp]
  | succ n ih =>
    have := Zq_succ_le (fun k => η k ω) (fun k => g k ω) n
    simp only [Gp] at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega)]
    linarith

theorem Gp_nonneg (η : ℕ → Ω → ℝ) (g : ℕ → Ω → ι → ℝ) (t : ℕ) (ω : Ω) : 0 ≤ Gp η g t ω :=
  le_trans (Zq_nonneg _ _ t) (Zq_le_Gp η g t ω)

section Meas
variable {P : Measure Ω} {ℱ : Filtration ℕ m0} {η : ℕ → Ω → ℝ} {g : ℕ → Ω → ι → ℝ} {Vv G : ℝ}

theorem Vm_meas (h : LWHyp P ℱ η g Vv G) (k t : ℕ) (ht : t ≤ k + 1) (j l : ι) :
    Measurable[ℱ k] (fun ω => Vm (fun s => g s ω) t j l) := by
  simp only [Vm, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply]
  refine measurable_const.add (Finset.measurable_sum _ (fun i hi => ?_))
  have hi' := Finset.mem_Icc.mp hi
  have hle : ℱ (i - 1) ≤ ℱ k := ℱ.mono (by omega)
  exact ((h.g_meas i hi'.1 j).mono hle le_rfl).mul ((h.g_meas i hi'.1 l).mono hle le_rfl)

theorem mv_meas (h : LWHyp P ℱ η g Vv G) (k t : ℕ) (ht : t ≤ k) (j : ι) :
    Measurable[ℱ k] (fun ω => mv (fun s => η s ω) (fun s => g s ω) t j) := by
  simp only [mv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ (fun i hi => ?_)
  have hi' := Finset.mem_Icc.mp hi
  exact ((h.η_meas i hi'.1).mono (ℱ.mono (by omega)) le_rfl).mul
    ((h.g_meas i hi'.1 j).mono (ℱ.mono (by omega)) le_rfl)

theorem aq_meas (h : LWHyp P ℱ η g Vv G) (t : ℕ) (ht : 1 ≤ t) :
    Measurable[ℱ (t - 1)] (fun ω => aq (fun s => g s ω) t) := by
  simp only [aq]
  refine meas_dot _ _ (h.g_meas t ht) (fun i => meas_mulVec _ _ (fun j l => ?_) (h.g_meas t ht) i)
  exact meas_inv _ (fun a b => Vm_meas h (t - 1) t (by omega) a b) j l

theorem bq_meas (h : LWHyp P ℱ η g Vv G) (t : ℕ) (ht : 1 ≤ t) :
    Measurable[ℱ (t - 1)] (fun ω => bq (fun s => η s ω) (fun s => g s ω) t) := by
  simp only [bq]
  refine meas_dot _ _ (h.g_meas t ht) (fun i => meas_mulVec _ _ (fun j l => ?_)
    (fun j => mv_meas h (t - 1) (t - 1) le_rfl j) i)
  exact meas_inv _ (fun a b => Vm_meas h (t - 1) t (by omega) a b) j l

theorem Gp_meas (h : LWHyp P ℱ η g Vv G) (t : ℕ) : Measurable[ℱ t] (Gp η g t) := by
  have : Gp η g t = fun ω => ∑ s ∈ Finset.Icc 1 t, (2 * η s ω * bq (fun k => η k ω)
      (fun k => g k ω) s + η s ω ^ 2 * aq (fun k => g k ω) s) := rfl
  rw [this]
  refine Finset.measurable_sum _ (fun s hs => ?_)
  have hs' := Finset.mem_Icc.mp hs
  have he := (h.η_meas s hs'.1).mono (ℱ.mono hs'.2) le_rfl
  have hb := (bq_meas h s hs'.1).mono (ℱ.mono (show s - 1 ≤ t by omega)) le_rfl
  have ha := (aq_meas h s hs'.1).mono (ℱ.mono (show s - 1 ≤ t by omega)) le_rfl
  exact ((measurable_const.mul he).mul hb).add ((he.pow_const 2).mul ha)

end Meas

section Integ
variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0} {η : ℕ → Ω → ℝ}
  {g : ℕ → Ω → ι → ℝ} {Vv G : ℝ}

theorem memLp_two_of_sq_le {f F : Ω → ℝ} (hf : AEStronglyMeasurable f P) (hF : Integrable F P)
    (hle : ∀ ω, f ω ^ 2 ≤ F ω) : MemLp f 2 P :=
  (memLp_two_iff_integrable_sq hf).mpr (hF.mono' (hf.pow 2) (ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle ω)))

theorem η_memLp (h : LWHyp P ℱ η g Vv G) (t : ℕ) (ht : 1 ≤ t) : MemLp (η t) 2 P :=
  (memLp_two_iff_integrable_sq ((h.η_meas t ht).mono (ℱ.le t) le_rfl).aestronglyMeasurable).mpr
    (h.η_sq t ht)

theorem g_sq_le (h : LWHyp P ℱ η g Vv G) (t : ℕ) (ω : Ω) (j : ι) : g t ω j ^ 2 ≤ G ^ 2 := by
  have := h.g_bdd t ω j
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2

theorem gg_le (h : LWHyp P ℱ η g Vv G) (t : ℕ) (ω : Ω) :
    g t ω ⬝ᵥ g t ω ≤ Fintype.card ι * G ^ 2 := by
  simp only [dotProduct]
  calc ∑ j, g t ω j * g t ω j ≤ ∑ _j : ι, G ^ 2 :=
        Finset.sum_le_sum (fun j _ => by rw [← sq]; exact g_sq_le h t ω j)
    _ = _ := by simp

theorem mv_memLp (h : LWHyp P ℱ η g Vv G) (t : ℕ) (j : ι) :
    MemLp (fun ω => mv (fun s => η s ω) (fun s => g s ω) t j) 2 P := by
  simp only [mv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine memLp_finsetSum _ (fun i hi => ?_)
  have hi' := Finset.mem_Icc.mp hi
  have hm : Measurable (fun ω => η i ω * g i ω j) :=
    ((h.η_meas i hi'.1).mono (ℱ.le i) le_rfl).mul ((h.g_meas i hi'.1 j).mono (ℱ.le _) le_rfl)
  refine memLp_two_of_sq_le hm.aestronglyMeasurable ((h.η_sq i hi'.1).const_mul (G ^ 2))
    (fun ω => ?_)
  rw [mul_pow, mul_comm (G ^ 2)]
  exact mul_le_mul_of_nonneg_left (g_sq_le h i ω j) (sq_nonneg _)

theorem bq_memLp (h : LWHyp P ℱ η g Vv G) (t : ℕ) (ht : 1 ≤ t) :
    MemLp (fun ω => bq (fun s => η s ω) (fun s => g s ω) t) 2 P := by
  have hm := Measurable.aestronglyMeasurable (μ := P) ((bq_meas h t ht).mono (ℱ.le _) le_rfl)
  have hint : Integrable (fun ω => (Fintype.card ι * G ^ 2) *
      ∑ j, mv (fun s => η s ω) (fun s => g s ω) (t - 1) j ^ 2) P :=
    (integrable_finsetSum _ (fun j _ => (mv_memLp h (t - 1) j).integrable_sq)).const_mul _
  refine memLp_two_of_sq_le hm hint (fun ω => ?_)
  have h1 := bq_sq_le (fun s => η s ω) (fun s => g s ω) t
  have h2 := gg_le h t ω
  have h3 : mv (fun s => η s ω) (fun s => g s ω) (t - 1) ⬝ᵥ mv (fun s => η s ω) (fun s => g s ω) (t - 1)
      = ∑ j, mv (fun s => η s ω) (fun s => g s ω) (t - 1) j ^ 2 := by
    simp only [dotProduct, sq]
  rw [h3] at h1
  have h4 : 0 ≤ ∑ j, mv (fun s => η s ω) (fun s => g s ω) (t - 1) j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 h4)

theorem aq_bdd (h : LWHyp P ℱ η g Vv G) (t : ℕ) (ω : Ω) :
    ‖aq (fun s => g s ω) t‖ ≤ Fintype.card ι * G ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (aq_nonneg _ _)]
  exact le_trans (aq_le _ _) (gg_le h t ω)

theorem int_eb (h : LWHyp P ℱ η g Vv G) (t : ℕ) (ht : 1 ≤ t) :
    Integrable (fun ω => bq (fun s => η s ω) (fun s => g s ω) t * η t ω) P :=
  (bq_memLp h t ht).integrable_mul (η_memLp h t ht)

theorem int_ea (h : LWHyp P ℱ η g Vv G) (t : ℕ) (ht : 1 ≤ t) :
    Integrable (fun ω => aq (fun s => g s ω) t * η t ω ^ 2) P :=
  (h.η_sq t ht).bdd_mul ((aq_meas h t ht).mono (ℱ.le _) le_rfl).aestronglyMeasurable
    (ae_of_all _ (aq_bdd h t))

theorem Gp_int (h : LWHyp P ℱ η g Vv G) (t : ℕ) : Integrable (Gp η g t) P := by
  have : Gp η g t = fun ω => ∑ s ∈ Finset.Icc 1 t, (2 * (bq (fun k => η k ω) (fun k => g k ω) s
      * η s ω) + aq (fun k => g k ω) s * η s ω ^ 2) := by
    funext ω; simp only [Gp]; refine Finset.sum_congr rfl (fun s _ => by ring)
  rw [this]
  refine integrable_finsetSum _ (fun s hs => ?_)
  have hs' := Finset.mem_Icc.mp hs
  exact ((int_eb h s hs'.1).const_mul 2).add (int_ea h s hs'.1)

theorem incr_eq (η : ℕ → Ω → ℝ) (g : ℕ → Ω → ι → ℝ) (i : ℕ) :
    Gp η g (i + 1) - Gp η g i = (2 : ℝ) • (fun ω => bq (fun k => η k ω) (fun k => g k ω) (i + 1)
      * η (i + 1) ω) + (fun ω => aq (fun k => g k ω) (i + 1) * η (i + 1) ω ^ 2) := by
  funext ω
  simp only [Gp, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_Icc_succ_top (by omega)]; ring

theorem condExp_eb (h : LWHyp P ℱ η g Vv G) (i : ℕ) :
    P[fun ω => bq (fun s => η s ω) (fun s => g s ω) (i + 1) * η (i + 1) ω | ℱ i] =ᵐ[P] 0 := by
  have hb := bq_meas h (i + 1) (by omega)
  have hm := h.η_mean (i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hb hm
  have := condExp_mul_of_stronglyMeasurable_left (m := ℱ i) (μ := P) hb.stronglyMeasurable
    (int_eb h (i + 1) (by omega)) (MemLp.integrable one_le_two (η_memLp h (i + 1) (by omega)))
  filter_upwards [this, hm] with ω h1 h2
  rw [show (fun ω => bq (fun s => η s ω) (fun s => g s ω) (i + 1) * η (i + 1) ω) =
    (fun ω => bq (fun s => η s ω) (fun s => g s ω) (i + 1)) * η (i + 1) from rfl, h1]
  simp [h2]

theorem Gp_submart (h : LWHyp P ℱ η g Vv G) : Submartingale (Gp η g) ℱ P := by
  refine submartingale_of_condExp_sub_nonneg_nat (fun t => (Gp_meas h t).stronglyMeasurable)
    (Gp_int h) (fun i => ?_)
  rw [incr_eq]
  have i1 := (int_eb h (i + 1) (by omega)).smul (2 : ℝ)
  have hadd := condExp_add (m := ℱ i) i1 (int_ea h (i + 1) (by omega))
  have hsm := condExp_smul (m := ℱ i) (μ := P) (2 : ℝ)
    (fun ω => bq (fun k => η k ω) (fun k => g k ω) (i + 1) * η (i + 1) ω)
  have h0 := condExp_eb h i
  have hpos := condExp_nonneg (m := ℱ i) (μ := P)
    (f := fun ω => aq (fun k => g k ω) (i + 1) * η (i + 1) ω ^ 2)
    (ae_of_all _ (fun ω => mul_nonneg (aq_nonneg _ _) (sq_nonneg _)))
  filter_upwards [hadd, hsm, h0, hpos] with ω e1 e2 e3 e4
  rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3]
  simpa using e4

/-- the log-determinant bound `log (D! (1 + N G²)^D)`. -/
noncomputable def LB (ι : Type) [Fintype ι] (G : ℝ) (N : ℕ) : ℝ :=
  Real.log ((Fintype.card ι).factorial * (1 + N * G ^ 2) ^ Fintype.card ι)

theorem sum_aq_le_LB (h : LWHyp P ℱ η g Vv G) (N : ℕ) (ω : Ω) :
    ∑ s ∈ Finset.Icc 1 N, aq (fun k => g k ω) s ≤ LB ι G N :=
  le_trans (sum_aq_le_logdet _ N) (Real.log_le_log (det_Vm_pos _ N)
    (det_Vm_le _ G (fun i j => h.g_bdd i ω j) N))

theorem integral_Gp_le (h : LWHyp P ℱ η g Vv G) (N : ℕ) :
    ∫ ω, Gp η g N ω ∂P ≤ Vv * LB ι G N := by
  have e : Gp η g N = fun ω => ∑ s ∈ Finset.Icc 1 N, (2 * (bq (fun k => η k ω) (fun k => g k ω) s
      * η s ω) + aq (fun k => g k ω) s * η s ω ^ 2) := by
    funext ω; simp only [Gp]; refine Finset.sum_congr rfl (fun s _ => by ring)
  have key : ∀ s ∈ Finset.Icc 1 N, ∫ ω, (2 * (bq (fun k => η k ω) (fun k => g k ω) s * η s ω)
      + aq (fun k => g k ω) s * η s ω ^ 2) ∂P ≤ Vv * ∫ ω, aq (fun k => g k ω) s ∂P := by
    intro s hs
    obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by have := (Finset.mem_Icc.mp hs).1; omega⟩
    rw [integral_add ((int_eb h (i + 1) (by omega)).const_mul 2) (int_ea h (i + 1) (by omega)),
      integral_const_mul]
    have h1 : ∫ ω, bq (fun k => η k ω) (fun k => g k ω) (i + 1) * η (i + 1) ω ∂P = 0 := by
      rw [← integral_condExp (m := ℱ i) (ℱ.le i)]
      rw [integral_congr_ae (condExp_eb h i)]; simp
    have ha := aq_meas h (i + 1) (by omega)
    have hv := h.η_var (i + 1) (by omega)
    simp only [Nat.add_sub_cancel] at ha hv
    have hc := condExp_mul_of_stronglyMeasurable_left (m := ℱ i) (μ := P) ha.stronglyMeasurable
      (int_ea h (i + 1) (by omega)) (h.η_sq (i + 1) (by omega))
    have h2 : ∫ ω, aq (fun k => g k ω) (i + 1) * η (i + 1) ω ^ 2 ∂P ≤
        ∫ ω, aq (fun k => g k ω) (i + 1) * Vv ∂P := by
      have hc' : P[fun ω => aq (fun k => g k ω) (i + 1) * η (i + 1) ω ^ 2 | ℱ i] =ᵐ[P]
          fun ω => aq (fun k => g k ω) (i + 1) * P[fun ω => η (i + 1) ω ^ 2 | ℱ i] ω := hc
      rw [← integral_condExp (m := ℱ i) (ℱ.le i)]
      rw [integral_congr_ae hc']
      refine integral_mono_ae ?_ ?_ ?_
      · exact (integrable_condExp).bdd_mul
          ((ha.mono (ℱ.le i) le_rfl).aestronglyMeasurable) (ae_of_all _ (aq_bdd h (i + 1)))
      · exact ((integrable_const (Fintype.card ι * G ^ 2 : ℝ)).mono'
          (Measurable.aestronglyMeasurable (μ := P) (ha.mono (ℱ.le i) le_rfl))
          (ae_of_all _ (aq_bdd h (i + 1)))).mul_const _
      · filter_upwards [hv] with ω hω
        exact mul_le_mul_of_nonneg_left hω (aq_nonneg _ _)
    rw [integral_mul_const] at h2
    rw [h1]; linarith
  have hai : ∀ s ∈ Finset.Icc 1 N, Integrable (fun ω => aq (fun k => g k ω) s) P := by
    intro s hs
    exact (integrable_const (Fintype.card ι * G ^ 2 : ℝ)).mono' (Measurable.aestronglyMeasurable
      (μ := P) ((aq_meas h s (Finset.mem_Icc.mp hs).1).mono (ℱ.le _) le_rfl))
      (ae_of_all _ (aq_bdd h s))
  have hint : ∀ s ∈ Finset.Icc 1 N, Integrable (fun ω => 2 * (bq (fun k => η k ω)
      (fun k => g k ω) s * η s ω) + aq (fun k => g k ω) s * η s ω ^ 2) P := fun s hs =>
    ((int_eb h s (Finset.mem_Icc.mp hs).1).const_mul 2).add (int_ea h s (Finset.mem_Icc.mp hs).1)
  rw [e]
  beta_reduce
  rw [integral_finsetSum _ hint]
  calc _ ≤ ∑ s ∈ Finset.Icc 1 N, Vv * ∫ ω, aq (fun k => g k ω) s ∂P := Finset.sum_le_sum key
    _ = Vv * ∫ ω, ∑ s ∈ Finset.Icc 1 N, aq (fun k => g k ω) s ∂P := by
        rw [← Finset.mul_sum, integral_finsetSum _ hai]
    _ ≤ Vv * ∫ _ω, LB ι G N ∂P := by
        refine mul_le_mul_of_nonneg_left (integral_mono (integrable_finsetSum _ hai)
          (integrable_const _) (fun ω => sum_aq_le_LB h N ω)) h.Vv_nonneg
    _ = Vv * LB ι G N := by simp

/-- Doob's maximal inequality for the dominating submartingale. -/
theorem maximal_Gp (h : LWHyp P ℱ η g Vv G) (N : ℕ) (lam : ℝ) (hl : 0 < lam) :
    P {ω | lam ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => Gp η g k ω)} ≤ ENNReal.ofReal (Vv * LB ι G N / lam) := by
  have hmax := maximal_ineq (Gp_submart h) (fun t ω => Gp_nonneg η g t ω)
    (ε := Real.toNNReal lam) N
  rw [Real.coe_toNNReal _ hl.le] at hmax
  set S := {ω | lam ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => Gp η g k ω)} with hS
  have h1 : ∫ ω in S, Gp η g N ω ∂P ≤ Vv * LB ι G N :=
    le_trans (setIntegral_le_integral (Gp_int h N) (ae_of_all _ (fun ω => Gp_nonneg η g N ω)))
      (integral_Gp_le h N)
  have h2 : ((Real.toNNReal lam : NNReal) : ENNReal) * P S ≤ ENNReal.ofReal (Vv * LB ι G N) :=
    le_trans hmax (ENNReal.ofReal_le_ofReal h1)
  rw [ENNReal.ofReal_div_of_pos hl, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hl))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h2

theorem absc_bound (h : LWHyp P ℱ η g Vv G) : ∀ t, 1 ≤ t → ∀ᵐ ω ∂P, 0 ≤ P[fun ω => |η t ω| | ℱ (t - 1)] ω ∧
      P[fun ω => |η t ω| | ℱ (t - 1)] ω ≤ (1 + Vv) / 2 := by
  intro t ht
  have hia : Integrable (fun ω => |η t ω|) P :=
    (MemLp.integrable one_le_two (η_memLp h t ht)).abs
  have hi2 := h.η_sq t ht
  have h0 := condExp_nonneg (m := ℱ (t - 1)) (μ := P) (f := fun ω => |η t ω|)
    (ae_of_all _ (fun ω => abs_nonneg _))
  have hmono := condExp_mono (m := ℱ (t - 1)) hia ((integrable_const (1 / 2 : ℝ)).add
    (hi2.smul (1 / 2 : ℝ))) (ae_of_all _ (fun ω => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [sq_nonneg (|η t ω| - 1), sq_abs (η t ω)]))
  have hadd := condExp_add (m := ℱ (t - 1)) (integrable_const (1 / 2 : ℝ)) (hi2.smul (1 / 2 : ℝ))
  have hsm := condExp_smul (m := ℱ (t - 1)) (μ := P) (1 / 2 : ℝ) (fun ω => η t ω ^ 2)
  have hc := condExp_const (μ := P) (ℱ.le (t - 1)) (1 / 2 : ℝ)
  filter_upwards [h0, hmono, hadd, hsm, h.η_var t ht] with ω e0 e1 e2 e3 e4
  refine ⟨e0, ?_⟩
  rw [e2, Pi.add_apply, e3, Pi.smul_apply, hc, smul_eq_mul] at e1
  linarith

/-- the centred absolute noise `|η_t| - E[|η_t| | ℱ_{t-1}]` is again an admissible noise. -/
theorem LW_abs {ι' : Type} [Fintype ι'] [DecidableEq ι'] (h : LWHyp P ℱ η g Vv G)
    (g' : ℕ → Ω → ι' → ℝ) (G' : ℝ)
    (hg'm : ∀ t, 1 ≤ t → ∀ j, Measurable[ℱ (t - 1)] (fun ω => g' t ω j))
    (hg'b : ∀ t ω j, |g' t ω j| ≤ G') :
    LWHyp P ℱ (fun t ω => |η t ω| - P[fun ω => |η t ω| | ℱ (t - 1)] ω) g'
      (2 * Vv + 2 * ((1 + Vv) / 2) ^ 2) G' := by
  have hB : ∀ t, 1 ≤ t → ∀ᵐ ω ∂P, 0 ≤ P[fun ω => |η t ω| | ℱ (t - 1)] ω ∧
      P[fun ω => |η t ω| | ℱ (t - 1)] ω ≤ (1 + Vv) / 2 := by
    intro t ht
    have hia : Integrable (fun ω => |η t ω|) P :=
      (MemLp.integrable one_le_two (η_memLp h t ht)).abs
    have hi2 := h.η_sq t ht
    have h0 := condExp_nonneg (m := ℱ (t - 1)) (μ := P) (f := fun ω => |η t ω|)
      (ae_of_all _ (fun ω => abs_nonneg _))
    have hmono := condExp_mono (m := ℱ (t - 1)) hia ((integrable_const (1 / 2 : ℝ)).add
      (hi2.smul (1 / 2 : ℝ))) (ae_of_all _ (fun ω => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [sq_nonneg (|η t ω| - 1), sq_abs (η t ω)]))
    have hadd := condExp_add (m := ℱ (t - 1)) (integrable_const (1 / 2 : ℝ)) (hi2.smul (1 / 2 : ℝ))
    have hsm := condExp_smul (m := ℱ (t - 1)) (μ := P) (1 / 2 : ℝ) (fun ω => η t ω ^ 2)
    have hc := condExp_const (μ := P) (ℱ.le (t - 1)) (1 / 2 : ℝ)
    filter_upwards [h0, hmono, hadd, hsm, h.η_var t ht] with ω e0 e1 e2 e3 e4
    refine ⟨e0, ?_⟩
    rw [e2, Pi.add_apply, e3, Pi.smul_apply, hc, smul_eq_mul] at e1
    linarith
  have hcm : ∀ t, 1 ≤ t → Measurable[ℱ t] (P[fun ω => |η t ω| | ℱ (t - 1)]) := fun t ht =>
    (stronglyMeasurable_condExp (m := ℱ (t - 1)) (μ := P) (f := fun ω => |η t ω|)).measurable.mono
      (ℱ.mono (by omega)) le_rfl
  have hV := h.Vv_nonneg
  have hab : ∀ t, 1 ≤ t → Measurable[ℱ t] (fun ω => |η t ω|) := fun t ht =>
    continuous_abs.measurable.comp (h.η_meas t ht)
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, hg'm, hg'b, by positivity⟩
  · exact (hab t ht).sub (hcm t ht)
  · have hm : AEStronglyMeasurable (fun ω => (|η t ω| - P[fun ω => |η t ω| | ℱ (t - 1)] ω) ^ 2) P :=
      (((hab t ht).sub (hcm t ht)).mono (ℱ.le t) le_rfl).aestronglyMeasurable.pow 2
    refine (((h.η_sq t ht).const_mul 2).add (integrable_const (2 * ((1 + Vv) / 2) ^ 2))).mono' hm ?_
    filter_upwards [hB t ht] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_abs (η t ω), sq_nonneg (|η t ω| + P[fun ω => |η t ω| | ℱ (t - 1)] ω), hω.1, hω.2]
  · have hia : Integrable (fun ω => |η t ω|) P :=
      (MemLp.integrable one_le_two (η_memLp h t ht)).abs
    have hs := condExp_sub (m := ℱ (t - 1)) hia (integrable_condExp (m := ℱ (t - 1)) (μ := P)
      (f := fun ω => |η t ω|))
    have hcc := condExp_of_stronglyMeasurable (ℱ.le (t - 1)) (stronglyMeasurable_condExp
      (m := ℱ (t - 1)) (μ := P) (f := fun ω => |η t ω|)) integrable_condExp
    filter_upwards [hs] with ω e
    have e' : (fun ω => |η t ω| - P[fun ω => |η t ω| | ℱ (t - 1)] ω) =
        (fun ω => |η t ω|) - P[fun ω => |η t ω| | ℱ (t - 1)] := rfl
    rw [e', e, Pi.sub_apply, hcc]; simp
  · have hia : Integrable (fun ω => |η t ω|) P :=
      (MemLp.integrable one_le_two (η_memLp h t ht)).abs
    set c := P[fun ω => |η t ω| | ℱ (t - 1)] with hcdef
    have hmeas : Measurable (fun ω => (|η t ω| - c ω) ^ 2) :=
      (((hab t ht).sub (hcm t ht)).mono (ℱ.le t) le_rfl).pow_const 2
    have i1 : Integrable (fun ω => (|η t ω| - c ω) ^ 2) P := by
      refine (((h.η_sq t ht).const_mul 2).add (integrable_const (2 * ((1 + Vv) / 2) ^ 2))).mono'
        hmeas.aestronglyMeasurable ?_
      filter_upwards [hB t ht] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [Pi.add_apply]
      nlinarith [sq_abs (η t ω), sq_nonneg (|η t ω| + c ω), hω.1, hω.2]
    have i2 : Integrable ((2 : ℝ) • (fun ω => η t ω ^ 2) + fun _ => 2 * ((1 + Vv) / 2) ^ 2) P :=
      ((h.η_sq t ht).smul (2 : ℝ)).add (integrable_const _)
    have hmono := condExp_mono (m := ℱ (t - 1)) i1 i2 (by
      filter_upwards [hB t ht] with ω hω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [sq_abs (η t ω), sq_nonneg (|η t ω| + c ω), hω.1, hω.2])
    have hadd := condExp_add (m := ℱ (t - 1)) ((h.η_sq t ht).smul (2 : ℝ))
      (integrable_const (μ := P) (2 * ((1 + Vv) / 2) ^ 2))
    have hsm := condExp_smul (m := ℱ (t - 1)) (μ := P) (2 : ℝ) (fun ω => η t ω ^ 2)
    have hc := condExp_const (μ := P) (ℱ.le (t - 1)) (2 * ((1 + Vv) / 2) ^ 2)
    filter_upwards [hmono, hadd, hsm, h.η_var t ht] with ω e1 e2 e3 e4
    rw [e2, Pi.add_apply, e3, Pi.smul_apply, hc, smul_eq_mul] at e1
    linarith

end Integ

end Prob

end B38LW


open Polynomial

namespace B38Dec

/-- antiderivative of a real polynomial. -/
noncomputable def antideriv (q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (q.natDegree + 1), C (q.coeff k / (k + 1)) * X ^ (k + 1)

theorem derivative_antideriv (q : ℝ[X]) : derivative (antideriv q) = q := by
  simp only [antideriv, derivative_sum, derivative_C_mul_X_pow]
  conv_rhs => rw [q.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Nat.add_sub_cancel]
  congr 1
  try rw [← C_mul]
  congr 1
  push_cast
  field_simp

theorem hasDerivAt_antideriv (q : ℝ[X]) (y : ℝ) :
    HasDerivAt (fun y => (antideriv q).eval y) (q.eval y) y := by
  have := (antideriv q).hasDerivAt y
  rwa [derivative_antideriv] at this

/-- `ε`-Lipschitz remainder after subtracting a polynomial antiderivative of an approximant of `w'`. -/
theorem lip_remainder (w w' : ℝ → ℝ) (lo hi : ℝ)
    (hw : ∀ y ∈ Set.Icc lo hi, HasDerivAt w (w' y) y) (hw' : ContinuousOn w' (Set.Icc lo hi))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ π : ℝ[X], ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi,
      |(w b - π.eval b) - (w a - π.eval a)| ≤ ε * |b - a| := by
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn lo hi w' hw' ε hε
  refine ⟨antideriv q, fun a ha b hb => ?_⟩
  have hd : ∀ y ∈ Set.Icc lo hi, HasDerivWithinAt (fun y => w y - (antideriv q).eval y)
      (w' y - q.eval y) (Set.Icc lo hi) y := fun y hy =>
    ((hw y hy).sub (hasDerivAt_antideriv q y)).hasDerivWithinAt
  have hb' : ∀ y ∈ Set.Icc lo hi, ‖w' y - q.eval y‖ ≤ ε := fun y hy => by
    rw [Real.norm_eq_abs, abs_sub_comm]; exact (hq y hy).le
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb' (convex_Icc lo hi) ha hb
  simpa [Real.norm_eq_abs] using this

/-- a polynomial expression in `(p, u)` splits as a finite sum `Σ_k θ_k(u) g_k(p)`. -/
theorem poly_repr (π : ℝ[X]) (A B : ℝ) : ∃ (n : ℕ) (θ : ℝ × ℝ → Fin n → ℝ) (g : ℝ → Fin n → ℝ),
    (∀ j, Continuous (fun u => θ u j)) ∧ (∀ j, Continuous (fun p => g p j)) ∧
    ∀ p u, π.eval (A + B * p + (u.1 + u.2 * p)) * (u.1 + u.2 * p) = θ u ⬝ᵥ g p := by
  set Pm : MvPolynomial (Fin 3) ℝ := Polynomial.aeval (MvPolynomial.C A + MvPolynomial.C B *
      MvPolynomial.X 0 + (MvPolynomial.X 1 + MvPolynomial.X 2 * MvPolynomial.X 0)) π *
      (MvPolynomial.X 1 + MvPolynomial.X 2 * MvPolynomial.X 0) with hPm
  have hev : ∀ (p : ℝ) (u : ℝ × ℝ), MvPolynomial.eval ![p, u.1, u.2] Pm =
      π.eval (A + B * p + (u.1 + u.2 * p)) * (u.1 + u.2 * p) := by
    intro p u
    have key : ∀ (x : MvPolynomial (Fin 3) ℝ) (π' : ℝ[X]),
        MvPolynomial.eval ![p, u.1, u.2] (Polynomial.aeval x π') =
          π'.eval (MvPolynomial.eval ![p, u.1, u.2] x) := by
      intro x π'
      induction π' using Polynomial.induction_on with
      | C a => simp
      | add f g hf hg => simp [hf, hg]
      | monomial n a h => simp
    rw [hPm, map_mul, key]
    simp
  set S := Pm.support
  set e := S.equivFin.symm
  refine ⟨S.card, fun u k => MvPolynomial.coeff (e k).1 Pm * u.1 ^ ((e k).1 1) * u.2 ^ ((e k).1 2),
    fun p k => p ^ ((e k).1 0), fun j => by fun_prop, fun j => by fun_prop, fun p u => ?_⟩
  rw [← hev, MvPolynomial.eval_eq, ← Finset.sum_coe_sort S, ← Equiv.sum_comp e]
  simp only [dotProduct]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero])]
  simp [Fin.prod_univ_three]
  ring

/-- MAIN decomposition: `w(x0+Δ)Δ = θ(u)⬝g(p) + O(ε Δ²)` with finitely many continuous pieces. -/
theorem decomp (w w' : ℝ → ℝ) (lo hi A B pl ph : ℝ)
    (hw : ∀ y ∈ Set.Icc lo hi, HasDerivAt w (w' y) y) (hw' : ContinuousOn w' (Set.Icc lo hi))
    (hx0 : ∀ p ∈ Set.Icc pl ph, A + B * p ∈ Set.Icc lo hi) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (θ : ℝ × ℝ → Fin n → ℝ) (g : ℝ → Fin n → ℝ),
      (∀ j, Continuous (fun u => θ u j)) ∧ (∀ j, ContinuousOn (fun p => g p j) (Set.Icc pl ph)) ∧
      ∀ p u, A + B * p ∈ Set.Icc lo hi → A + B * p + (u.1 + u.2 * p) ∈ Set.Icc lo hi →
        |w (A + B * p + (u.1 + u.2 * p)) * (u.1 + u.2 * p) - θ u ⬝ᵥ g p| ≤
          ε * (u.1 + u.2 * p) ^ 2 := by
  obtain ⟨π, hπ⟩ := lip_remainder w w' lo hi hw hw' ε hε
  obtain ⟨n, θ1, g1, hθ1, hg1, hrep⟩ := poly_repr π A B
  set r : ℝ → ℝ := fun y => w y - π.eval y with hr
  have hrc : ContinuousOn r (Set.Icc lo hi) := by
    intro y hy
    exact ((hw y hy).continuousAt.sub (π.continuous.continuousAt)).continuousWithinAt
  have hrx : ContinuousOn (fun p => r (A + B * p)) (Set.Icc pl ph) :=
    hrc.comp (by fun_prop) (fun p hp => hx0 p hp)
  refine ⟨n + 2, fun u => Fin.append (θ1 u) ![u.1, u.2],
    fun p => Fin.append (g1 p) ![r (A + B * p), r (A + B * p) * p], ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]; exact hθ1 i
    · simp only [Fin.append_right]
      fin_cases i <;> simp <;> fun_prop
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]; exact (hg1 i).continuousOn
    · simp only [Fin.append_right]
      fin_cases i
      · simpa using hrx
      · simp; exact hrx.mul continuousOn_id
  · intro p u h0 h1
    have hdot : Fin.append (θ1 u) ![u.1, u.2] ⬝ᵥ Fin.append (g1 p) ![r (A + B * p), r (A + B * p) * p]
        = θ1 u ⬝ᵥ g1 p + r (A + B * p) * (u.1 + u.2 * p) := by
      simp only [dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
    rw [hdot, ← hrep]
    have hl := hπ _ h0 _ h1
    have e : w (A + B * p + (u.1 + u.2 * p)) * (u.1 + u.2 * p) -
        (π.eval (A + B * p + (u.1 + u.2 * p)) * (u.1 + u.2 * p) + r (A + B * p) * (u.1 + u.2 * p))
        = ((w (A + B * p + (u.1 + u.2 * p)) - π.eval (A + B * p + (u.1 + u.2 * p))) -
          (w (A + B * p) - π.eval (A + B * p))) * (u.1 + u.2 * p) := by
      simp only [hr]; ring
    rw [e, abs_mul]
    have e2 : A + B * p + (u.1 + u.2 * p) - (A + B * p) = u.1 + u.2 * p := by ring
    rw [e2] at hl
    calc _ ≤ ε * |u.1 + u.2 * p| * |u.1 + u.2 * p| :=
          mul_le_mul_of_nonneg_right hl (abs_nonneg _)
      _ = ε * (u.1 + u.2 * p) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

end B38Dec


namespace B38M1a
open KeskinZeevi.SufficientConditions CVPricing.Regret

theorem g_cont (M : CVPricing.Regret.Model) (D : ℝ) :
    ContinuousOn (fun y => deriv M.h y / (M.σ ^ 2 * M.v (M.h y)) * (D - M.h y)) (Set.Ioi 0) := by
  have hh : ContDiffOn ℝ 2 M.h (Set.Ioi 0) := M.h_contDiffOn.mono Set.Ioi_subset_Ici_self
  have hd : ContinuousOn (deriv M.h) (Set.Ioi 0) :=
    hh.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc : ContinuousOn M.h (Set.Ioi 0) := hh.continuousOn
  have hvh : ContinuousOn (fun y => M.v (M.h y)) (Set.Ioi 0) :=
    M.v_contDiffOn.continuousOn.comp hc (fun y hy => Set.mem_Ici.mpr (M.h_nonneg y (le_of_lt hy)))
  refine (hd.div (continuousOn_const.mul hvh) ?_).mul (continuousOn_const.sub hc)
  intro y hy
  have hv := M.v_pos (M.h y) (M.h_nonneg y (le_of_lt hy))
  exact (mul_pos (pow_pos M.σ_pos 2) hv).ne'

theorem euclid_eq (a b : ℝ × ℝ) :
    euclidNorm (a - b) = Real.sqrt ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
  simp [euclidNorm]

theorem score_root_of_inward (M : CVPricing.Regret.Model) (p d : ℕ → ℝ) (t : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hdom : ∀ a : ℝ × ℝ, euclidNorm (a - M.a0) ≤ ρ → ∀ i ∈ Finset.Icc 1 t, 0 < a.1 + a.2 * p i)
    (hin : ∀ a : ℝ × ℝ, euclidNorm (a - M.a0) = ρ →
      (qscore M p d t a).1 * (a - M.a0).1 + (qscore M p d t a).2 * (a - M.a0).2 < 0) :
    ∃ a, euclidNorm (a - M.a0) < ρ ∧ IsMQLE M p d t a := by
  set g : ℕ → ℝ → ℝ := fun i y => deriv M.h y / (M.σ ^ 2 * M.v (M.h y)) * (d i - M.h y) with hg
  have gc : ∀ i, ContinuousOn (g i) (Set.Ioi 0) := fun i => g_cont M (d i)
  set y0 : ℕ → ℝ := fun i => M.a0.1 + M.a0.2 * p i with hy0
  have hρ0 : euclidNorm (M.a0 - M.a0) ≤ ρ := by
    rw [euclid_eq]; simp; exact hρ.le
  have y0pos : ∀ i ∈ Finset.Icc 1 t, 0 < y0 i := fun i hi => hdom M.a0 hρ0 i hi
  set G : ℕ → ℝ → ℝ := fun i y => ∫ s in y0 i..y, g i s with hG
  have Gd : ∀ i ∈ Finset.Icc 1 t, ∀ y, 0 < y → HasDerivAt (G i) (g i y) y := by
    intro i hi y hy
    have hsub : Set.uIcc (y0 i) y ⊆ Set.Ioi 0 := by
      intro s hs
      rw [Set.mem_uIcc] at hs
      rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact lt_of_lt_of_le (y0pos i hi) h1
      · exact lt_of_lt_of_le hy h1
    exact intervalIntegral.integral_hasDerivAt_right
      (((gc i).mono hsub).intervalIntegrable)
      ((gc i).stronglyMeasurableAtFilter isOpen_Ioi y hy)
      ((gc i).continuousAt (Ioi_mem_nhds hy))
  set Q : ℝ × ℝ → ℝ := fun a => ∑ i ∈ Finset.Icc 1 t, G i (a.1 + a.2 * p i) with hQ
  set L : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun a => ∑ i ∈ Finset.Icc 1 t,
    g i (a.1 + a.2 * p i) • (ContinuousLinearMap.fst ℝ ℝ ℝ + p i • ContinuousLinearMap.snd ℝ ℝ ℝ)
    with hL
  have Qd : ∀ a : ℝ × ℝ, (∀ i ∈ Finset.Icc 1 t, 0 < a.1 + a.2 * p i) → HasFDerivAt Q (L a) a := by
    intro a ha
    apply HasFDerivAt.fun_sum
    intro i hi
    have hx : HasFDerivAt (fun a : ℝ × ℝ => a.1 + a.2 * p i)
        (ContinuousLinearMap.fst ℝ ℝ ℝ + p i • ContinuousLinearMap.snd ℝ ℝ ℝ) a :=
      hasFDerivAt_fst.add (hasFDerivAt_snd.mul_const (p i))
    exact (Gd i hi _ (ha i hi)).comp_hasFDerivAt a hx
  have Lapp : ∀ a v, L a v = (qscore M p d t a).1 * v.1 + (qscore M p d t a).2 * v.2 := by
    intro a v
    simp only [hL, qscore, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, Prod.fst_sum,
      Prod.snd_sum, hg]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  set K : Set (ℝ × ℝ) := {a | (a.1 - M.a0.1) ^ 2 + (a.2 - M.a0.2) ^ 2 ≤ ρ ^ 2} with hK
  have memK : ∀ a, a ∈ K ↔ euclidNorm (a - M.a0) ≤ ρ := by
    intro a
    rw [euclid_eq, Real.sqrt_le_left hρ.le]
    · rfl
  have Kdom : ∀ a ∈ K, ∀ i ∈ Finset.Icc 1 t, 0 < a.1 + a.2 * p i :=
    fun a ha => hdom a ((memK a).mp ha)
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_le (by fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := M.a0) (r := ρ)).subset ?_
      intro a ha
      simp only [hK, Set.mem_setOf_eq] at ha
      rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have h1 : (a.1 - M.a0.1) ^ 2 ≤ ρ ^ 2 := by nlinarith [sq_nonneg (a.2 - M.a0.2)]
      have h2 : (a.2 - M.a0.2) ^ 2 ≤ ρ ^ 2 := by nlinarith [sq_nonneg (a.1 - M.a0.1)]
      exact max_le (abs_le.mpr ⟨by nlinarith, by nlinarith⟩) (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
  have hQc : ContinuousOn Q K := fun a ha =>
    (Qd a (Kdom a ha)).continuousAt.continuousWithinAt
  have a0K : M.a0 ∈ K := by simp [hK]; positivity
  obtain ⟨a, haK, hmax⟩ := hKc.exists_isMaxOn ⟨M.a0, a0K⟩ hQc
  have hdomA := Kdom a haK
  have haK' : (a.1 - M.a0.1) ^ 2 + (a.2 - M.a0.2) ^ 2 ≤ ρ ^ 2 := haK
  rcases lt_or_eq_of_le haK' with hlt | heq
  · have hnhds : K ∈ nhds a := by
      have hopen : IsOpen {b : ℝ × ℝ | (b.1 - M.a0.1) ^ 2 + (b.2 - M.a0.2) ^ 2 < ρ ^ 2} :=
        isOpen_lt (by fun_prop) continuous_const
      exact Filter.mem_of_superset (hopen.mem_nhds hlt) (fun b hb => by simp only [hK, Set.mem_setOf_eq]; exact le_of_lt hb)
    have h0 := (hmax.isLocalMax hnhds).hasFDerivAt_eq_zero (Qd a hdomA)
    have e1 := Lapp a (1, 0)
    have e2 := Lapp a (0, 1)
    rw [h0] at e1 e2
    simp at e1 e2
    refine ⟨a, ?_, fun i hi => le_of_lt (hdomA i hi), ?_⟩
    · rw [euclid_eq, Real.sqrt_lt' hρ]; exact hlt
    · exact Prod.ext e1.symm e2.symm
  · exfalso
    have hnorm : euclidNorm (a - M.a0) = ρ := by
      rw [euclid_eq, heq, Real.sqrt_sq hρ.le]
    have hseg : segment ℝ a M.a0 ⊆ K := by
      rw [segment_eq_image']
      rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
      simp only [hK, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      have : (a.1 + θ * (M.a0.1 - a.1) - M.a0.1) ^ 2 + (a.2 + θ * (M.a0.2 - a.2) - M.a0.2) ^ 2
          = (1 - θ) ^ 2 * ((a.1 - M.a0.1) ^ 2 + (a.2 - M.a0.2) ^ 2) := by ring
      rw [this, heq]
      have : (1 - θ) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg ρ]
    have hcone := sub_mem_posTangentConeAt_of_segment_subset hseg
    have hle := hmax.localize.hasFDerivWithinAt_nonpos (Qd a hdomA).hasFDerivWithinAt hcone
    rw [Lapp] at hle
    have hlt := hin a hnorm
    simp only [Prod.fst_sub, Prod.snd_sub] at hle hlt
    linarith

end B38M1a



namespace B38M1b
open KeskinZeevi.SufficientConditions CVPricing.Regret

theorem w_cont (M : CVPricing.Regret.Model) :
    ContinuousOn (fun y => deriv M.h y / (M.σ ^ 2 * M.v (M.h y))) (Set.Ioi 0) := by
  have hh : ContDiffOn ℝ 2 M.h (Set.Ioi 0) := M.h_contDiffOn.mono Set.Ioi_subset_Ici_self
  have hd : ContinuousOn (deriv M.h) (Set.Ioi 0) :=
    hh.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc : ContinuousOn M.h (Set.Ioi 0) := hh.continuousOn
  have hvh : ContinuousOn (fun y => M.v (M.h y)) (Set.Ioi 0) :=
    M.v_contDiffOn.continuousOn.comp hc (fun y hy => Set.mem_Ici.mpr (M.h_nonneg y (le_of_lt hy)))
  refine hd.div (continuousOn_const.mul hvh) ?_
  intro y hy
  have hv := M.v_pos (M.h y) (M.h_nonneg y (le_of_lt hy))
  exact (mul_pos (pow_pos M.σ_pos 2) hv).ne'

theorem w_pos (M : CVPricing.Regret.Model) (y : ℝ) (hy : 0 ≤ y) :
    0 < deriv M.h y / (M.σ ^ 2 * M.v (M.h y)) :=
  div_pos (M.deriv_h_pos y hy) (mul_pos (pow_pos M.σ_pos 2) (M.v_pos _ (M.h_nonneg y hy)))

/-- a continuous positive function has a positive lower bound on a nonempty compact interval. -/
theorem pos_min (f : ℝ → ℝ) (lo hi : ℝ) (hle : lo ≤ hi) (hf : ContinuousOn f (Set.Icc lo hi))
    (hpos : ∀ y ∈ Set.Icc lo hi, 0 < f y) : ∃ m, 0 < m ∧ ∀ y ∈ Set.Icc lo hi, m ≤ f y := by
  obtain ⟨y0, hy0, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨lo, Set.left_mem_Icc.mpr hle⟩ hf
  exact ⟨f y0, hpos y0 hy0, fun y hy => hmin hy⟩

theorem euclid_le (u : ℝ × ℝ) (r : ℝ) (h : euclidNorm u ≤ r) : |u.1| ≤ r ∧ |u.2| ≤ r := by
  unfold euclidNorm at h
  have h1 : Real.sqrt (u.1 ^ 2) ≤ r :=
    le_trans (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u.2])) h
  have h2 : Real.sqrt (u.2 ^ 2) ≤ r :=
    le_trans (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u.1])) h
  rw [Real.sqrt_sq_eq_abs] at h1 h2
  exact ⟨h1, h2⟩

theorem drift_bound (M : CVPricing.Regret.Model) :
    ∃ ρd : ℝ, 0 < ρd ∧ ∃ m : ℝ, 0 < m ∧ ∀ (p d : ℕ → ℝ) (t : ℕ),
      (∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc M.pl M.ph) → ∀ a : ℝ × ℝ, euclidNorm (a - M.a0) ≤ ρd →
      (∀ q ∈ Set.Icc M.pl M.ph, 0 < a.1 + a.2 * q) ∧
      (qscore M p d t a).1 * (a - M.a0).1 + (qscore M p d t a).2 * (a - M.a0).2 ≤
        ∑ i ∈ Finset.Icc 1 t, deriv M.h (a.1 + a.2 * p i) / (M.σ ^ 2 * M.v (M.h (a.1 + a.2 * p i)))
            * (d i - M.h (M.a0.1 + M.a0.2 * p i)) * ((a - M.a0).1 + (a - M.a0).2 * p i)
          - m * ∑ i ∈ Finset.Icc 1 t, ((a - M.a0).1 + (a - M.a0).2 * p i) ^ 2 := by
  set δ0 := M.a0.1 + M.a0.2 * M.ph with hδ0
  have hδ : 0 < δ0 := M.a0_ph_pos
  have hpl := M.pl_pos
  have hph : 0 < M.ph := lt_trans M.pl_pos M.pl_lt_ph
  have hB : 0 < 1 + M.ph := by linarith
  set ρd := δ0 / (2 * (1 + M.ph)) with hρd
  have hρ : 0 < ρd := by positivity
  have hρB : ρd * (1 + M.ph) = δ0 / 2 := by rw [hρd]; field_simp
  set X := M.a0.1 + ρd * (1 + M.ph) with hX
  have hlo : δ0 / 2 ≤ X := by
    have : δ0 ≤ M.a0.1 := by have := M.a01_neg; nlinarith
    rw [hX, hρB]; linarith
  -- every relevant linear predictor lies in I = [δ0/2, X]
  have hrange : ∀ a : ℝ × ℝ, euclidNorm (a - M.a0) ≤ ρd → ∀ q ∈ Set.Icc M.pl M.ph,
      a.1 + a.2 * q ∈ Set.Icc (δ0 / 2) X := by
    intro a ha q hq
    obtain ⟨h1, h2⟩ := euclid_le _ _ ha
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
    obtain ⟨hq1, hq2⟩ := hq
    have hq0 : 0 < q := lt_of_lt_of_le hpl hq1
    have e1 := abs_le.mp h1
    have e2 := abs_le.mp h2
    have hneg := M.a01_neg
    have k1 : M.a0.2 * M.ph ≤ M.a0.2 * q := by nlinarith
    have k2 : -(ρd * q) ≤ (a.2 - M.a0.2) * q := by nlinarith
    have k3 : (a.2 - M.a0.2) * q ≤ ρd * q := by nlinarith
    have k4 : ρd * q ≤ ρd * M.ph := by nlinarith
    have k5 : M.a0.2 * q ≤ 0 := by nlinarith
    constructor
    · have : a.1 + a.2 * q = (M.a0.1 + M.a0.2 * q) + (a.1 - M.a0.1) + (a.2 - M.a0.2) * q := by ring
      rw [this]; nlinarith
    · have : a.1 + a.2 * q = (M.a0.1 + M.a0.2 * q) + (a.1 - M.a0.1) + (a.2 - M.a0.2) * q := by ring
      rw [this, hX]; nlinarith
  have hI0 : Set.Icc (δ0 / 2) X ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le (by positivity) hy.1
  obtain ⟨wm, hwm, hwmin⟩ := pos_min (fun y => deriv M.h y / (M.σ ^ 2 * M.v (M.h y))) _ _ hlo
    ((w_cont M).mono hI0) (fun y hy => w_pos M y (le_of_lt (hI0 hy)))
  have hh : ContDiffOn ℝ 2 M.h (Set.Ioi 0) := M.h_contDiffOn.mono Set.Ioi_subset_Ici_self
  have hdc : ContinuousOn (deriv M.h) (Set.Ioi 0) :=
    hh.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  obtain ⟨hm, hhm, hhmin⟩ := pos_min (deriv M.h) _ _ hlo (hdc.mono hI0)
    (fun y hy => M.deriv_h_pos y (le_of_lt (hI0 hy)))
  have hdiff : DifferentiableOn ℝ M.h (Set.Ioi 0) :=
    hh.differentiableOn (by norm_num)
  -- k(y) = h y - hm * y is monotone on I
  have hmono : MonotoneOn (fun y => M.h y - hm * y) (Set.Icc (δ0 / 2) X) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact ((hdiff.mono hI0).continuousOn).sub (continuousOn_const.mul continuousOn_id)
    · rw [interior_Icc]
      exact ((hdiff.mono (Set.Ioo_subset_Icc_self.trans hI0))).sub
        ((differentiableOn_id).const_mul hm)
    · intro y hy
      rw [interior_Icc] at hy
      have hy0 : 0 < y := hI0 (Set.Ioo_subset_Icc_self hy)
      have hdy : DifferentiableAt ℝ M.h y := hdiff.differentiableAt (Ioi_mem_nhds hy0)
      have hD : HasDerivAt (fun y => M.h y - hm * y) (deriv M.h y - hm * 1) y :=
        hdy.hasDerivAt.sub ((hasDerivAt_id' y).const_mul hm)
      rw [hD.deriv]
      linarith [hhmin y (Set.Ioo_subset_Icc_self hy)]
  have key : ∀ x x0 : ℝ, x ∈ Set.Icc (δ0 / 2) X → x0 ∈ Set.Icc (δ0 / 2) X →
      hm * (x - x0) ^ 2 ≤ (M.h x - M.h x0) * (x - x0) := by
    intro x x0 hx hx0
    rcases le_total x x0 with hle | hle
    · have := hmono hx hx0 hle
      simp only at this
      nlinarith
    · have := hmono hx0 hx hle
      simp only at this
      nlinarith
  refine ⟨ρd, hρ, wm * hm, mul_pos hwm hhm, ?_⟩
  intro p d t hp a ha
  have hdom : ∀ q ∈ Set.Icc M.pl M.ph, 0 < a.1 + a.2 * q :=
    fun q hq => lt_of_lt_of_le (by positivity) (hrange a ha q hq).1
  refine ⟨hdom, ?_⟩
  have ha0 : euclidNorm (M.a0 - M.a0) ≤ ρd := by simp [euclidNorm]; exact hρ.le
  simp only [qscore, Prod.fst_sum, Prod.snd_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  set x := a.1 + a.2 * p i
  set x0 := M.a0.1 + M.a0.2 * p i
  have hxI := hrange a ha (p i) (hp i hi)
  have hx0I := hrange M.a0 ha0 (p i) (hp i hi)
  have hΔ : (a - M.a0).1 + (a - M.a0).2 * p i = x - x0 := by
    simp only [Prod.fst_sub, Prod.snd_sub, x, x0]; ring
  rw [hΔ]
  set w := deriv M.h x / (M.σ ^ 2 * M.v (M.h x))
  have hw : wm ≤ w := hwmin x hxI
  have hk := key x x0 hxI hx0I
  have hsq : 0 ≤ hm * (x - x0) ^ 2 := by positivity
  have h1 : wm * (hm * (x - x0) ^ 2) ≤ w * ((M.h x - M.h x0) * (x - x0)) :=
    mul_le_mul hw hk hsq (le_trans hwm.le hw)
  have e : w * (d i - M.h x) * (a - M.a0).1 + w * (d i - M.h x) * (a - M.a0).2 * p i
      = w * (d i - M.h x0) * (x - x0) - w * ((M.h x - M.h x0) * (x - x0)) := by
    have : (a - M.a0).1 + (a - M.a0).2 * p i = x - x0 := hΔ
    linear_combination (w * (d i - M.h x)) * this
  linarith

end B38M1b



namespace B38M1d
open KeskinZeevi.SufficientConditions Matrix

theorem quad_eq (p : ℕ → ℝ) (t : ℕ) (y : Fin 2 → ℝ) :
    y ⬝ᵥ (fisherOf p t *ᵥ y) = ∑ i ∈ Finset.Icc 1 t, (y 0 + y 1 * p i) ^ 2 := by
  unfold fisherOf
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- `Σ (u₁ + u₂ p_i)² ≥ λ_min(P_t) ‖u‖²`. -/
theorem quad_ge_minRayleigh (p : ℕ → ℝ) (t : ℕ) (u : ℝ × ℝ) :
    minRayleigh (fisherOf p t) * (u.1 ^ 2 + u.2 ^ 2) ≤
      ∑ i ∈ Finset.Icc 1 t, (u.1 + u.2 * p i) ^ 2 := by
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg u.1) (sq_nonneg u.2)) with h0 | hpos
  · rw [← h0, mul_zero]; positivity
  set n := Real.sqrt (u.1 ^ 2 + u.2 ^ 2) with hn
  have hnpos : 0 < n := Real.sqrt_pos.mpr hpos
  have hn2 : n ^ 2 = u.1 ^ 2 + u.2 ^ 2 := Real.sq_sqrt hpos.le
  let y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1} :=
    ⟨![u.1 / n, u.2 / n], by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, div_pow, ← add_div, ← hn2]
      field_simp⟩
  have hbdd : BddBelow (Set.range fun y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1} =>
      y.1 ⬝ᵥ (fisherOf p t *ᵥ y.1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    show 0 ≤ z.1 ⬝ᵥ (fisherOf p t *ᵥ z.1)
    rw [quad_eq]; positivity
  have hle : minRayleigh (fisherOf p t) ≤ y.1 ⬝ᵥ (fisherOf p t *ᵥ y.1) := ciInf_le hbdd y
  rw [quad_eq] at hle
  have hy : ∑ i ∈ Finset.Icc 1 t, (y.1 0 + y.1 1 * p i) ^ 2 =
      (∑ i ∈ Finset.Icc 1 t, (u.1 + u.2 * p i) ^ 2) / (u.1 ^ 2 + u.2 ^ 2) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [y, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hn2]
    field_simp
  rw [hy, le_div_iff₀ hpos] at hle
  exact hle

end B38M1d


namespace B38M1det
open KeskinZeevi.SufficientConditions CVPricing.Regret

/-- Deterministic core of MSCR existence: if the noise term is dominated on the sphere by the
drift `m λ_min(P_t) ρ²`, an MQLE exists strictly inside the ball. -/
theorem root_of_small_noise (M : CVPricing.Regret.Model) :
    ∃ ρd : ℝ, 0 < ρd ∧ ∃ m : ℝ, 0 < m ∧ ∀ (p d : ℕ → ℝ) (t : ℕ),
      (∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc M.pl M.ph) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρd →
      (∀ a : ℝ × ℝ, euclidNorm (a - M.a0) = ρ →
        |∑ i ∈ Finset.Icc 1 t, deriv M.h (a.1 + a.2 * p i) / (M.σ ^ 2 * M.v (M.h (a.1 + a.2 * p i)))
            * (d i - M.h (M.a0.1 + M.a0.2 * p i)) * ((a - M.a0).1 + (a - M.a0).2 * p i)|
          < m * minRayleigh (fisherOf p t) * ρ ^ 2) →
      ∃ a, euclidNorm (a - M.a0) < ρ ∧ IsMQLE M p d t a := by
  obtain ⟨ρd, hρd, m, hm, hdrift⟩ := B38M1b.drift_bound M
  refine ⟨ρd, hρd, m, hm, ?_⟩
  intro p d t hp ρ hρ hρle hsmall
  apply B38M1a.score_root_of_inward M p d t ρ hρ
  · intro a ha i hi
    exact (hdrift p d t hp a (le_trans ha hρle)).1 (p i) (hp i hi)
  · intro a ha
    have hD := (hdrift p d t hp a (le_trans ha.le hρle)).2
    have hS := hsmall a ha
    have hq := B38M1d.quad_ge_minRayleigh p t (a - M.a0)
    have hn : (a - M.a0).1 ^ 2 + (a - M.a0).2 ^ 2 = ρ ^ 2 := by
      have h0 : 0 ≤ (a - M.a0).1 ^ 2 + (a - M.a0).2 ^ 2 := by positivity
      unfold euclidNorm at ha
      rw [← ha, Real.sq_sqrt h0]
    rw [hn] at hq
    have hq' := mul_le_mul_of_nonneg_left hq hm.le
    have hab := le_abs_self (∑ i ∈ Finset.Icc 1 t, deriv M.h (a.1 + a.2 * p i) /
      (M.σ ^ 2 * M.v (M.h (a.1 + a.2 * p i))) * (d i - M.h (M.a0.1 + M.a0.2 * p i)) *
      ((a - M.a0).1 + (a - M.a0).2 * p i))
    nlinarith

end B38M1det

namespace B38App

open KeskinZeevi.SufficientConditions CVPricing.Regret Matrix

noncomputable def W (M : CVPricing.Regret.Model) (y : ℝ) : ℝ :=
  deriv M.h y / (M.σ ^ 2 * M.v (M.h y))

theorem W_contDiffOn (M : CVPricing.Regret.Model) : ContDiffOn ℝ 1 (W M) (Set.Ioi 0) := by
  have hh : ContDiffOn ℝ 2 M.h (Set.Ioi 0) := M.h_contDiffOn.mono Set.Ioi_subset_Ici_self
  have hd : ContDiffOn ℝ 1 (deriv M.h) (Set.Ioi 0) := hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hvh : ContDiffOn ℝ 2 (fun y => M.v (M.h y)) (Set.Ioi 0) :=
    M.v_contDiffOn.comp hh (fun y hy => Set.mem_Ici.mpr (M.h_nonneg y (le_of_lt hy)))
  refine hd.div ((contDiffOn_const.mul hvh).of_le (by norm_num)) (fun y hy => ?_)
  exact (mul_pos (pow_pos M.σ_pos 2) (M.v_pos _ (M.h_nonneg y (le_of_lt hy)))).ne'

theorem W_hasDeriv (M : CVPricing.Regret.Model) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (W M) (deriv (W M) y) y :=
  (((W_contDiffOn M).differentiableOn (by norm_num) y hy).differentiableAt
    (isOpen_Ioi.mem_nhds hy)).hasDerivAt

theorem W_deriv_cont (M : CVPricing.Regret.Model) : ContinuousOn (deriv (W M)) (Set.Ioi 0) :=
  (W_contDiffOn M).continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl

theorem bdd_on_ball (f : ℝ × ℝ → ℝ) (hf : Continuous f) (r : ℝ) :
    ∃ C, ∀ u : ℝ × ℝ, euclidNorm u ≤ r → f u ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ × ℝ) r).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨C, fun u hu => ?_⟩
  have h1 := B38M1b.euclid_le u r hu
  have hm : u ∈ Metric.closedBall (0 : ℝ × ℝ) r := by
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le h1.1 h1.2
  exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC u hm)

theorem mv_dot (η : ℕ → ℝ) {n : ℕ} (g : ℕ → Fin n → ℝ) (t : ℕ) (θ : Fin n → ℝ) :
    B38LW.mv η g t ⬝ᵥ θ = ∑ i ∈ Finset.Icc 1 t, η i * (g i ⬝ᵥ θ) := by
  simp only [B38LW.mv, sum_dotProduct, smul_dotProduct, smul_eq_mul]

noncomputable def gt (q : ℝ) : Fin 3 → ℝ := ![1, q, q ^ 2]
noncomputable def tt (u : ℝ × ℝ) : Fin 3 → ℝ := ![u.1 ^ 2, 2 * u.1 * u.2, u.2 ^ 2]

theorem gt_tt (q : ℝ) (u : ℝ × ℝ) : gt q ⬝ᵥ tt u = (u.1 + u.2 * q) ^ 2 := by
  simp [gt, tt, dotProduct, Fin.sum_univ_three]; ring

theorem region (M : CVPricing.Regret.Model) (r : ℝ)
    (hr : r * (1 + M.ph) ≤ (M.a0.1 + M.a0.2 * M.ph) / 4)
    (q : ℝ) (hq : q ∈ Set.Icc M.pl M.ph) (u : ℝ × ℝ) (hu : euclidNorm u ≤ r) :
    M.a0.1 + M.a0.2 * q ∈ Set.Icc ((M.a0.1 + M.a0.2 * M.ph) / 2) (M.a0.1 + (M.a0.1 + M.a0.2 * M.ph)) ∧
    M.a0.1 + M.a0.2 * q + (u.1 + u.2 * q) ∈
      Set.Icc ((M.a0.1 + M.a0.2 * M.ph) / 2) (M.a0.1 + (M.a0.1 + M.a0.2 * M.ph)) ∧
    |u.1 + u.2 * q| ≤ (M.a0.1 + M.a0.2 * M.ph) / 4 := by
  have hδ : 0 < M.a0.1 + M.a0.2 * M.ph := M.a0_ph_pos
  have hB := M.a01_neg
  have hpl := M.pl_pos
  obtain ⟨hq1, hq2⟩ := hq
  have hq0 : 0 < q := lt_of_lt_of_le hpl hq1
  obtain ⟨h1, h2⟩ := B38M1b.euclid_le u r hu
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  have hx0lo : M.a0.1 + M.a0.2 * M.ph ≤ M.a0.1 + M.a0.2 * q := by nlinarith
  have hx0hi : M.a0.1 + M.a0.2 * q ≤ M.a0.1 := by nlinarith
  have hD : |u.1 + u.2 * q| ≤ (M.a0.1 + M.a0.2 * M.ph) / 4 := by
    rw [abs_le]; constructor <;> nlinarith
  obtain ⟨d1, d2⟩ := abs_le.mp hD
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hD⟩

/-- PATH CORE: on one path, the score drift is bounded by the two self-normalized martingale terms. -/
theorem path_core (M : CVPricing.Regret.Model) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∃ m : ℝ, 0 < m ∧ ∀ C0 : ℝ, 0 ≤ C0 → ∃ ε : ℝ, 0 < ε ∧
    ∃ (n : ℕ) (θ : ℝ × ℝ → Fin n → ℝ) (g : ℝ → Fin n → ℝ) (Cθ C1 Cθ' C2 : ℝ),
      (∀ j, ContinuousOn (fun q => g q j) (Set.Icc M.pl M.ph)) ∧
      ∀ (p d c : ℕ → ℝ) (t : ℕ), (∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc M.pl M.ph) →
        (∀ i ∈ Finset.Icc 1 t, 0 ≤ c i ∧ c i ≤ C0) → ∀ u : ℝ × ℝ, euclidNorm u ≤ ρ1 →
        ((qscore M p d t (M.a0 + u)).1 * u.1 + (qscore M p d t (M.a0 + u)).2 * u.2 ≤
          |B38LW.mv (fun i => d i - M.h (M.a0.1 + M.a0.2 * p i)) (fun i => g (p i)) t ⬝ᵥ θ u|
          + ε * |B38LW.mv (fun i => |d i - M.h (M.a0.1 + M.a0.2 * p i)| - c i)
              (fun i => gt (p i)) t ⬝ᵥ tt u|
          - m / 2 * ∑ i ∈ Finset.Icc 1 t, (u.1 + u.2 * p i) ^ 2) ∧
        (B38LW.mv (fun i => d i - M.h (M.a0.1 + M.a0.2 * p i)) (fun i => g (p i)) t ⬝ᵥ θ u) ^ 2 ≤
          B38LW.Zq (fun i => d i - M.h (M.a0.1 + M.a0.2 * p i)) (fun i => g (p i)) t *
            (Cθ + C1 * ∑ i ∈ Finset.Icc 1 t, (u.1 + u.2 * p i) ^ 2) ∧
        (B38LW.mv (fun i => |d i - M.h (M.a0.1 + M.a0.2 * p i)| - c i) (fun i => gt (p i)) t
            ⬝ᵥ tt u) ^ 2 ≤
          B38LW.Zq (fun i => |d i - M.h (M.a0.1 + M.a0.2 * p i)| - c i) (fun i => gt (p i)) t *
            (Cθ' + C2 * ∑ i ∈ Finset.Icc 1 t, (u.1 + u.2 * p i) ^ 2) := by
  obtain ⟨ρd, hρd, m, hm, hdrift⟩ := B38M1b.drift_bound M
  set A := M.a0.1 with hA
  set B := M.a0.2 with hB
  set δ0 := A + B * M.ph with hδ0
  have hδ : 0 < δ0 := M.a0_ph_pos
  have hph : 0 < 1 + M.ph := by linarith [M.pl_pos, M.pl_lt_ph]
  set ρ1 := min ρd (δ0 / (4 * (1 + M.ph))) with hρ1
  have hρ1 : 0 < ρ1 := lt_min hρd (by positivity)
  have hρ1B : ρ1 * (1 + M.ph) ≤ δ0 / 4 := by
    have : ρ1 ≤ δ0 / (4 * (1 + M.ph)) := min_le_right _ _
    calc ρ1 * (1 + M.ph) ≤ δ0 / (4 * (1 + M.ph)) * (1 + M.ph) :=
          mul_le_mul_of_nonneg_right this hph.le
      _ = δ0 / 4 := by field_simp
  refine ⟨ρ1, hρ1, m, hm, fun C0 hC0 => ?_⟩
  set ε := m / (2 * (C0 + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hεC : ε * C0 ≤ m / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set lo := δ0 / 2
  set hi := A + δ0
  have hIcc : ∀ y ∈ Set.Icc lo hi, 0 < y := fun y hy => lt_of_lt_of_le (by positivity) hy.1
  obtain ⟨n, θ, g, hθc, hgc, herr⟩ := B38Dec.decomp (W M) (deriv (W M)) lo hi A B M.pl M.ph
    (fun y hy => W_hasDeriv M y (hIcc y hy))
    ((W_deriv_cont M).mono (fun y hy => hIcc y hy))
    (fun q hq => (region M ρ1 hρ1B q hq 0 (by simp [euclidNorm, hρ1.le])).1) ε hε0
  obtain ⟨Wm, hWm⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
    ((W_contDiffOn M).continuousOn.mono (fun y hy => hIcc y hy))
  obtain ⟨Cθ, hCθ⟩ := bdd_on_ball (fun u => θ u ⬝ᵥ θ u)
    (continuous_finset_sum _ (fun j _ => (hθc j).mul (hθc j))) ρ1
  obtain ⟨Cθ', hCθ'⟩ := bdd_on_ball (fun u => tt u ⬝ᵥ tt u) (by
    simp only [tt, dotProduct, Fin.sum_univ_three]; fun_prop) ρ1
  set Dm := δ0 / 4
  refine ⟨ε, hε0, n, θ, g, Cθ, (max Wm 0 + ε * Dm) ^ 2, Cθ', Dm ^ 2, hgc, ?_⟩
  intro p d c t hp hc u hu
  set e : ℕ → ℝ := fun i => d i - M.h (M.a0.1 + M.a0.2 * p i) with he
  set Q := ∑ i ∈ Finset.Icc 1 t, (u.1 + u.2 * p i) ^ 2 with hQ
  have hreg : ∀ i ∈ Finset.Icc 1 t, A + B * p i ∈ Set.Icc lo hi ∧
      A + B * p i + (u.1 + u.2 * p i) ∈ Set.Icc lo hi ∧ |u.1 + u.2 * p i| ≤ Dm :=
    fun i hi => region M ρ1 hρ1B (p i) (hp i hi) u hu
  have herr' : ∀ i ∈ Finset.Icc 1 t, |W M (A + B * p i + (u.1 + u.2 * p i)) * (u.1 + u.2 * p i)
      - θ u ⬝ᵥ g (p i)| ≤ ε * (u.1 + u.2 * p i) ^ 2 :=
    fun i hi => herr (p i) u (hreg i hi).1 (hreg i hi).2.1
  -- the drift bound of M1b
  have hu' : euclidNorm (M.a0 + u - M.a0) ≤ ρd := by
    rw [add_sub_cancel_left]; exact le_trans hu (min_le_left _ _)
  have hD := (hdrift p d t hp (M.a0 + u) hu').2
  have hx : ∀ i, (M.a0 + u).1 + (M.a0 + u).2 * p i = A + B * p i + (u.1 + u.2 * p i) := by
    intro i; simp only [Prod.fst_add, Prod.snd_add, hA, hB]; ring
  simp only [add_sub_cancel_left, hx] at hD
  -- rewrite the noise sum
  have hsplit : ∑ i ∈ Finset.Icc 1 t, deriv M.h (A + B * p i + (u.1 + u.2 * p i)) /
      (M.σ ^ 2 * M.v (M.h (A + B * p i + (u.1 + u.2 * p i)))) *
      (d i - M.h (M.a0.1 + M.a0.2 * p i)) * (u.1 + u.2 * p i) =
      ∑ i ∈ Finset.Icc 1 t, e i * (g (p i) ⬝ᵥ θ u) + ∑ i ∈ Finset.Icc 1 t, e i *
        (W M (A + B * p i + (u.1 + u.2 * p i)) * (u.1 + u.2 * p i) - θ u ⬝ᵥ g (p i)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [he, W, dotProduct_comm (g (p i))]; ring
  have hS1 : ∑ i ∈ Finset.Icc 1 t, e i * (g (p i) ⬝ᵥ θ u) =
      B38LW.mv e (fun i => g (p i)) t ⬝ᵥ θ u := (mv_dot e _ t (θ u)).symm
  have hS2 : ∑ i ∈ Finset.Icc 1 t, (|e i| - c i) * (u.1 + u.2 * p i) ^ 2 =
      B38LW.mv (fun i => |e i| - c i) (fun i => gt (p i)) t ⬝ᵥ tt u := by
    rw [mv_dot]; refine Finset.sum_congr rfl (fun i _ => by rw [gt_tt])
  have hE : ∑ i ∈ Finset.Icc 1 t, e i * (W M (A + B * p i + (u.1 + u.2 * p i)) *
      (u.1 + u.2 * p i) - θ u ⬝ᵥ g (p i)) ≤
      ε * C0 * Q + ε * (B38LW.mv (fun i => |e i| - c i) (fun i => gt (p i)) t ⬝ᵥ tt u) := by
    rw [← hS2, hQ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have h1 := herr' i hi
    have h2 := hc i hi
    have h3 := le_abs_self (e i * (W M (A + B * p i + (u.1 + u.2 * p i)) * (u.1 + u.2 * p i)
      - θ u ⬝ᵥ g (p i)))
    rw [abs_mul] at h3
    have h4 : |e i| * |W M (A + B * p i + (u.1 + u.2 * p i)) * (u.1 + u.2 * p i)
        - θ u ⬝ᵥ g (p i)| ≤ |e i| * (ε * (u.1 + u.2 * p i) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h5 : 0 ≤ (u.1 + u.2 * p i) ^ 2 := sq_nonneg _
    have h6 := mul_le_mul_of_nonneg_right h2.2 (mul_nonneg hε0.le h5)
    nlinarith [h3, h4, h6]
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · have hD' := hD
    rw [hsplit, hS1] at hD'
    try rw [← hQ] at hD'
    have a1 := le_abs_self (B38LW.mv e (fun i => g (p i)) t ⬝ᵥ θ u)
    have a2 := le_abs_self (B38LW.mv (fun i => |e i| - c i) (fun i => gt (p i)) t ⬝ᵥ tt u)
    have a3 := mul_le_mul_of_nonneg_left a2 hε0.le
    have a4 : ε * C0 * Q ≤ m / 2 * Q := mul_le_mul_of_nonneg_right hεC hQ0
    linarith
  · have hcs := B38LW.mv_dot_sq_le e (fun i => g (p i)) t (θ u)
    have hb : ∑ i ∈ Finset.Icc 1 t, (g (p i) ⬝ᵥ θ u) ^ 2 ≤ (max Wm 0 + ε * Dm) ^ 2 * Q := by
      rw [hQ, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i hi => ?_)
      have h1 := herr' i hi
      have hw := hWm _ (hreg i hi).2.1
      rw [Real.norm_eq_abs] at hw
      have hΔ := (hreg i hi).2.2
      have hw' : |W M (A + B * p i + (u.1 + u.2 * p i))| ≤ max Wm 0 := le_trans hw (le_max_left _ _)
      have hm0 : 0 ≤ max Wm 0 := le_max_right _ _
      have k1 : |g (p i) ⬝ᵥ θ u| ≤ (max Wm 0 + ε * Dm) * |u.1 + u.2 * p i| := by
        have e1 : g (p i) ⬝ᵥ θ u = W M (A + B * p i + (u.1 + u.2 * p i)) * (u.1 + u.2 * p i) -
            (W M (A + B * p i + (u.1 + u.2 * p i)) * (u.1 + u.2 * p i) - θ u ⬝ᵥ g (p i)) := by
          rw [dotProduct_comm]; ring
        rw [e1]
        refine le_trans (abs_sub _ _) ?_
        rw [abs_mul]
        have hsq : (u.1 + u.2 * p i) ^ 2 ≤ Dm * |u.1 + u.2 * p i| := by
          rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)
        have : ε * (u.1 + u.2 * p i) ^ 2 ≤ ε * Dm * |u.1 + u.2 * p i| := by
          calc ε * (u.1 + u.2 * p i) ^ 2 ≤ ε * (Dm * |u.1 + u.2 * p i|) :=
                mul_le_mul_of_nonneg_left hsq hε0.le
            _ = ε * Dm * |u.1 + u.2 * p i| := by ring
        nlinarith [abs_nonneg (u.1 + u.2 * p i), mul_le_mul_of_nonneg_right hw'
          (abs_nonneg (u.1 + u.2 * p i))]
      have k2 := pow_le_pow_left₀ (abs_nonneg _) k1 2
      rw [sq_abs, mul_pow, sq_abs] at k2
      exact k2
    have hz := B38LW.Zq_nonneg e (fun i => g (p i)) t
    have hθb := hCθ u hu
    calc _ ≤ _ := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [show θ u ⬝ᵥ θ u ≤ Cθ from hθb]) hz
  · have hcs := B38LW.mv_dot_sq_le (fun i => |e i| - c i) (fun i => gt (p i)) t (tt u)
    have hb : ∑ i ∈ Finset.Icc 1 t, (gt (p i) ⬝ᵥ tt u) ^ 2 ≤ Dm ^ 2 * Q := by
      rw [hQ, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i hi => ?_)
      rw [gt_tt]
      have hΔ := (hreg i hi).2.2
      have k := pow_le_pow_left₀ (abs_nonneg _) hΔ 2
      rw [sq_abs] at k
      have : ((u.1 + u.2 * p i) ^ 2) ^ 2 = (u.1 + u.2 * p i) ^ 2 * (u.1 + u.2 * p i) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right k (sq_nonneg _) |>.trans_eq (by ring)
    have hz := B38LW.Zq_nonneg (fun i => |e i| - c i) (fun i => gt (p i)) t
    have hθb := hCθ' u hu
    calc _ ≤ _ := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [show tt u ⬝ᵥ tt u ≤ Cθ' from hθb]) hz

theorem sq_bound_abs (S Z Q C D m : ℝ) (hm : 0 < m) (hZ : 0 ≤ Z) (hQ : 0 ≤ Q)
    (h : S ^ 2 ≤ Z * (C + D * Q)) :
    |S| ≤ m / 4 * Q + (2 * |D| / m + |C| + 1) * (1 + Z) := by
  set K := 2 * |D| / m + |C| + 1 with hK
  have hK1 : 1 ≤ K := by have : 0 ≤ 2 * |D| / m := by positivity
                         linarith [abs_nonneg C]
  have hKD : |D| ≤ m / 2 * K := by
    have : m / 2 * (2 * |D| / m) = |D| := by field_simp
    nlinarith [abs_nonneg C]
  set R := m / 4 * Q + K * (1 + Z)
  have hR : 0 ≤ R := by positivity
  apply abs_le_of_sq_le_sq _ hR
  have e1 : S ^ 2 ≤ Z * (|C| + |D| * Q) := by
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ hZ)
    have := mul_le_mul_of_nonneg_right (le_abs_self D) hQ
    linarith [le_abs_self C]
  have e2 : Z * |D| * Q ≤ m / 2 * K * Q * Z := by
    have := mul_le_mul_of_nonneg_right hKD (mul_nonneg hQ hZ); nlinarith
  have e3 : Z * |C| ≤ K ^ 2 * (1 + Z) ^ 2 := by
    have h1 : |C| ≤ K := by have : 0 ≤ 2 * |D| / m := by positivity
                            linarith
    have h2 : K ≤ K ^ 2 := by nlinarith
    have h3 : Z ≤ (1 + Z) ^ 2 := by nlinarith
    calc Z * |C| ≤ (1 + Z) ^ 2 * K ^ 2 := mul_le_mul h3 (h1.trans h2) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e4 : R ^ 2 = (m / 4 * Q) ^ 2 + 2 * (m / 4 * Q) * (K * (1 + Z)) + K ^ 2 * (1 + Z) ^ 2 := by ring
  have e5 : 0 ≤ (m / 4 * Q) ^ 2 := sq_nonneg _
  have e6 : m / 2 * K * Q * Z ≤ 2 * (m / 4 * Q) * (K * (1 + Z)) := by
    have : 0 ≤ m / 2 * K * Q := by positivity
    nlinarith
  nlinarith

/-- (ii): at a root inside the ball, the quadratic form is controlled by the martingale terms. -/
theorem Q_bound (m ε Cθ C1 Cθ' C2 : ℝ) (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ S1 S2 Z1 Z2 Q : ℝ, 0 ≤ Q → 0 ≤ Z1 → 0 ≤ Z2 →
      S1 ^ 2 ≤ Z1 * (Cθ + C1 * Q) → S2 ^ 2 ≤ Z2 * (Cθ' + C2 * Q) →
      0 ≤ |S1| + ε * |S2| - m / 2 * Q → Q ≤ K * (1 + Z1 + Z2) := by
  set K1 := 2 * |C1| / (m / 2) + |Cθ| + 1
  set K2 := 2 * |ε ^ 2 * C2| / (m / 2) + |ε ^ 2 * Cθ'| + 1
  have hK1 : 0 < K1 := by positivity
  have hK2 : 0 < K2 := by positivity
  refine ⟨4 * (K1 + K2) / m, by positivity, fun S1 S2 Z1 Z2 Q hQ hZ1 hZ2 h1 h2 h0 => ?_⟩
  have b1 := sq_bound_abs S1 Z1 Q Cθ C1 (m / 2) (by positivity) hZ1 hQ h1
  have h2' : (ε * S2) ^ 2 ≤ Z2 * (ε ^ 2 * Cθ' + ε ^ 2 * C2 * Q) := by
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg ε)
    calc (ε * S2) ^ 2 = ε ^ 2 * S2 ^ 2 := by ring
      _ ≤ ε ^ 2 * (Z2 * (Cθ' + C2 * Q)) := this
      _ = _ := by ring
  have b2 := sq_bound_abs (ε * S2) Z2 Q (ε ^ 2 * Cθ') (ε ^ 2 * C2) (m / 2) (by positivity) hZ2 hQ h2'
  have hεS : ε * |S2| ≤ |ε * S2| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (le_abs_self ε) (abs_nonneg _)
  have b1' : |S1| ≤ m / 2 / 4 * Q + K1 * (1 + Z1) := b1
  have b2' : |ε * S2| ≤ m / 2 / 4 * Q + K2 * (1 + Z2) := b2
  have k : m / 4 * Q ≤ (K1 + K2) * (1 + Z1 + Z2) := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith

/-- (i): small martingale terms force the drift on the sphere to be negative. -/
theorem neg_of_small (m ε qmin Cθ C1 Cθ' C2 : ℝ) (hm : 0 < m) (hq : 0 < qmin) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ S1 S2 Z1 Z2 Q q0 : ℝ, qmin ≤ q0 → q0 ≤ Q → 0 ≤ Z1 → 0 ≤ Z2 →
      S1 ^ 2 ≤ Z1 * (Cθ + C1 * Q) → S2 ^ 2 ≤ Z2 * (Cθ' + C2 * Q) → Z1 ≤ κ * q0 → Z2 ≤ κ * q0 →
      |S1| + ε * |S2| - m / 2 * Q < 0 := by
  set K := |Cθ| / qmin + |C1| + |Cθ'| / qmin + |C2| + 1 with hKdef
  have hK : 0 < K := by positivity
  refine ⟨m ^ 2 / (64 * (1 + ε ^ 2) * K), by positivity, ?_⟩
  intro S1 S2 Z1 Z2 Q q0 hq0 hQ hZ1 hZ2 h1 h2 hz1 hz2
  have hQ0 : 0 < Q := lt_of_lt_of_le hq (hq0.trans hQ)
  set κ := m ^ 2 / (64 * (1 + ε ^ 2) * K) with hκ
  have hκ0 : 0 < κ := by positivity
  -- generic: Z (C + D Q) ≤ κ K Q²
  have gen : ∀ Z C D : ℝ, 0 ≤ Z → Z ≤ κ * q0 → |C| / qmin + |D| ≤ K →
      Z * (C + D * Q) ≤ κ * K * Q ^ 2 := by
    intro Z C D hZ hz hCD
    have c1 : C + D * Q ≤ (|C| / qmin + |D|) * Q := by
      have : |C| ≤ |C| / qmin * Q := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hq]
        exact mul_le_mul_of_nonneg_left (hq0.trans hQ) (abs_nonneg _)
      have := mul_le_mul_of_nonneg_right (le_abs_self D) hQ0.le
      nlinarith [le_abs_self C]
    have c2 : (|C| / qmin + |D|) * Q ≤ K * Q := mul_le_mul_of_nonneg_right hCD hQ0.le
    have c3 : Z ≤ κ * Q := le_trans hz (mul_le_mul_of_nonneg_left (by linarith) hκ0.le)
    rcases le_or_gt (C + D * Q) 0 with hneg | hpos
    · have : Z * (C + D * Q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hZ hneg
      have : 0 ≤ κ * K * Q ^ 2 := by positivity
      linarith
    · calc Z * (C + D * Q) ≤ (κ * Q) * (K * Q) := mul_le_mul c3 (c1.trans c2) hpos.le (by positivity)
        _ = κ * K * Q ^ 2 := by ring
  have hκK : κ * K = m ^ 2 / (64 * (1 + ε ^ 2)) := by rw [hκ]; field_simp
  have s1 : S1 ^ 2 ≤ m ^ 2 / (64 * (1 + ε ^ 2)) * Q ^ 2 := by
    rw [← hκK]; refine le_trans h1 (gen Z1 Cθ C1 hZ1 hz1 ?_)
    have : 0 ≤ |Cθ'| / qmin + |C2| := by positivity
    linarith
  have s2 : S2 ^ 2 ≤ m ^ 2 / (64 * (1 + ε ^ 2)) * Q ^ 2 := by
    rw [← hκK]; refine le_trans h2 (gen Z2 Cθ' C2 hZ2 hz2 ?_)
    have : 0 ≤ |Cθ| / qmin + |C1| := by positivity
    linarith
  have hb : 0 < m / 4 * Q := by positivity
  have a1 : |S1| < m / 4 * Q := by
    apply abs_lt_of_sq_lt_sq _ hb.le
    have : m ^ 2 / (64 * (1 + ε ^ 2)) * Q ^ 2 < (m / 4 * Q) ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      have : 0 < m ^ 2 * Q ^ 2 := by positivity
      nlinarith [sq_nonneg ε]
    linarith
  have a2 : ε * |S2| < m / 4 * Q := by
    have : |ε * S2| < m / 4 * Q := by
      apply abs_lt_of_sq_lt_sq _ hb.le
      have e : (ε * S2) ^ 2 = ε ^ 2 * S2 ^ 2 := by ring
      rw [e]
      have k := mul_le_mul_of_nonneg_left s2 (sq_nonneg ε)
      have : ε ^ 2 * (m ^ 2 / (64 * (1 + ε ^ 2)) * Q ^ 2) < (m / 4 * Q) ^ 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc', div_lt_iff₀ (by positivity)]
        have : 0 < m ^ 2 * Q ^ 2 := by positivity
        nlinarith [sq_nonneg ε]
      linarith
    calc ε * |S2| ≤ |ε| * |S2| := mul_le_mul_of_nonneg_right (le_abs_self ε) (abs_nonneg _)
      _ = |ε * S2| := (abs_mul _ _).symm
      _ < _ := this
  linarith

theorem euclid_sq (u : ℝ × ℝ) : euclidNorm u ^ 2 = u.1 ^ 2 + u.2 ^ 2 := by
  unfold euclidNorm; rw [Real.sq_sqrt (by positivity)]

/-- PATH ALL: per-path existence of a root (small martingale terms) and the rate bound at a root. -/
theorem path_all (M : CVPricing.Regret.Model) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∀ C0 : ℝ, 0 ≤ C0 → ∃ (n : ℕ) (g : ℝ → Fin n → ℝ),
      (∀ j, ContinuousOn (fun q => g q j) (Set.Icc M.pl M.ph)) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ1 → ∀ L : ℝ, 0 < L → ∃ κ : ℝ, 0 < κ ∧
        ∀ (p d c : ℕ → ℝ) (t : ℕ) (α : ℝ), 2 ≤ t → 0 ≤ α →
          (∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc M.pl M.ph) →
          (∀ i ∈ Finset.Icc 1 t, 0 ≤ c i ∧ c i ≤ C0) →
          L * (t : ℝ) ^ α ≤ minRayleigh (fisherOf p t) →
          B38LW.Zq (fun i => d i - M.h (M.a0.1 + M.a0.2 * p i)) (fun i => g (p i)) t ≤
            κ * (t : ℝ) ^ α →
          B38LW.Zq (fun i => |d i - M.h (M.a0.1 + M.a0.2 * p i)| - c i) (fun i => gt (p i)) t ≤
            κ * (t : ℝ) ^ α →
          ∃ a, euclidNorm (a - M.a0) < ρ ∧ IsMQLE M p d t a) ∧
      (∀ L : ℝ, 0 < L → ∃ K : ℝ, 0 < K ∧
        ∀ (p d c : ℕ → ℝ) (t : ℕ) (α : ℝ), 2 ≤ t →
          (∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc M.pl M.ph) →
          (∀ i ∈ Finset.Icc 1 t, 0 ≤ c i ∧ c i ≤ C0) →
          L * (t : ℝ) ^ α ≤ minRayleigh (fisherOf p t) →
          ∀ a, IsMQLE M p d t a → euclidNorm (a - M.a0) ≤ ρ1 →
          euclidNorm (a - M.a0) ^ 2 * (t : ℝ) ^ α ≤ K * (1 +
            B38LW.Zq (fun i => d i - M.h (M.a0.1 + M.a0.2 * p i)) (fun i => g (p i)) t +
            B38LW.Zq (fun i => |d i - M.h (M.a0.1 + M.a0.2 * p i)| - c i) (fun i => gt (p i)) t)) := by
  obtain ⟨ρ0, hρ0, m, hm, hcore⟩ := path_core M
  have hδ : 0 < M.a0.1 + M.a0.2 * M.ph := M.a0_ph_pos
  have hph : 0 < 1 + M.ph := by linarith [M.pl_pos, M.pl_lt_ph]
  set ρ1 := min ρ0 ((M.a0.1 + M.a0.2 * M.ph) / (4 * (1 + M.ph))) with hρ1d
  have hρ1 : 0 < ρ1 := lt_min hρ0 (by positivity)
  have hρ1B : ρ1 * (1 + M.ph) ≤ (M.a0.1 + M.a0.2 * M.ph) / 4 := by
    have : ρ1 ≤ (M.a0.1 + M.a0.2 * M.ph) / (4 * (1 + M.ph)) := min_le_right _ _
    calc ρ1 * (1 + M.ph) ≤ (M.a0.1 + M.a0.2 * M.ph) / (4 * (1 + M.ph)) * (1 + M.ph) :=
          mul_le_mul_of_nonneg_right this hph.le
      _ = _ := by field_simp
  refine ⟨ρ1, hρ1, fun C0 hC0 => ?_⟩
  obtain ⟨ε, hε, n, θ, g, Cθ, C1, Cθ', C2, hgc, hc⟩ := hcore C0 hC0
  have hcore' : ∀ (p d c : ℕ → ℝ) (t : ℕ), (∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc M.pl M.ph) →
      (∀ i ∈ Finset.Icc 1 t, 0 ≤ c i ∧ c i ≤ C0) → ∀ a : ℝ × ℝ, euclidNorm (a - M.a0) ≤ ρ1 → _ :=
    fun p d c t hp hcc a ha => hc p d c t hp hcc (a - M.a0) (le_trans ha (min_le_left _ _))
  refine ⟨n, g, hgc, ?_, ?_⟩
  · intro ρ hρ hρle L hL
    obtain ⟨κ0, hκ0, hneg⟩ := neg_of_small m ε (L * ρ ^ 2) Cθ C1 Cθ' C2 hm (by positivity)
    refine ⟨κ0 * (L * ρ ^ 2), by positivity, ?_⟩
    intro p d c t α ht hα hp hcc hlam hz1 hz2
    have htα : 1 ≤ (t : ℝ) ^ α := Real.one_le_rpow (by norm_cast; omega) hα
    apply B38M1a.score_root_of_inward M p d t ρ hρ
    · intro a ha i hi
      have := (region M ρ1 hρ1B (p i) (hp i hi) (a - M.a0) (le_trans ha hρle)).2.1.1
      have e : a.1 + a.2 * p i = M.a0.1 + M.a0.2 * p i + ((a - M.a0).1 + (a - M.a0).2 * p i) := by
        simp only [Prod.fst_sub, Prod.snd_sub]; ring
      rw [e]; exact lt_of_lt_of_le (by positivity) this
    · intro a ha
      obtain ⟨h1, h2, h3⟩ := hcore' p d c t hp hcc a (by rw [ha]; exact hρle)
      rw [add_sub_cancel] at h1
      have hq := B38M1d.quad_ge_minRayleigh p t (a - M.a0)
      have hn : (a - M.a0).1 ^ 2 + (a - M.a0).2 ^ 2 = ρ ^ 2 := by rw [← euclid_sq, ha]
      rw [hn] at hq
      have hQ : L * (t : ℝ) ^ α * ρ ^ 2 ≤ ∑ i ∈ Finset.Icc 1 t, ((a - M.a0).1 + (a - M.a0).2 * p i) ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_right hlam (sq_nonneg ρ)) hq
      have hqmin : L * ρ ^ 2 ≤ L * (t : ℝ) ^ α * ρ ^ 2 := by
        have : L * ρ ^ 2 * 1 ≤ L * ρ ^ 2 * (t : ℝ) ^ α :=
          mul_le_mul_of_nonneg_left htα (by positivity)
        linarith
      have key := hneg _ _ _ _ _ (L * (t : ℝ) ^ α * ρ ^ 2) hqmin hQ (B38LW.Zq_nonneg _ _ _)
        (B38LW.Zq_nonneg _ _ _) h2 h3 (by nlinarith) (by nlinarith)
      linarith
  · intro L hL
    obtain ⟨K0, hK0, hQb⟩ := Q_bound m ε Cθ C1 Cθ' C2 hm
    refine ⟨K0 / L, by positivity, ?_⟩
    intro p d c t α ht hp hcc hlam a ha hρa
    obtain ⟨h1, h2, h3⟩ := hcore' p d c t hp hcc a hρa
    rw [add_sub_cancel, ha.2] at h1
    simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at h1
    have hQ0 : 0 ≤ ∑ i ∈ Finset.Icc 1 t, ((a - M.a0).1 + (a - M.a0).2 * p i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hb := hQb _ _ _ _ _ hQ0 (B38LW.Zq_nonneg _ _ _) (B38LW.Zq_nonneg _ _ _) h2 h3 (by linarith)
    have hq := B38M1d.quad_ge_minRayleigh p t (a - M.a0)
    rw [← euclid_sq] at hq
    have hlow : L * ((t : ℝ) ^ α * euclidNorm (a - M.a0) ^ 2) ≤
        ∑ i ∈ Finset.Icc 1 t, ((a - M.a0).1 + (a - M.a0).2 * p i) ^ 2 := by
      rw [← mul_assoc]; exact le_trans (mul_le_mul_of_nonneg_right hlam (sq_nonneg _)) hq
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    nlinarith

end B38App

namespace B38Prob

open KeskinZeevi.SufficientConditions CVPricing.Regret MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

noncomputable def clamp (M : CVPricing.Regret.Model) (q : ℝ) : ℝ := max M.pl (min M.ph q)

noncomputable def hcx (M : CVPricing.Regret.Model) (y : ℝ) : ℝ :=
  M.h (max y (M.a0.1 + M.a0.2 * M.ph))

noncomputable def eta (M : CVPricing.Regret.Model) (p d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  d t ω - hcx M (M.a0.1 + M.a0.2 * clamp M (p t ω))

theorem clamp_cont (M : CVPricing.Regret.Model) : Continuous (clamp M) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clamp_mem (M : CVPricing.Regret.Model) (q : ℝ) : clamp M q ∈ Set.Icc M.pl M.ph :=
  ⟨le_max_left _ _, max_le M.pl_lt_ph.le (min_le_left _ _)⟩

theorem clamp_eq (M : CVPricing.Regret.Model) (q : ℝ) (hq : q ∈ Set.Icc M.pl M.ph) :
    clamp M q = q := by
  simp only [clamp, min_eq_right hq.2, max_eq_right hq.1]

theorem hcx_cont (M : CVPricing.Regret.Model) : Continuous (hcx M) :=
  M.h_contDiffOn.continuousOn.comp_continuous (continuous_id.max continuous_const)
    (fun y => Set.mem_Ici.mpr (le_trans M.a0_ph_pos.le (le_max_right _ _)))

theorem hcx_eq (M : CVPricing.Regret.Model) (q : ℝ) (hq : q ∈ Set.Icc M.pl M.ph) :
    hcx M (M.a0.1 + M.a0.2 * q) = M.h (M.a0.1 + M.a0.2 * q) := by
  have : M.a0.1 + M.a0.2 * M.ph ≤ M.a0.1 + M.a0.2 * q := by nlinarith [M.a01_neg, hq.2]
  simp only [hcx, max_eq_left this]

theorem eta_eq (M : CVPricing.Regret.Model) (p d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)
    (hq : p t ω ∈ Set.Icc M.pl M.ph) : eta M p d t ω = noise M p d t ω := by
  simp only [eta, noise, clamp_eq M _ hq, hcx_eq M _ hq]

theorem comp_clamp_cont (M : CVPricing.Regret.Model) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc M.pl M.ph)) : Continuous (fun q => f (clamp M q)) :=
  hf.comp_continuous (clamp_cont M) (clamp_mem M)

theorem bound_on_Icc (M : CVPricing.Regret.Model) {n : ℕ} (g : ℝ → Fin n → ℝ)
    (hg : ∀ j, ContinuousOn (fun q => g q j) (Set.Icc M.pl M.ph)) :
    ∃ G, ∀ q ∈ Set.Icc M.pl M.ph, ∀ j, |g q j| ≤ G := by
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := M.pl) (b := M.ph)).exists_bound_of_continuousOn
    (f := fun q => ∑ j, |g q j|) (continuousOn_finset_sum _ (fun j _ => (hg j).abs))
  refine ⟨G, fun q hq j => ?_⟩
  have h1 := hG q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at h1
  exact le_trans (Finset.single_le_sum (f := fun j => |g q j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ j)) h1

theorem var_bound (M : CVPricing.Regret.Model) :
    ∃ V, 0 ≤ V ∧ ∀ q ∈ Set.Icc M.pl M.ph, M.σ ^ 2 * M.v (M.h (M.a0.1 + M.a0.2 * q)) ≤ V := by
  have hpos : ∀ q ∈ Set.Icc M.pl M.ph, 0 < M.a0.1 + M.a0.2 * q := fun q hq => by
    nlinarith [M.a01_neg, hq.2, M.a0_ph_pos]
  have hc : ContinuousOn (fun q => M.σ ^ 2 * M.v (M.h (M.a0.1 + M.a0.2 * q))) (Set.Icc M.pl M.ph) := by
    refine continuousOn_const.mul ?_
    refine M.v_contDiffOn.continuousOn.comp ?_ (fun q hq => Set.mem_Ici.mpr
      (M.h_nonneg _ (hpos q hq).le))
    refine M.h_contDiffOn.continuousOn.comp (by fun_prop) (fun q hq => Set.mem_Ici.mpr (hpos q hq).le)
  obtain ⟨V, hV⟩ := (isCompact_Icc (a := M.pl) (b := M.ph)).exists_bound_of_continuousOn hc
  refine ⟨max V 0, le_max_right _ _, fun q hq => ?_⟩
  exact le_trans (le_abs_self _) (le_trans (by simpa [Real.norm_eq_abs] using hV q hq) (le_max_left _ _))

variable (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)

/-- first Lai-Wei instance: the (clamped) noise with continuous weights `g`. -/
theorem lw1 (M : CVPricing.Regret.Model) (p d : ℕ → Ω → ℝ) (hD : DemandModel M P ℱ p d)
    (hpr : ∀ᵐ ω ∂P, ∀ t : ℕ, 1 ≤ t → p t ω ∈ Set.Icc M.pl M.ph)
    {n : ℕ} (g : ℝ → Fin n → ℝ) (hg : ∀ j, ContinuousOn (fun q => g q j) (Set.Icc M.pl M.ph))
    (V : ℝ) (hV0 : 0 ≤ V) (hV : ∀ q ∈ Set.Icc M.pl M.ph, M.σ ^ 2 * M.v (M.h (M.a0.1 + M.a0.2 * q)) ≤ V)
    (G : ℝ) (hG : ∀ q ∈ Set.Icc M.pl M.ph, ∀ j, |g q j| ≤ G) :
    B38LW.LWHyp P ℱ (eta M p d) (fun t ω => g (clamp M (p t ω))) V G := by
  have hpm : ∀ t, 1 ≤ t → Measurable[ℱ (t - 1)] (p t) := fun t ht => (hD.price_meas t ht).measurable
  have hae : ∀ t, 1 ≤ t → eta M p d t =ᵐ[P] noise M p d t := fun t ht => by
    filter_upwards [hpr] with ω hω; exact eta_eq M p d t ω (hω t ht)
  have hae2 : ∀ t, 1 ≤ t → (fun ω => eta M p d t ω ^ 2) =ᵐ[P] fun ω => noise M p d t ω ^ 2 :=
    fun t ht => by filter_upwards [hae t ht] with ω hω; rw [hω]
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht j => ?_,
    fun t ω j => hG _ (clamp_mem M _) j, hV0⟩
  · have h1 : Measurable[ℱ t] (d t) := (hD.demand_meas t ht).measurable
    have h2 : Measurable[ℱ t] (fun ω => hcx M (M.a0.1 + M.a0.2 * clamp M (p t ω))) :=
      ((hcx_cont M).comp (continuous_const.add (continuous_const.mul (clamp_cont M)))).measurable.comp
        ((hpm t ht).mono (ℱ.mono (by omega)) le_rfl)
    exact h1.sub h2
  · exact (hD.noise_sq_integrable t ht).congr (hae2 t ht).symm
  · exact (condExp_congr_ae (hae t ht)).trans (hD.cond_mean t ht)
  · refine ((condExp_congr_ae (hae2 t ht)).trans (hD.cond_var t ht)).trans_le ?_
    filter_upwards [hpr] with ω hω
    exact hV _ (hω t ht)
  · exact (comp_clamp_cont M (fun q => g q j) (hg j)).measurable.comp (hpm t ht)

/-- second Lai-Wei instance: centred absolute noise with weights `(1, p, p²)`. -/
theorem lw2 (M : CVPricing.Regret.Model) (p d : ℕ → Ω → ℝ) (hD : DemandModel M P ℱ p d)
    {n : ℕ} (g : ℝ → Fin n → ℝ) (V G : ℝ)
    (h1 : B38LW.LWHyp P ℱ (eta M p d) (fun t ω => g (clamp M (p t ω))) V G) :
    B38LW.LWHyp P ℱ (fun t ω => |eta M p d t ω| - P[fun ω => |eta M p d t ω| | ℱ (t - 1)] ω)
      (fun t ω => B38App.gt (clamp M (p t ω))) (2 * V + 2 * ((1 + V) / 2) ^ 2)
      (1 + M.ph + M.ph ^ 2) := by
  have hpm : ∀ t, 1 ≤ t → Measurable[ℱ (t - 1)] (p t) := fun t ht => (hD.price_meas t ht).measurable
  refine B38LW.LW_abs h1 _ _ (fun t ht j => ?_) (fun t ω j => ?_)
  · have hc : Continuous (fun q => B38App.gt (clamp M q) j) := by
      fin_cases j <;> simp [B38App.gt] <;>
        first | exact clamp_cont M | exact (clamp_cont M).pow 2 | fun_prop
    exact hc.measurable.comp (hpm t ht)
  · have hm := clamp_mem M (p t ω)
    have hpl := M.pl_pos
    have h0 : 0 ≤ clamp M (p t ω) := le_trans hpl.le hm.1
    have hph : 0 < M.ph := lt_trans hpl M.pl_lt_ph
    have hb1 : |(1 : ℝ)| ≤ 1 + M.ph + M.ph ^ 2 := by rw [abs_one]; nlinarith
    have hb2 : |clamp M (p t ω)| ≤ 1 + M.ph + M.ph ^ 2 := by
      rw [abs_of_nonneg h0]; nlinarith [hm.2]
    have hb3 : |clamp M (p t ω) ^ 2| ≤ 1 + M.ph + M.ph ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hm.2, mul_le_mul hm.2 hm.2 h0 hph.le]
    fin_cases j <;>
      first | simpa [B38App.gt] using hb1 | simpa [B38App.gt] using hb2 | simpa [B38App.gt] using hb3

end B38Prob

namespace B38Gen

open MeasureTheory Filter Topology KeskinZeevi.SufficientConditions CVPricing.Regret
open scoped ENNReal

theorem zero_set_eq {Ω : Type*} (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (F : ℝ × ℝ → Ω → ℝ) (hFc : ∀ ω, ContinuousOn (fun a => F a ω) K)
    (D : Set (ℝ × ℝ)) (hDK : D ⊆ K) (hKD : K ⊆ closure D) :
    {ω | ∃ a ∈ K, F a ω = 0} = ⋂ n : ℕ, ⋃ a ∈ D, {ω | |F a ω| < 1 / ((n : ℝ) + 1)} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨a, haK, ha0⟩ n
    have hc := hFc ω a haK
    rw [Metric.continuousWithinAt_iff] at hc
    obtain ⟨δ, hδ, hδc⟩ := hc (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨b, hbD, hb⟩ := Metric.mem_closure_iff.mp (hKD haK) δ hδ
    refine ⟨b, hbD, ?_⟩
    have := hδc (hDK hbD) (by rw [dist_comm]; exact hb)
    rw [Real.dist_eq, ha0, sub_zero] at this
    exact this
  · intro h
    choose a haD ha using h
    obtain ⟨x, hxK, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun n => hDK (haD n))
    refine ⟨x, hxK, ?_⟩
    have h1 : Tendsto (fun n => F (a (φ n)) ω) atTop (𝓝 (F x ω)) :=
      (hFc ω x hxK).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hlim, Eventually.of_forall (fun n => hDK (haD (φ n)))⟩)
    have h2 : Tendsto (fun n => F (a (φ n)) ω) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
      rw [Real.norm_eq_abs]; exact (ha (φ n)).le
    exact tendsto_nhds_unique h1 h2

theorem zero_set_meas {Ω : Type*} [MeasurableSpace Ω] (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (F : ℝ × ℝ → Ω → ℝ) (hFm : ∀ a ∈ K, Measurable (F a))
    (hFc : ∀ ω, ContinuousOn (fun a => F a ω) K) :
    MeasurableSet {ω | ∃ a ∈ K, F a ω = 0} := by
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  rw [zero_set_eq K hK F hFc D hDK hKD]
  exact MeasurableSet.iInter (fun n => MeasurableSet.biUnion hDc
    (fun a ha => measurableSet_lt (hFm a (hDK ha)).abs measurable_const))

open Classical in
theorem sel_meas {Ω : Type*} [MeasurableSpace Ω] (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (F : ℝ × ℝ → Ω → ℝ) (hFm : ∀ a ∈ K, Measurable (F a))
    (hFc : ∀ ω, ContinuousOn (fun a => F a ω) K)
    (hU : ∀ ω, ∀ a ∈ K, ∀ b ∈ K, F a ω = 0 → F b ω = 0 → a = b)
    (sel : Ω → ℝ × ℝ) (hsel : ∀ ω, (∃ a ∈ K, F a ω = 0) → sel ω ∈ K ∧ F (sel ω) ω = 0)
    (a₀ : ℝ × ℝ) :
    Measurable (fun ω => if ∃ a ∈ K, F a ω = 0 then sel ω else a₀) := by
  classical
  refine measurable_of_isClosed (fun C hC => ?_)
  have e : (fun ω => if ∃ a ∈ K, F a ω = 0 then sel ω else a₀) ⁻¹' C =
      {ω | ∃ a ∈ K ∩ C, F a ω = 0} ∪ ({ω | ∃ a ∈ K, F a ω = 0}ᶜ ∩ {_ω | a₀ ∈ C}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_compl_iff]
    by_cases hE : ∃ a ∈ K, F a ω = 0
    · rw [if_pos hE]
      obtain ⟨hs1, hs2⟩ := hsel ω hE
      constructor
      · intro h; exact Or.inl ⟨sel ω, ⟨hs1, h⟩, hs2⟩
      · rintro (⟨b, ⟨hbK, hbC⟩, hb0⟩ | ⟨h1, _⟩)
        · rw [hU ω _ hs1 _ hbK hs2 hb0]; exact hbC
        · exact absurd hE h1
    · rw [if_neg hE]
      constructor
      · intro h; exact Or.inr ⟨hE, h⟩
      · rintro (⟨b, ⟨hbK, _⟩, hb0⟩ | ⟨_, h⟩)
        · exact absurd ⟨b, hbK, hb0⟩ hE
        · exact h
  rw [e]
  exact (zero_set_meas (K ∩ C) (hK.inter_right hC) F (fun a ha => hFm a ha.1)
    (fun ω => (hFc ω).mono Set.inter_subset_left)).union
    ((zero_set_meas K hK F hFm hFc).compl.inter (MeasurableSet.const _))

theorem Tρ_lt_iff (M : CVPricing.Regret.Model) {Ω : Type*} (p d : ℕ → Ω → ℝ) (ρ : ℝ) (ω : Ω) (t : ℕ)
    (ht : 1 ≤ t) :
    Tρ M p d ρ ω < (t : ℕ∞) ↔ ∀ s : ℕ, t ≤ s →
      ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) s a ∧ euclidNorm (a - M.a0) ≤ ρ := by
  unfold Tρ
  constructor
  · intro h s hs
    by_contra hno
    have h1 : (s : ℕ∞) ≤ sSup {n : ℕ∞ | ∃ t : ℕ, (t : ℕ∞) = n ∧ 1 ≤ t ∧
        ¬ ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a ∧ euclidNorm (a - M.a0) ≤ ρ} :=
      le_sSup ⟨s, rfl, le_trans ht hs, hno⟩
    have h2 : (t : ℕ∞) ≤ s := ENat.coe_le_coe.mpr hs
    exact absurd (lt_of_le_of_lt (h2.trans h1) h) (lt_irrefl _)
  · intro h
    have h3 : sSup {n : ℕ∞ | ∃ t : ℕ, (t : ℕ∞) = n ∧ 1 ≤ t ∧
        ¬ ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a ∧ euclidNorm (a - M.a0) ≤ ρ}
        ≤ ((t - 1 : ℕ) : ℕ∞) := by
      apply sSup_le
      rintro n ⟨s, rfl, hs1, hno⟩
      have : s < t := by
        by_contra hst
        exact hno (h s (not_lt.mp hst))
      exact ENat.coe_le_coe.mpr (by omega : s ≤ t - 1)
    exact lt_of_le_of_lt h3 (ENat.coe_lt_coe.mpr (by omega : t - 1 < t))

theorem Tρ_sqrt_le (M : CVPricing.Regret.Model) {Ω : Type*} (p d : ℕ → Ω → ℝ) (ρ : ℝ) (ω : Ω) (f : ℝ≥0∞)
    (h : ∀ s : ℕ, 1 ≤ s → (¬ ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) s a ∧
      euclidNorm (a - M.a0) ≤ ρ) → (s : ℝ≥0∞) ≤ f ^ 2) :
    ((Tρ M p d ρ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) ≤ f := by
  have key : ((Tρ M p d ρ ω : ℝ≥0∞)) ≤ f ^ 2 := by
    by_cases hf : f ^ 2 = ⊤
    · rw [hf]; exact le_top
    set N := ⌊(f ^ 2).toReal⌋₊ with hN
    have hT : Tρ M p d ρ ω ≤ (N : ℕ∞) := by
      unfold Tρ
      apply sSup_le
      rintro n ⟨s, rfl, hs1, hno⟩
      have h1 := h s hs1 hno
      have h2 : (s : ℝ) ≤ (f ^ 2).toReal := by
        have := ENNReal.toReal_mono hf h1
        simpa using this
      exact ENat.coe_le_coe.mpr (Nat.le_floor h2)
    calc ((Tρ M p d ρ ω : ℝ≥0∞)) ≤ ((N : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr hT
      _ = (N : ℝ≥0∞) := by simp
      _ ≤ f ^ 2 := by
        rw [← ENNReal.ofReal_toReal hf, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (Nat.floor_le ENNReal.toReal_nonneg)
  calc ((Tρ M p d ρ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) ≤ (f ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = f := by
      rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num

theorem geom_summable (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun k : ℕ => ((k : ℝ) + 2) * r ^ k) := by
  have ha := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
    (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have hb := (summable_geometric_of_lt_one h0 h1).mul_left 2
  refine (ha.add hb).congr (fun k => ?_)
  simp only [pow_one]; ring

theorem two_rpow_pow (α : ℝ) (k : ℕ) : ((2 : ℝ) ^ k) ^ α = ((2 : ℝ) ^ α) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

theorem sup_set_eq {Ω : Type*} (Y : ℕ → Ω → ℝ) (N : ℕ) (lam : ℝ) :
    {ω | lam ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun k => Y k ω)} =
      ⋃ j ∈ Finset.range (N + 1), {ω | lam ≤ Y j ω} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, Finset.le_sup'_iff]

theorem tail_lintegral {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (A κ α : ℝ) (hA : 0 ≤ A) (hκ : 0 < κ) (hα : 1 / 2 < α)
    (hmax : ∀ N : ℕ, 1 ≤ N → ∀ lam : ℝ, 0 < lam →
      P {ω | lam ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun k => Y k ω)} ≤
        ENNReal.ofReal (A * (1 + Real.log N) / lam)) :
    ∃ f : Ω → ℝ≥0∞, Measurable f ∧ (∫⁻ ω, f ω ∂P) < ⊤ ∧
      ∀ ω (t : ℕ), 2 ≤ t → κ * (t : ℝ) ^ α < Y t ω → (t : ℝ≥0∞) ≤ f ω ^ 2 := by
  set θ : ℝ := (2 : ℝ) ^ α with hθ
  have hθ0 : 0 < θ := by positivity
  set B : ℕ → Set Ω := fun k => {ω | κ * θ ^ k ≤
    (Finset.range (2 ^ (k + 1) + 1)).sup' Finset.nonempty_range_add_one (fun j => Y j ω)} with hBd
  have hB : ∀ k, MeasurableSet (B k) := fun k => by
    simp only [hBd]
    rw [sup_set_eq]
    exact Finset.measurableSet_biUnion _ (fun j _ => measurableSet_le measurable_const (hY j))
  set f : Ω → ℝ≥0∞ := fun ω => ∑' k, (B k).indicator
    (fun _ => ENNReal.ofReal (Real.sqrt 2 ^ (k + 1))) ω with hfd
  have hfm : Measurable f := Measurable.ennreal_tsum (fun k => measurable_const.indicator (hB k))
  refine ⟨f, hfm, ?_, ?_⟩
  · set r : ℝ := Real.sqrt 2 / θ with hr
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by
      rw [hr, div_lt_one hθ0, hθ, Real.sqrt_eq_rpow]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hα
    set C : ℝ := Real.sqrt 2 * A / κ with hC
    have hC0 : 0 ≤ C := by positivity
    have hterm : ∀ k : ℕ, ENNReal.ofReal (Real.sqrt 2 ^ (k + 1)) * P (B k) ≤
        ENNReal.ofReal (C * (((k : ℝ) + 2) * r ^ k)) := by
      intro k
      have hN : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      have hm := hmax (2 ^ (k + 1)) hN (κ * θ ^ k) (by positivity)
      refine le_trans (mul_le_mul' le_rfl hm) ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hlog : Real.log ((2 ^ (k + 1) : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
        rw [Nat.cast_pow, Real.log_pow]
        have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
        have h0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        push_cast at h0 ⊢
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      have e1 : Real.sqrt 2 ^ (k + 1) = Real.sqrt 2 * Real.sqrt 2 ^ k := by ring
      have e2 : r ^ k = Real.sqrt 2 ^ k / θ ^ k := by rw [hr, div_pow]
      rw [e1, e2, hC]
      have hθk : 0 < θ ^ k := by positivity
      have hs2k : 0 < Real.sqrt 2 ^ k := by positivity
      have : A * (1 + Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) ≤ A * ((k : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hA
      calc Real.sqrt 2 * Real.sqrt 2 ^ k * (A * (1 + Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) /
            (κ * θ ^ k))
          ≤ Real.sqrt 2 * Real.sqrt 2 ^ k * (A * ((k : ℝ) + 2) / (κ * θ ^ k)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right this (by positivity)
        _ = Real.sqrt 2 * A / κ * (((k : ℝ) + 2) * (Real.sqrt 2 ^ k / θ ^ k)) := by
            ring
    calc (∫⁻ ω, f ω ∂P) = ∑' k, ENNReal.ofReal (Real.sqrt 2 ^ (k + 1)) * P (B k) := by
          rw [hfd, lintegral_tsum (fun k => (measurable_const.indicator (hB k)).aemeasurable)]
          congr 1; funext k
          rw [lintegral_indicator_const (hB k)]
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (C * (((k : ℝ) + 2) * r ^ k)) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' k : ℕ, C * (((k : ℝ) + 2) * r ^ k)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            ((geom_summable r hr0 hr1).mul_left C)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  · intro ω t ht hYt
    set k := Nat.log 2 t with hk
    have hk1 : 2 ^ k ≤ t := Nat.pow_log_le_self 2 (by omega)
    have hk2 : t < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
    have hmem : ω ∈ B k := by
      simp only [hBd, Set.mem_setOf_eq]
      have h1 : θ ^ k ≤ (t : ℝ) ^ α := by
        rw [hθ, ← two_rpow_pow]
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk1) (by linarith)
      have h2 : Y t ω ≤ (Finset.range (2 ^ (k + 1) + 1)).sup' Finset.nonempty_range_add_one
          (fun j => Y j ω) :=
        Finset.le_sup' (fun j => Y j ω) (Finset.mem_range.mpr (by omega))
      nlinarith
    have hfk : ENNReal.ofReal (Real.sqrt 2 ^ (k + 1)) ≤ f ω := by
      have := ENNReal.le_tsum (f := fun k => (B k).indicator
        (fun _ => ENNReal.ofReal (Real.sqrt 2 ^ (k + 1))) ω) k
      simp only [Set.indicator_of_mem hmem] at this
      exact this
    calc (t : ℝ≥0∞) = ENNReal.ofReal (t : ℝ) := (ENNReal.ofReal_natCast t).symm
      _ ≤ ENNReal.ofReal (Real.sqrt 2 ^ (k + 1)) ^ 2 := by
          rw [← ENNReal.ofReal_pow (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
          exact_mod_cast hk2.le
      _ ≤ f ω ^ 2 := pow_le_pow_left' hfk 2

theorem LB_le (ι : Type) [Fintype ι] (G : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    B38LW.LB ι G N ≤ (Real.log (Fintype.card ι).factorial +
      Fintype.card ι * Real.log (1 + G ^ 2)) + Fintype.card ι * Real.log N := by
  unfold B38LW.LB
  have hf : (0 : ℝ) < (Fintype.card ι).factorial := by exact_mod_cast Nat.factorial_pos _
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 0 < 1 + (N : ℝ) * G ^ 2 := by positivity
  rw [Real.log_mul hf.ne' (pow_pos h1 _).ne', Real.log_pow]
  have h2 : Real.log (1 + N * G ^ 2) ≤ Real.log (1 + G ^ 2) + Real.log N := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log h1 (by nlinarith [sq_nonneg G])
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 hn]

theorem LB_const_nonneg (ι : Type) [Fintype ι] (G : ℝ) :
    0 ≤ Real.log (Fintype.card ι).factorial + Fintype.card ι * Real.log (1 + G ^ 2) := by
  have h1 : 0 ≤ Real.log (Fintype.card ι).factorial :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
  have h2 : 0 ≤ Real.log (1 + G ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg G])
  positivity

end B38Gen

namespace B38Fin

open MeasureTheory Filter KeskinZeevi.SufficientConditions CVPricing.Regret
open scoped ENNReal

theorem lw_consts {Ω : Type*} {m0 : MeasurableSpace Ω} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0} {η : ℕ → Ω → ℝ}
    {g : ℕ → Ω → ι → ℝ} {Vv G : ℝ} (h : B38LW.LWHyp P ℱ η g Vv G) :
    ∃ A, 0 ≤ A ∧
      (∀ N : ℕ, 1 ≤ N → ∀ lam : ℝ, 0 < lam →
        P {ω | lam ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k => B38LW.Gp η g k ω)} ≤ ENNReal.ofReal (A * (1 + Real.log N) / lam)) ∧
      (∀ N : ℕ, 1 ≤ N → ∫ ω, B38LW.Gp η g N ω ∂P ≤ A * (1 + Real.log N)) := by
  have ha := B38Gen.LB_const_nonneg ι G
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hV := h.Vv_nonneg
  have key : ∀ N : ℕ, 1 ≤ N → Vv * B38LW.LB ι G N ≤
      Vv * ((Real.log (Fintype.card ι).factorial + Fintype.card ι * Real.log (1 + G ^ 2)) +
        Fintype.card ι) * (1 + Real.log N) := by
    intro N hN
    have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have h1 := B38Gen.LB_le ι G N hN
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hV
    nlinarith
  refine ⟨Vv * ((Real.log (Fintype.card ι).factorial + Fintype.card ι * Real.log (1 + G ^ 2)) +
        Fintype.card ι), by positivity, fun N hN lam hl => ?_, fun N hN => ?_⟩
  · refine le_trans (B38LW.maximal_Gp h N lam hl) (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (key N hN) hl.le
  · exact le_trans (B38LW.integral_Gp_le h N) (key N hN)

theorem mqle_spec (M : CVPricing.Regret.Model) {Ω : Type*} (p d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)
    (h : ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a) :
    IsMQLE M (fun s => p s ω) (fun s => d s ω) t (mqle M p d t ω) := by
  unfold mqle; rw [dif_pos h]; exact Classical.choose_spec h

theorem euclid_cont : Continuous euclidNorm := by
  unfold euclidNorm
  exact Real.continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2))

open Classical in
theorem main (M : CVPricing.Regret.Model) (hU : MQLEUnique M) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d) (α L p₁ p₂ : ℝ) (hα : 1 / 2 < α) (hL : 0 < L) (h12 : p₁ ≠ p₂)
    (hp1 : ∀ ω, p 1 ω = p₁) (hp2 : ∀ ω, p 2 ω = p₂)
    (hIcc : ∀ᵐ ω ∂P, ∀ t : ℕ, 1 ≤ t → p t ω ∈ Set.Icc M.pl M.ph)
    (hlam : ∀ᵐ ω ∂P, ∀ t : ℕ, 2 ≤ t → L * (t : ℝ) ^ α ≤ minRayleigh (fisherOf (fun s => p s ω) t)) :
    (∀ᵐ ω ∂P, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a) ∧
    (∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ a,
        IsMQLE M (fun s => p s ω) (fun s => d s ω) t a → euclidNorm (a - M.a0) < ε) ∧
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      (∫⁻ ω, ((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) ∂P) < ⊤ ∧
      ∃ K : ℝ, 0 < K ∧ ∀ t : ℕ, 2 ≤ t →
        Integrable (fun ω => if (t : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) P ∧
        ∫ ω, (if (t : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) ∂P
          ≤ K * (Real.log t / (t : ℝ) ^ α) := by
  obtain ⟨V, hV0, hV⟩ := B38Prob.var_bound M
  set C0 : ℝ := (1 + V) / 2 with hC0
  have hC00 : 0 ≤ C0 := by positivity
  obtain ⟨ρ1, hρ1, hpa⟩ := B38App.path_all M
  obtain ⟨n, g, hgc, hroot, hrate⟩ := hpa C0 hC00
  obtain ⟨G, hG⟩ := B38Prob.bound_on_Icc M g hgc
  have lw1 := B38Prob.lw1 P ℱ M p d hD hIcc g hgc V hV0 hV G hG
  have lw2 := B38Prob.lw2 P ℱ M p d hD g V G lw1
  set η := B38Prob.eta M p d with hηd
  set gc : ℕ → Ω → Fin n → ℝ := fun t ω => g (B38Prob.clamp M (p t ω)) with hgcd
  set gc2 : ℕ → Ω → Fin 3 → ℝ := fun t ω => B38App.gt (B38Prob.clamp M (p t ω)) with hgc2d
  set η2 : ℕ → Ω → ℝ := fun t ω => |η t ω| - P[fun ω => |η t ω| | ℱ (t - 1)] ω with hη2d
  set Y1 := B38LW.Gp η gc with hY1d
  set Y2 := B38LW.Gp η2 gc2 with hY2d
  have hY1m : ∀ t, Measurable (Y1 t) := fun t => (B38LW.Gp_meas lw1 t).mono (ℱ.le t) le_rfl
  have hY2m : ∀ t, Measurable (Y2 t) := fun t => (B38LW.Gp_meas lw2 t).mono (ℱ.le t) le_rfl
  obtain ⟨A1, hA1, hmax1, hint1⟩ := lw_consts lw1
  obtain ⟨A2, hA2, hmax2, hint2⟩ := lw_consts lw2
  have hcb : ∀ᵐ ω ∂P, ∀ i : ℕ, 1 ≤ i → 0 ≤ P[fun ω => |η i ω| | ℱ (i - 1)] ω ∧
      P[fun ω => |η i ω| | ℱ (i - 1)] ω ≤ C0 := by
    rw [ae_all_iff]; intro i
    by_cases hi : 1 ≤ i
    · filter_upwards [B38LW.absc_bound lw1 i hi] with ω hω _ using hω
    · exact Filter.Eventually.of_forall (fun ω h => absurd h hi)
  have hZ : ∀ ω, (∀ t : ℕ, 1 ≤ t → p t ω ∈ Set.Icc M.pl M.ph) → ∀ t : ℕ,
      B38LW.Zq (fun i => d i ω - M.h (M.a0.1 + M.a0.2 * p i ω)) (fun i => g (p i ω)) t
        ≤ Y1 t ω ∧
      B38LW.Zq (fun i => |d i ω - M.h (M.a0.1 + M.a0.2 * p i ω)| -
          P[fun ω => |η i ω| | ℱ (i - 1)] ω) (fun i => B38App.gt (p i ω)) t ≤ Y2 t ω := by
    intro ω hω t
    have he : ∀ i ∈ Finset.Icc 1 t, d i ω - M.h (M.a0.1 + M.a0.2 * p i ω) = η i ω :=
      fun i hi => (B38Prob.eta_eq M p d i ω (hω i (Finset.mem_Icc.mp hi).1)).symm
    have hcl : ∀ i ∈ Finset.Icc 1 t, B38Prob.clamp M (p i ω) = p i ω := fun i hi =>
      B38Prob.clamp_eq M _ (hω i (Finset.mem_Icc.mp hi).1)
    constructor
    · rw [B38LW.Zq_congr _ (fun k => η k ω) _ (fun k => gc k ω) t
        (fun i hi => ⟨he i hi, by simp only [hgcd, hcl i hi]⟩)]
      exact B38LW.Zq_le_Gp η gc t ω
    · rw [B38LW.Zq_congr _ (fun k => η2 k ω) _ (fun k => gc2 k ω) t
        (fun i hi => ⟨by simp only [hη2d, he i hi], by simp only [hgc2d, hcl i hi]⟩)]
      exact B38LW.Zq_le_Gp η2 gc2 t ω
  have hp1I : p₁ ∈ Set.Icc M.pl M.ph := by
    obtain ⟨ω, hω⟩ := hIcc.exists
    rw [← hp1 ω]; exact hω 1 le_rfl
  have hp2I : p₂ ∈ Set.Icc M.pl M.ph := by
    obtain ⟨ω, hω⟩ := hIcc.exists
    rw [← hp2 ω]; exact hω 2 (by norm_num)
  -- radius
  have hδ : 0 < M.a0.1 + M.a0.2 * M.ph := M.a0_ph_pos
  have hph : 0 < 1 + M.ph := by linarith [M.pl_pos, M.pl_lt_ph]
  set ρs := min ρ1 ((M.a0.1 + M.a0.2 * M.ph) / (4 * (1 + M.ph))) with hρsd
  have hρs : 0 < ρs := lt_min hρ1 (by positivity)
  have hρsB : ρs * (1 + M.ph) ≤ (M.a0.1 + M.a0.2 * M.ph) / 4 := by
    have : ρs ≤ (M.a0.1 + M.a0.2 * M.ph) / (4 * (1 + M.ph)) := min_le_right _ _
    calc ρs * (1 + M.ph) ≤ (M.a0.1 + M.a0.2 * M.ph) / (4 * (1 + M.ph)) * (1 + M.ph) :=
          mul_le_mul_of_nonneg_right this hph.le
      _ = _ := by field_simp
  have hdom : ∀ a : ℝ × ℝ, euclidNorm (a - M.a0) ≤ ρs → ∀ q ∈ Set.Icc M.pl M.ph,
      (M.a0.1 + M.a0.2 * M.ph) / 2 ≤ a.1 + a.2 * q := by
    intro a ha q hq
    have := (B38App.region M ρs hρsB q hq (a - M.a0) ha).2.1.1
    have e : a.1 + a.2 * q = M.a0.1 + M.a0.2 * q + ((a - M.a0).1 + (a - M.a0).2 * q) := by
      simp only [Prod.fst_sub, Prod.snd_sub]; ring
    rw [e]; exact this
  -- tail bound per radius
  have htail : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρs → ∃ f : Ω → ℝ≥0∞, Measurable f ∧
      (∫⁻ ω, f ω ∂P) < ⊤ ∧ ∀ᵐ ω ∂P, ((Tρ M p d ρ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) ≤ f ω := by
    intro ρ hρ hρle
    obtain ⟨κ, hκ, hκr⟩ := hroot ρ hρ (le_trans hρle (min_le_left _ _)) L hL
    obtain ⟨f1, hf1m, hf1i, hf1⟩ := B38Gen.tail_lintegral P Y1 hY1m A1 κ α hA1 hκ hα hmax1
    obtain ⟨f2, hf2m, hf2i, hf2⟩ := B38Gen.tail_lintegral P Y2 hY2m A2 κ α hA2 hκ hα hmax2
    refine ⟨fun ω => 1 + f1 ω + f2 ω, (measurable_const.add hf1m).add hf2m, ?_, ?_⟩
    · rw [lintegral_add_right _ hf2m, lintegral_add_left measurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
      exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hf1i⟩, hf2i⟩
    · filter_upwards [hIcc, hlam, hcb] with ω hω hlω hcω
      apply B38Gen.Tρ_sqrt_le
      intro s hs1 hno
      have hge : (1 : ℝ≥0∞) ≤ 1 + f1 ω + f2 ω := by rw [add_assoc]; exact le_self_add
      have hge1 : f1 ω ≤ 1 + f1 ω + f2 ω := le_trans le_add_self le_self_add
      have hge2 : f2 ω ≤ 1 + f1 ω + f2 ω := le_add_self
      rcases Nat.lt_or_ge s 2 with hs | hs
      · have : s = 1 := by omega
        subst this
        calc ((1 : ℕ) : ℝ≥0∞) = 1 ^ 2 := by simp
          _ ≤ _ := pow_le_pow_left' hge 2
      · have hpI : ∀ i ∈ Finset.Icc 1 s, p i ω ∈ Set.Icc M.pl M.ph :=
          fun i hi => hω i (Finset.mem_Icc.mp hi).1
        have hcI : ∀ i ∈ Finset.Icc 1 s, 0 ≤ P[fun ω => |η i ω| | ℱ (i - 1)] ω ∧
            P[fun ω => |η i ω| | ℱ (i - 1)] ω ≤ C0 := fun i hi => hcω i (Finset.mem_Icc.mp hi).1
        obtain ⟨hz1, hz2⟩ := hZ ω hω s
        by_cases hb1 : κ * (s : ℝ) ^ α < Y1 s ω
        · exact le_trans (hf1 ω s hs hb1) (pow_le_pow_left' hge1 2)
        by_cases hb2 : κ * (s : ℝ) ^ α < Y2 s ω
        · exact le_trans (hf2 ω s hs hb2) (pow_le_pow_left' hge2 2)
        exfalso
        obtain ⟨a, ha, hmq⟩ := hκr (fun i => p i ω) (fun i => d i ω)
          (fun i => P[fun ω => |η i ω| | ℱ (i - 1)] ω) s α hs (by linarith) hpI hcI
          (hlω s hs) (le_trans hz1 (not_lt.mp hb1)) (le_trans hz2 (not_lt.mp hb2))
        exact hno ⟨a, hmq, ha.le⟩
  have hfin : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρs → ∀ᵐ ω ∂P, ∃ t₀ : ℕ, 2 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a ∧ euclidNorm (a - M.a0) ≤ ρ := by
    intro ρ hρ hρle
    obtain ⟨f, hfm, hfi, hf⟩ := htail ρ hρ hρle
    filter_upwards [hf, ae_lt_top hfm hfi.ne] with ω h1 h2
    have hT : Tρ M p d ρ ω ≠ ⊤ := by
      intro hT
      rw [hT, ENat.toENNReal_top, ENNReal.top_rpow_of_pos (by norm_num)] at h1
      exact absurd (top_le_iff.mp h1) h2.ne
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hT
    refine ⟨N + 2, by omega, fun t ht => ?_⟩
    have hlt : Tρ M p d ρ ω < ((N + 2 : ℕ) : ℕ∞) := by
      rw [← hN]; exact ENat.coe_lt_coe.mpr (by omega)
    exact (B38Gen.Tρ_lt_iff M p d ρ ω (N + 2) (by omega)).mp hlt t ht
  refine ⟨?_, ?_, ρs, hρs, ?_⟩
  · filter_upwards [hfin ρs hρs le_rfl] with ω hω
    obtain ⟨t₀, _, ht₀⟩ := hω
    exact ⟨t₀, fun t ht => (ht₀ t ht).imp (fun a h => h.1)⟩
  · have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∃ t₀ : ℕ, 2 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
        ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a ∧
          euclidNorm (a - M.a0) ≤ ρs / ((j : ℝ) + 1) := by
      rw [ae_all_iff]; intro j
      exact hfin _ (by positivity)
        (div_le_self hρs.le (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith))
    filter_upwards [hall, hIcc] with ω hω hωI ε hε
    obtain ⟨j, hj⟩ := exists_nat_gt (ρs / ε)
    obtain ⟨t₀, ht₀2, ht₀⟩ := hω j
    refine ⟨t₀, fun t ht a ha => ?_⟩
    obtain ⟨b, hb, hbd⟩ := ht₀ t ht
    have hab : a = b := hU (fun s => p s ω) (fun s => d s ω) t (le_trans ht₀2 ht)
      (fun i hi => hωI i (Finset.mem_Icc.mp hi).1)
      (by show p 1 ω ≠ p 2 ω; rw [hp1, hp2]; exact h12) ha hb
    rw [hab]
    have hj' : ρs < j * ε := (div_lt_iff₀ hε).mp hj
    calc euclidNorm (b - M.a0) ≤ ρs / ((j : ℝ) + 1) := hbd
      _ < ε := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hfm, hfi, hf⟩ := htail ρs hρs le_rfl
    exact lt_of_le_of_lt (lintegral_mono_ae hf) hfi
  -- the mean-square rate
  obtain ⟨K, hK, hKr⟩ := hrate L hL
  -- clamped prices (equal to p on the a.s. set) for measurability
  set pc : ℕ → Ω → ℝ := fun t ω => if t = 0 then p 0 ω else B38Prob.clamp M (p t ω) with hpcd
  have hpc_eq : ∀ ω, (∀ t : ℕ, 1 ≤ t → p t ω ∈ Set.Icc M.pl M.ph) →
      (fun s => pc s ω) = (fun s => p s ω) := by
    intro ω hω; funext s
    simp only [hpcd]
    split_ifs with hs
    · rw [hs]
    · exact B38Prob.clamp_eq M _ (hω s (Nat.one_le_iff_ne_zero.mpr hs))
  have hpcI : ∀ ω (i : ℕ), 1 ≤ i → pc i ω = B38Prob.clamp M (p i ω) := by
    intro ω i hi; simp only [hpcd, if_neg (show i ≠ 0 by omega)]
  have hpcmem : ∀ ω (i : ℕ), 1 ≤ i → pc i ω ∈ Set.Icc M.pl M.ph := fun ω i hi => by
    rw [hpcI ω i hi]; exact B38Prob.clamp_mem M _
  have hTeq : ∀ ω ρ, (∀ t : ℕ, 1 ≤ t → p t ω ∈ Set.Icc M.pl M.ph) →
      Tρ M pc d ρ ω = Tρ M p d ρ ω := by
    intro ω ρ hω; unfold Tρ; rw [hpc_eq ω hω]
  have hmeq : ∀ ω t, (∀ t : ℕ, 1 ≤ t → p t ω ∈ Set.Icc M.pl M.ph) →
      mqle M pc d t ω = mqle M p d t ω := by
    intro ω t hω; unfold mqle; rw [hpc_eq ω hω]
  set Kset : Set (ℝ × ℝ) := {a | euclidNorm (a - M.a0) ≤ ρs} with hKd
  have hKc : IsCompact Kset := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_le (euclid_cont.comp (continuous_id.sub continuous_const)) continuous_const
    · refine (Metric.isBounded_closedBall (x := M.a0) (r := ρs)).subset (fun a ha => ?_)
      rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have := B38M1b.euclid_le (a - M.a0) ρs ha
      simp only [Prod.fst_sub, Prod.snd_sub] at this
      exact max_le this.1 this.2
  set Q : ℕ → ℝ × ℝ → Ω → ℝ × ℝ := fun s a ω =>
    qscore M (fun i => pc i ω) (fun i => d i ω) s a with hQd
  set F : ℕ → ℝ × ℝ → Ω → ℝ := fun s a ω => |(Q s a ω).1| + |(Q s a ω).2| with hFd
  have hF0 : ∀ s ω a, a ∈ Kset →
      (F s a ω = 0 ↔ IsMQLE M (fun i => pc i ω) (fun i => d i ω) s a) := by
    intro s ω a ha
    have hpos : ∀ i ∈ Finset.Icc 1 s, 0 ≤ a.1 + a.2 * pc i ω := fun i hi =>
      le_trans (by positivity) (hdom a ha _ (hpcmem ω i (Finset.mem_Icc.mp hi).1))
    have h1 := abs_nonneg (Q s a ω).1
    have h2 := abs_nonneg (Q s a ω).2
    constructor
    · intro h
      have e1 : (Q s a ω).1 = 0 := abs_eq_zero.mp (by simp only [hFd] at h; linarith)
      have e2 : (Q s a ω).2 = 0 := abs_eq_zero.mp (by simp only [hFd] at h; linarith)
      exact ⟨hpos, Prod.ext (by simpa using e1) (by simpa using e2)⟩
    · rintro ⟨_, h⟩
      have : Q s a ω = 0 := h
      simp only [hFd, this, Prod.fst_zero, Prod.snd_zero, abs_zero, add_zero]
  have hQ1 : ∀ s a ω, (Q s a ω).1 = ∑ i ∈ Finset.Icc 1 s,
      B38App.W M (a.1 + a.2 * pc i ω) * (d i ω - M.h (a.1 + a.2 * pc i ω)) := by
    intro s a ω; simp only [hQd, qscore, Prod.fst_sum, B38App.W]
  have hQ2 : ∀ s a ω, (Q s a ω).2 = ∑ i ∈ Finset.Icc 1 s,
      B38App.W M (a.1 + a.2 * pc i ω) * (d i ω - M.h (a.1 + a.2 * pc i ω)) * pc i ω := by
    intro s a ω; simp only [hQd, qscore, Prod.snd_sum, B38App.W]
  have hWc : ∀ q ∈ Set.Icc M.pl M.ph,
      ContinuousOn (fun a : ℝ × ℝ => B38App.W M (a.1 + a.2 * q)) Kset := by
    intro q hq
    exact (B38App.W_contDiffOn M).continuousOn.comp
      (continuous_fst.add (continuous_snd.mul continuous_const)).continuousOn
      (fun a ha => Set.mem_Ioi.mpr (lt_of_lt_of_le (by positivity) (hdom a ha q hq)))
  have hhc : ∀ q ∈ Set.Icc M.pl M.ph,
      ContinuousOn (fun a : ℝ × ℝ => M.h (a.1 + a.2 * q)) Kset := by
    intro q hq
    exact M.h_contDiffOn.continuousOn.comp
      (continuous_fst.add (continuous_snd.mul continuous_const)).continuousOn
      (fun a ha => Set.mem_Ici.mpr (le_trans (by positivity) (hdom a ha q hq)))
  have hFc : ∀ s ω, ContinuousOn (fun a => F s a ω) Kset := by
    intro s ω
    simp only [hFd, hQ1, hQ2]
    refine ContinuousOn.add (ContinuousOn.abs ?_) (ContinuousOn.abs ?_) <;>
      refine continuousOn_finset_sum _ (fun i hi => ?_)
    · exact (hWc _ (hpcmem ω i (Finset.mem_Icc.mp hi).1)).mul
        (continuousOn_const.sub (hhc _ (hpcmem ω i (Finset.mem_Icc.mp hi).1)))
    · exact ((hWc _ (hpcmem ω i (Finset.mem_Icc.mp hi).1)).mul
        (continuousOn_const.sub (hhc _ (hpcmem ω i (Finset.mem_Icc.mp hi).1)))).mul
        continuousOn_const
  have hpm : ∀ i, 1 ≤ i → Measurable (p i) := fun i hi =>
    (hD.price_meas i hi).measurable.mono (ℱ.le _) le_rfl
  have hdm : ∀ i, 1 ≤ i → Measurable (d i) := fun i hi =>
    (hD.demand_meas i hi).measurable.mono (ℱ.le _) le_rfl
  have hpcm : ∀ i, 1 ≤ i → Measurable (pc i) := fun i hi => by
    have : pc i = B38Prob.clamp M ∘ p i := by
      funext ω; simp only [Function.comp, hpcI ω i hi]
    rw [this]; exact (B38Prob.clamp_cont M).measurable.comp (hpm i hi)
  have hWm : ∀ a ∈ Kset, ∀ i, 1 ≤ i → Measurable (fun ω => B38App.W M (a.1 + a.2 * pc i ω)) := by
    intro a ha i hi
    have hc : Continuous (fun q => B38App.W M (a.1 + a.2 * B38Prob.clamp M q)) :=
      (B38App.W_contDiffOn M).continuousOn.comp_continuous
        (continuous_const.add (continuous_const.mul (B38Prob.clamp_cont M)))
        (fun q => Set.mem_Ioi.mpr (lt_of_lt_of_le (by positivity)
          (hdom a ha _ (B38Prob.clamp_mem M q))))
    have : (fun ω => B38App.W M (a.1 + a.2 * pc i ω)) =
        (fun q => B38App.W M (a.1 + a.2 * B38Prob.clamp M q)) ∘ p i := by
      funext ω; simp only [Function.comp, hpcI ω i hi]
    rw [this]; exact hc.measurable.comp (hpm i hi)
  have hhm : ∀ a ∈ Kset, ∀ i, 1 ≤ i → Measurable (fun ω => M.h (a.1 + a.2 * pc i ω)) := by
    intro a ha i hi
    have hc : Continuous (fun q => M.h (a.1 + a.2 * B38Prob.clamp M q)) :=
      M.h_contDiffOn.continuousOn.comp_continuous
        (continuous_const.add (continuous_const.mul (B38Prob.clamp_cont M)))
        (fun q => Set.mem_Ici.mpr (le_trans (by positivity)
          (hdom a ha _ (B38Prob.clamp_mem M q))))
    have : (fun ω => M.h (a.1 + a.2 * pc i ω)) =
        (fun q => M.h (a.1 + a.2 * B38Prob.clamp M q)) ∘ p i := by
      funext ω; simp only [Function.comp, hpcI ω i hi]
    rw [this]; exact hc.measurable.comp (hpm i hi)
  have hFm : ∀ s, ∀ a ∈ Kset, Measurable (F s a) := by
    intro s a ha
    show Measurable (fun ω => F s a ω)
    simp only [hFd, hQ1, hQ2]
    refine Measurable.add (continuous_abs.measurable.comp ?_)
      (continuous_abs.measurable.comp ?_) <;>
      refine Finset.measurable_sum _ (fun i hi => ?_)
    · have hi1 := (Finset.mem_Icc.mp hi).1
      exact (hWm a ha i hi1).mul ((hdm i hi1).sub (hhm a ha i hi1))
    · have hi1 := (Finset.mem_Icc.mp hi).1
      exact ((hWm a ha i hi1).mul ((hdm i hi1).sub (hhm a ha i hi1))).mul (hpcm i hi1)
  have hUc : ∀ ω (s : ℕ), 2 ≤ s → ∀ a b, IsMQLE M (fun i => pc i ω) (fun i => d i ω) s a →
      IsMQLE M (fun i => pc i ω) (fun i => d i ω) s b → a = b := by
    intro ω s hs a b ha hb
    refine hU (fun i => pc i ω) (fun i => d i ω) s hs
      (fun i hi => hpcmem ω i (Finset.mem_Icc.mp hi).1) ?_ ha hb
    show pc 1 ω ≠ pc 2 ω
    rw [hpcI ω 1 le_rfl, hpcI ω 2 (by norm_num), hp1, hp2, B38Prob.clamp_eq M _ hp1I,
      B38Prob.clamp_eq M _ hp2I]
    exact h12
  have hTiff : ∀ ω (t : ℕ), 1 ≤ t → (Tρ M pc d ρs ω < (t : ℕ∞) ↔
      ∀ k : ℕ, ∃ a ∈ Kset, F (k + t) a ω = 0) := by
    intro ω t ht
    rw [B38Gen.Tρ_lt_iff M pc d ρs ω t ht]
    constructor
    · intro h k
      obtain ⟨a, ha, had⟩ := h (k + t) (by omega)
      exact ⟨a, had, (hF0 _ ω a had).mpr ha⟩
    · intro h s hs
      obtain ⟨a, haK, ha0⟩ := h (s - t)
      rw [Nat.sub_add_cancel hs] at ha0
      exact ⟨a, (hF0 s ω a haK).mp ha0, haK⟩
  refine ⟨K * (1 + A1 + A2) * (1 / Real.log 2 + 1), by positivity, fun t ht => ?_⟩
  -- measurability of the integrand
  set Et : Set Ω := ⋂ k : ℕ, {ω | ∃ a ∈ Kset, F (k + t) a ω = 0} with hEtd
  have hEt : MeasurableSet Et :=
    MeasurableSet.iInter (fun k => B38Gen.zero_set_meas Kset hKc (F (k + t)) (hFm (k + t))
      (hFc (k + t)))
  have hsel := B38Gen.sel_meas Kset hKc (F t) (hFm t) (hFc t)
    (fun ω a ha b hb h0a h0b => hUc ω t ht a b ((hF0 t ω a ha).mp h0a) ((hF0 t ω b hb).mp h0b))
    (fun ω => mqle M pc d t ω)
    (fun ω ⟨a, haK, ha0⟩ => by
      have hq := (hF0 t ω a haK).mp ha0
      have hm := mqle_spec M pc d t ω ⟨a, hq⟩
      have := hUc ω t ht _ _ hm hq
      rw [this]; exact ⟨haK, ha0⟩) M.a0
  set Gs : Ω → ℝ × ℝ := fun ω => if ∃ a ∈ Kset, F t a ω = 0 then mqle M pc d t ω else M.a0
    with hGsd
  have hIpc : (fun ω => if (t : ℕ∞) > Tρ M pc d ρs ω then
      euclidNorm (mqle M pc d t ω - M.a0) ^ 2 else 0) =
      Et.indicator (fun ω => euclidNorm (Gs ω - M.a0) ^ 2) := by
    funext ω
    have hiff := hTiff ω t (by omega)
    by_cases hT : (t : ℕ∞) > Tρ M pc d ρs ω
    · have hmem : ω ∈ Et := by
        simp only [hEtd, Set.mem_iInter, Set.mem_setOf_eq]; exact hiff.mp hT
      have h0 : ∃ a ∈ Kset, F t a ω = 0 := by
        have := hiff.mp hT 0; rwa [zero_add] at this
      rw [if_pos hT, Set.indicator_of_mem hmem]
      simp only [hGsd, if_pos h0]
    · have hmem : ω ∉ Et := by
        simp only [hEtd, Set.mem_iInter, Set.mem_setOf_eq]; exact fun h => hT (hiff.mpr h)
      rw [if_neg hT, Set.indicator_of_notMem hmem]
  have hIm : Measurable (fun ω => if (t : ℕ∞) > Tρ M pc d ρs ω then
      euclidNorm (mqle M pc d t ω - M.a0) ^ 2 else 0) := by
    rw [hIpc]
    exact (((euclid_cont.measurable.comp (hsel.sub measurable_const)).pow_const 2)).indicator hEt
  have hae : (fun ω => if (t : ℕ∞) > Tρ M p d ρs ω then
      euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) =ᵐ[P]
      (fun ω => if (t : ℕ∞) > Tρ M pc d ρs ω then
      euclidNorm (mqle M pc d t ω - M.a0) ^ 2 else 0) := by
    filter_upwards [hIcc] with ω hω
    rw [hTeq ω ρs hω, hmeq ω t hω]
  -- pointwise bound
  have htα : 0 < (t : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_cast; omega) α
  have hbound : ∀ᵐ ω ∂P, (if (t : ℕ∞) > Tρ M p d ρs ω then
      euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) ≤
      K / (t : ℝ) ^ α * (1 + Y1 t ω + Y2 t ω) := by
    filter_upwards [hIcc, hlam, hcb] with ω hω hlω hcω
    have hY1 := B38LW.Gp_nonneg η gc t ω
    have hY2 := B38LW.Gp_nonneg η2 gc2 t ω
    by_cases hT : (t : ℕ∞) > Tρ M p d ρs ω
    · rw [if_pos hT]
      obtain ⟨b, hb, hbd⟩ := (B38Gen.Tρ_lt_iff M p d ρs ω t (by omega)).mp hT t le_rfl
      have hm := mqle_spec M p d t ω ⟨b, hb⟩
      have hmb : mqle M p d t ω = b := hU (fun s => p s ω) (fun s => d s ω) t ht
        (fun i hi => hω i (Finset.mem_Icc.mp hi).1)
        (by show p 1 ω ≠ p 2 ω; rw [hp1, hp2]; exact h12) hm hb
      obtain ⟨hz1, hz2⟩ := hZ ω hω t
      have hk := hKr (fun i => p i ω) (fun i => d i ω)
        (fun i => P[fun ω => |η i ω| | ℱ (i - 1)] ω) t α ht
        (fun i hi => hω i (Finset.mem_Icc.mp hi).1)
        (fun i hi => hcω i (Finset.mem_Icc.mp hi).1) (hlω t ht) _ hm
        (by rw [hmb]; exact le_trans hbd (min_le_left _ _))
      rw [div_mul_eq_mul_div, le_div_iff₀ htα]
      nlinarith
    · rw [if_neg hT]; positivity
  have hbi : Integrable (fun ω => K / (t : ℝ) ^ α * (1 + Y1 t ω + Y2 t ω)) P :=
    (((integrable_const 1).add (B38LW.Gp_int lw1 t)).add (B38LW.Gp_int lw2 t)).const_mul _
  have hint : Integrable (fun ω => if (t : ℕ∞) > Tρ M p d ρs ω then
      euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) P := by
    refine Integrable.mono' hbi (hIm.aestronglyMeasurable.congr hae.symm) ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    exact hω
  refine ⟨hint, ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have hE1 := hint1 t (by omega)
  have hE2 := hint2 t (by omega)
  have hbint : ∫ ω, K / (t : ℝ) ^ α * (1 + Y1 t ω + Y2 t ω) ∂P =
      K / (t : ℝ) ^ α * (1 + ∫ ω, Y1 t ω ∂P + ∫ ω, Y2 t ω ∂P) := by
    rw [integral_const_mul]
    congr 1
    have i1 : Integrable (fun ω => (1 : ℝ) + Y1 t ω) P :=
      (integrable_const 1).add (B38LW.Gp_int lw1 t)
    have e1 : ∫ ω, (1 + Y1 t ω + Y2 t ω) ∂P = ∫ ω, (1 + Y1 t ω) ∂P + ∫ ω, Y2 t ω ∂P :=
      integral_add i1 (B38LW.Gp_int lw2 t)
    have e2 : ∫ ω, (1 + Y1 t ω) ∂P = ∫ ω, (1 : ℝ) ∂P + ∫ ω, Y1 t ω ∂P :=
      integral_add (integrable_const 1) (B38LW.Gp_int lw1 t)
    rw [e1, e2]; simp
  have h1lt : 1 + Real.log t ≤ (1 / Real.log 2 + 1) * Real.log t := by
    have : 1 ≤ Real.log t / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    have e : (1 / Real.log 2 + 1) * Real.log t = Real.log t / Real.log 2 + Real.log t := by ring
    linarith
  have hsum : 1 + ∫ ω, Y1 t ω ∂P + ∫ ω, Y2 t ω ∂P ≤
      (1 + A1 + A2) * ((1 / Real.log 2 + 1) * Real.log t) := by
    have hl0 : 0 ≤ Real.log t := le_trans hl2.le hlt
    have : 1 + ∫ ω, Y1 t ω ∂P + ∫ ω, Y2 t ω ∂P ≤ (1 + A1 + A2) * (1 + Real.log t) := by
      nlinarith
    exact le_trans this (mul_le_mul_of_nonneg_left h1lt (by positivity))
  calc ∫ ω, (if (t : ℕ∞) > Tρ M p d ρs ω then
          euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) ∂P
      ≤ ∫ ω, K / (t : ℝ) ^ α * (1 + Y1 t ω + Y2 t ω) ∂P := integral_mono_ae hint hbi hbound
    _ = K / (t : ℝ) ^ α * (1 + ∫ ω, Y1 t ω ∂P + ∫ ω, Y2 t ω ∂P) := hbint
    _ ≤ K / (t : ℝ) ^ α * ((1 + A1 + A2) * ((1 / Real.log 2 + 1) * Real.log t)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = K * (1 + A1 + A2) * (1 / Real.log 2 + 1) * (Real.log t / (t : ℝ) ^ α) := by ring

end B38Fin
section C1sec
open KeskinZeevi.SufficientConditions CVPricing.Regret

namespace B38C1

theorem J_eq (p : ℕ → ℝ) (t : ℕ) :
    infoMetricOf p t = (∑ s ∈ Finset.Icc 1 t, p s ^ 2) - (∑ s ∈ Finset.Icc 1 t, p s) ^ 2 / t := by
  unfold infoMetricOf avgPriceOf
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have htR : (t : ℝ) ≠ 0 := by positivity
  have hcard : ((Finset.Icc 1 t).card : ℝ) = t := by simp
  have : ∀ s ∈ Finset.Icc 1 t, (p s - (∑ s ∈ Finset.Icc 1 t, p s) / t) ^ 2 =
      p s ^ 2 - 2 * ((∑ s ∈ Finset.Icc 1 t, p s) / t) * p s
        + ((∑ s ∈ Finset.Icc 1 t, p s) / t) ^ 2 := fun s _ => by ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard]
  field_simp
  ring

theorem J_succ (p : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    infoMetricOf p (t + 1) = infoMetricOf p t
      + (t / (t + 1 : ℝ)) * (p (t + 1) - avgPriceOf p t) ^ 2 := by
  rw [J_eq, J_eq, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  unfold avgPriceOf
  have htR : (t : ℝ) ≠ 0 := by positivity
  have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem far_inc (p : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) (hF : FarPrice p t) :
    (p 1 - p 2) ^ 2 / 8 ≤ (t / (t + 1 : ℝ)) * (p (t + 1) - avgPriceOf p t) ^ 2 := by
  obtain ⟨-, hab⟩ := hF
  set A := avgPriceOf p t
  have h1 : |p 1 - p 2| / 2 ≤ |p (t + 1) - A| := by
    rw [hab]
    have : |p 1 - p 2| ≤ |p 1 - A| + |p 2 - A| := by
      calc |p 1 - p 2| = |(p 1 - A) - (p 2 - A)| := by ring_nf
        _ ≤ |p 1 - A| + |p 2 - A| := abs_sub _ _
    have := max_le_iff.mp (le_refl (max |p 1 - A| |p 2 - A|))
    rcases le_total |p 1 - A| |p 2 - A| with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (p 1 - p 2) ^ 2 / 4 ≤ (p (t + 1) - A) ^ 2 := by
    have h0 : 0 ≤ |p 1 - p 2| / 2 := by positivity
    have := mul_le_mul h1 h1 h0 (le_trans h0 h1)
    rw [← sq_abs (p (t + 1) - A), ← sq_abs (p 1 - p 2)]
    nlinarith
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hq : (1 / 2 : ℝ) ≤ t / (t + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  have hsq : 0 ≤ (p 1 - p 2) ^ 2 / 4 := by positivity
  calc (p 1 - p 2) ^ 2 / 8 = (1 / 2) * ((p 1 - p 2) ^ 2 / 4) := by ring
    _ ≤ (t / (t + 1 : ℝ)) * (p (t + 1) - A) ^ 2 :=
        mul_le_mul hq h2 hsq (by positivity)

theorem taboo_inc (α c : ℝ) (hα0 : 0 < α) (hc : 0 < c) (p : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hx : p (t + 1) ∉ tabooInterval α c p t) :
    c * (((t : ℝ) + 1) ^ α - (t : ℝ) ^ α) ≤ (t / (t + 1 : ℝ)) * (p (t + 1) - avgPriceOf p t) ^ 2 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hmono : (t : ℝ) ^ α ≤ ((t : ℝ) + 1) ^ α :=
    Real.rpow_le_rpow (by linarith) (by linarith) hα0.le
  have harg : 0 ≤ c * (((t : ℝ) + 1) ^ α - (t : ℝ) ^ α) * (((t : ℝ) + 1) / t) := by
    have : 0 ≤ ((t : ℝ) + 1) ^ α - (t : ℝ) ^ α := by linarith
    positivity
  have hw0 : 0 ≤ tabooHalfWidth α c t := Real.sqrt_nonneg _
  have hw : tabooHalfWidth α c t ≤ |p (t + 1) - avgPriceOf p t| := by
    unfold tabooInterval at hx
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hx
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have hsq : tabooHalfWidth α c t ^ 2 ≤ (p (t + 1) - avgPriceOf p t) ^ 2 := by
    rw [← sq_abs (p (t + 1) - avgPriceOf p t)]
    exact pow_le_pow_left₀ hw0 hw 2
  have hww : tabooHalfWidth α c t ^ 2 =
      c * (((t : ℝ) + 1) ^ α - (t : ℝ) ^ α) * (((t : ℝ) + 1) / t) := by
    unfold tabooHalfWidth; rw [Real.sq_sqrt harg]
  have hq : 0 ≤ (t / (t + 1 : ℝ)) := by positivity
  calc c * (((t : ℝ) + 1) ^ α - (t : ℝ) ^ α)
      = (t / (t + 1 : ℝ)) * (c * (((t : ℝ) + 1) ^ α - (t : ℝ) ^ α) * (((t : ℝ) + 1) / t)) := by
        field_simp
    _ ≤ (t / (t + 1 : ℝ)) * (p (t + 1) - avgPriceOf p t) ^ 2 := by
        rw [← hww]; exact mul_le_mul_of_nonneg_left hsq hq

theorem rpow_step_le_one (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (t : ℕ) :
    ((t : ℝ) + 1) ^ α - (t : ℝ) ^ α ≤ 1 := by
  have := Real.rpow_add_le_add_rpow (Nat.cast_nonneg t) zero_le_one hα0.le hα1.le
  simp at this
  linarith

theorem cvp_infoMetric_lower (M : CVPricing.Regret.Model) (α c : ℝ) (p d : ℕ → ℝ) (h : IsCVPPath M α c p d) :
    ∀ t : ℕ, 2 ≤ t → min c ((p 1 - p 2) ^ 2 / 8) * (t : ℝ) ^ α ≤ infoMetricOf p t := by
  obtain ⟨-, -, h12, ⟨hα0, hα1⟩, hc, -, hstep⟩ := h
  have hd : 0 < (p 1 - p 2) ^ 2 := by
    have : p 1 - p 2 ≠ 0 := sub_ne_zero.mpr h12
    positivity
  set κ := min c ((p 1 - p 2) ^ 2 / 8)
  have hκc : κ ≤ c := min_le_left _ _
  have hκd : κ ≤ (p 1 - p 2) ^ 2 / 8 := min_le_right _ _
  have hκ0 : 0 < κ := lt_min hc (by positivity)
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    have h2 : infoMetricOf p 2 = (p 1 - p 2) ^ 2 / 2 := by
      rw [J_eq]
      simp [Finset.sum_Icc_succ_top]
      ring
    rw [h2]
    have : (2 : ℝ) ^ α ≤ 2 := by
      calc (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
        _ = 2 := Real.rpow_one 2
    push_cast
    nlinarith
  | succ n hn ih =>
    have hn1 : 1 ≤ n := by omega
    have hdiff := rpow_step_le_one α hα0 hα1 n
    have hmono : (n : ℝ) ^ α ≤ ((n : ℝ) + 1) ^ α :=
      Real.rpow_le_rpow (by positivity) (by linarith) hα0.le
    rw [J_succ p n hn1]
    push_cast
    have far : FarPrice p n → κ * ((n : ℝ) + 1) ^ α ≤
        infoMetricOf p n + (n / (n + 1 : ℝ)) * (p (n + 1) - avgPriceOf p n) ^ 2 := by
      intro hF
      have := far_inc p n hn1 hF
      nlinarith
    rcases hstep n hn with ⟨-, hF⟩ | ⟨a, -, -, hF⟩ | ⟨a, -, -, hE⟩
    · exact far hF
    · exact far hF
    · rcases hE with ⟨-, -, hv⟩ | ⟨-, hm⟩
      · rw [← J_succ p n hn1]
        unfold sampleVar at hv
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        push_cast at hv
        rw [le_div_iff₀ hpos] at hv
        have hr : ((n : ℝ) + 1) ^ (α - 1) * ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ α := by
          rw [← Real.rpow_add_one hpos.ne']; ring_nf
        have : c * ((n : ℝ) + 1) ^ α ≤ infoMetricOf p (n + 1) := by
          calc c * ((n : ℝ) + 1) ^ α = c * ((n : ℝ) + 1) ^ (α - 1) * ((n : ℝ) + 1) := by
                rw [mul_assoc, hr]
            _ ≤ infoMetricOf p (n + 1) := hv
        have hpow : 0 ≤ ((n : ℝ) + 1) ^ α := by positivity
        nlinarith
      · have := taboo_inc α c hα0 hc p n hn1 hm.1.2
        have h1 : κ * (((n : ℝ) + 1) ^ α - (n : ℝ) ^ α) ≤ c * (((n : ℝ) + 1) ^ α - (n : ℝ) ^ α) :=
          mul_le_mul_of_nonneg_right hκc (by linarith)
        nlinarith


theorem prices_mem (M : CVPricing.Regret.Model) (α c : ℝ) (p d : ℕ → ℝ) (h : IsCVPPath M α c p d) :
    ∀ t : ℕ, 1 ≤ t → p t ∈ Set.Icc M.pl M.ph := by
  obtain ⟨h1, h2, -, -, -, -, hstep⟩ := h
  intro t ht
  induction t with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact h1
      · exact h2
    · rcases hstep n hn with ⟨-, hF⟩ | ⟨a, -, -, hF⟩ | ⟨a, -, -, hE⟩
      · rcases hF.1 with e | e <;> rw [e] <;> assumption
      · rcases hF.1 with e | e <;> rw [e] <;> assumption
      · rcases hE with ⟨-, hm, -⟩ | ⟨-, hm⟩
        · exact hm.1
        · exact hm.1.1

open MeasureTheory
end B38C1
end C1sec

open Matrix KeskinZeevi.SufficientConditions in
theorem CVPricing_Regret_dmeb_fisher_quad (p : ℕ → ℝ) (t : ℕ) (y : Fin 2 → ℝ) :
    y ⬝ᵥ (fisherOf p t *ᵥ y) = ∑ s ∈ Finset.Icc 1 t, (y 0 + p s * y 1) ^ 2 := by
  have h00 : fisherOf p t 0 0 = ∑ s ∈ Finset.Icc 1 t, (1 : ℝ) := by
    simp [fisherOf, Matrix.sum_apply]
  have h01 : fisherOf p t 0 1 = ∑ s ∈ Finset.Icc 1 t, p s := by
    simp [fisherOf, Matrix.sum_apply]
  have h10 : fisherOf p t 1 0 = ∑ s ∈ Finset.Icc 1 t, p s := by
    simp [fisherOf, Matrix.sum_apply]
  have h11 : fisherOf p t 1 1 = ∑ s ∈ Finset.Icc 1 t, p s ^ 2 := by
    simp [fisherOf, Matrix.sum_apply]
  simp only [dotProduct, mulVec, Fin.sum_univ_two, h00, h01, h10, h11]
  have : ∀ s, (y 0 + p s * y 1) ^ 2 = y 0 * y 0 * 1 + y 0 * y 1 * p s + y 1 * y 0 * p s
      + y 1 * y 1 * p s ^ 2 := fun s => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

open Matrix KeskinZeevi.SufficientConditions in
theorem CVPricing_Regret_dmeb_info (p : ℕ → ℝ) (t : ℕ) (ht : 0 < t) :
    (t : ℝ) * infoMetricOf p t
      = (t : ℝ) * ∑ s ∈ Finset.Icc 1 t, p s ^ 2 - (∑ s ∈ Finset.Icc 1 t, p s) ^ 2 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hcard : ∑ s ∈ Finset.Icc 1 t, (1 : ℝ) = t := by simp
  unfold infoMetricOf avgPriceOf
  set b := ∑ s ∈ Finset.Icc 1 t, p s
  have : ∀ s, (p s - b / t) ^ 2 = p s ^ 2 - 2 * (b / t) * p s + (b / t) ^ 2 * 1 :=
    fun s => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcard]
  field_simp
  ring

open Matrix KeskinZeevi.SufficientConditions in
theorem B38_eig_bounds (pl ph : ℝ) (hpl : 0 < pl) (hlh : pl < ph)
    (p : ℕ → ℝ) (t : ℕ) (ht : 2 ≤ t) (hp : ∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc pl ph)
    (h12 : p 1 ≠ p 2) :
    (⨆ y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1}, y.1 ⬝ᵥ (fisherOf p t *ᵥ y.1))
        ≤ (1 + ph ^ 2) * t ∧
      infoMetricOf p t ≤ (1 + ph ^ 2) * minRayleigh (fisherOf p t) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hcard : ∑ s ∈ Finset.Icc 1 t, (1 : ℝ) = t := by simp
  have hne : Nonempty {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1} :=
    ⟨⟨![1, 0], by simp⟩⟩
  have hsq : ∀ s ∈ Finset.Icc 1 t, p s ^ 2 ≤ ph ^ 2 := by
    intro s hs
    obtain ⟨h1, h2⟩ := hp s hs
    nlinarith
  have hc : ∑ s ∈ Finset.Icc 1 t, p s ^ 2 ≤ t * ph ^ 2 := by
    calc ∑ s ∈ Finset.Icc 1 t, p s ^ 2 ≤ ∑ s ∈ Finset.Icc 1 t, ph ^ 2 := Finset.sum_le_sum hsq
      _ = t * ph ^ 2 := by simp
  -- upper bound for each unit vector
  have hup : ∀ y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1},
      y.1 ⬝ᵥ (fisherOf p t *ᵥ y.1) ≤ (1 + ph ^ 2) * t := by
    intro y
    obtain ⟨y, hy⟩ := y
    rw [CVPricing_Regret_dmeb_fisher_quad]
    calc ∑ s ∈ Finset.Icc 1 t, (y 0 + p s * y 1) ^ 2
        ≤ ∑ s ∈ Finset.Icc 1 t, (1 + ph ^ 2) := by
          apply Finset.sum_le_sum
          intro s hs
          have h := hsq s hs
          have h' : (y 0 + p s * y 1) ^ 2 ≤ (1 + p s ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by
            nlinarith [sq_nonneg (p s * y 0 - y 1)]
          rw [hy] at h'
          linarith
      _ = (1 + ph ^ 2) * t := by simp; ring
  refine ⟨ciSup_le hup, ?_⟩
  -- lower bound
  have hlow : ∀ y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1},
      infoMetricOf p t / (1 + ph ^ 2) ≤ y.1 ⬝ᵥ (fisherOf p t *ᵥ y.1) := by
    intro y
    obtain ⟨y, hy⟩ := y
    have hQ := CVPricing_Regret_dmeb_fisher_quad p t y
    have hinfo := CVPricing_Regret_dmeb_info p t (by omega)
    simp only at hQ ⊢
    set Q := y ⬝ᵥ (fisherOf p t *ᵥ y)
    set b := ∑ s ∈ Finset.Icc 1 t, p s
    set c := ∑ s ∈ Finset.Icc 1 t, p s ^ 2
    have hQnn : 0 ≤ Q := by
      rw [hQ]; exact Finset.sum_nonneg (fun s _ => sq_nonneg _)
    have hQexp : Q = t * y 0 ^ 2 + 2 * b * y 0 * y 1 + c * y 1 ^ 2 := by
      rw [hQ]
      have : ∀ s, (y 0 + p s * y 1) ^ 2 = y 0 ^ 2 * 1 + (2 * y 0 * y 1) * p s
          + y 1 ^ 2 * p s ^ 2 := fun s => by ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hcard]
      ring
    have hkey : Q * (t + c) - (t * c - b ^ 2) * (y 0 ^ 2 + y 1 ^ 2)
        = (t * y 0 + b * y 1) ^ 2 + (b * y 0 + c * y 1) ^ 2 := by
      rw [hQexp]; ring
    rw [hy, mul_one] at hkey
    have h1 : (t : ℝ) * infoMetricOf p t ≤ Q * (t + c) := by
      nlinarith [sq_nonneg (t * y 0 + b * y 1), sq_nonneg (b * y 0 + c * y 1)]
    have h2 : Q * (t + c) ≤ Q * (t * (1 + ph ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hQnn
      nlinarith
    have h3 : infoMetricOf p t ≤ Q * (1 + ph ^ 2) := by
      have : (t : ℝ) * infoMetricOf p t ≤ t * (Q * (1 + ph ^ 2)) := by nlinarith
      exact le_of_mul_le_mul_left this htR
    rw [div_le_iff₀ (by positivity)]
    exact h3
  have := le_ciInf hlow
  unfold minRayleigh
  rw [div_le_iff₀ (by positivity)] at this
  linarith

open MeasureTheory KeskinZeevi.SufficientConditions CVPricing.Regret in
theorem solution (M : CVPricing.Regret.Model) (hU : MQLEUnique M) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d) (α c p₁ p₂ : ℝ) (hα : 1 / 2 < α)
    (hp₁ : ∀ ω, p 1 ω = p₁) (hp₂ : ∀ ω, p 2 ω = p₂)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω)) :
    (∀ᵐ ω ∂P, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a) ∧
    (∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ a,
        IsMQLE M (fun s => p s ω) (fun s => d s ω) t a → euclidNorm (a - M.a0) < ε) ∧
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      (∫⁻ ω, ((Tρ M p d ρ₀ ω : ENNReal)) ^ (1 / 2 : ℝ) ∂P) < ⊤ ∧
      ∃ K : ℝ, 0 < K ∧ ∀ t : ℕ, 2 ≤ t →
        Integrable (fun ω => if (t : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) P ∧
        ∫ ω, (if (t : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d t ω - M.a0) ^ 2 else 0) ∂P
          ≤ K * (Real.log t / (t : ℝ) ^ α) := by
  obtain ⟨ω₀, hω₀⟩ := hCVP.exists
  have h12 : p₁ ≠ p₂ := by
    have := hω₀.2.2.1; simpa [hp₁, hp₂] using this
  have hc : 0 < c := hω₀.2.2.2.2.1
  have hd : 0 < (p₁ - p₂) ^ 2 := by
    have : p₁ - p₂ ≠ 0 := sub_ne_zero.mpr h12
    positivity
  have hph : 0 < 1 + M.ph ^ 2 := by positivity
  refine B38Fin.main M hU P ℱ p d hD α (min c ((p₁ - p₂) ^ 2 / 8) / (1 + M.ph ^ 2)) p₁ p₂ hα
    (div_pos (lt_min hc (by positivity)) hph) h12 hp₁ hp₂ ?_ ?_
  · filter_upwards [hCVP] with ω hω
    exact B38C1.prices_mem M α c _ _ hω
  · filter_upwards [hCVP] with ω hω t ht
    have hJ := B38C1.cvp_infoMetric_lower M α c _ _ hω t ht
    have hE := (B38_eig_bounds M.pl M.ph M.pl_pos M.pl_lt_ph (fun s => p s ω) t ht
      (fun i hi => B38C1.prices_mem M α c _ _ hω i (Finset.mem_Icc.mp hi).1) hω.2.2.1).2
    simp only [hp₁, hp₂] at hJ
    rw [div_mul_eq_mul_div, div_le_iff₀ hph]
    nlinarith
