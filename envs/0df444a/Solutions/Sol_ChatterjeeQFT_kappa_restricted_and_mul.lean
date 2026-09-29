-- Prove2me | solution 1 for ChatterjeeQFT.kappa_restricted_and_mul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:17:08.922986+00:00
-- url     : https://prove2.me/submissions/2cbf6597-e995-4583-8094-8def70225d50

import Mathlib
import Definitions.Def_ChatterjeeQFT_SL2C

open Matrix
open scoped ComplexOrder
open ChatterjeeQFT

theorem W7b_ChatterjeeQFT_det_herm (x : Fin 4 → ℝ) :
    (hermOfVec x).det = ((minkowskiSq x : ℝ) : ℂ) := by
  rw [hermOfVec, Matrix.det_fin_two_of]
  simp only [minkowskiSq, minkowskiInner]
  push_cast
  linear_combination ((x 2 : ℂ)) ^ 2 * Complex.I_sq

theorem W7b_ChatterjeeQFT_hdiv (z : ℂ) : (z / (2 * Complex.I)).re = z.im / 2 := by
  rw [div_mul_eq_div_div, Complex.div_I]
  simp

theorem W7b_ChatterjeeQFT_vec_herm (x : Fin 4 → ℝ) : vecOfHerm (hermOfVec x) = x := by
  ext i
  fin_cases i
  · show ((hermOfVec x 0 0 + hermOfVec x 1 1) / 2).re = x 0
    simp [hermOfVec]
    try ring
  · show ((hermOfVec x 0 1 + hermOfVec x 1 0) / 2).re = x 1
    simp [hermOfVec]
    try ring
  · show ((hermOfVec x 1 0 - hermOfVec x 0 1) / (2 * Complex.I)).re = x 2
    rw [W7b_ChatterjeeQFT_hdiv]
    simp [hermOfVec]
    try ring
  · show ((hermOfVec x 0 0 - hermOfVec x 1 1) / 2).re = x 3
    simp [hermOfVec]
    try ring

theorem W7b_ChatterjeeQFT_herm_round (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.IsHermitian) :
    hermOfVec (vecOfHerm H) = H := by
  have e00 := hH.apply 0 0
  have e11 := hH.apply 1 1
  have e10 := hH.apply 1 0
  have i00 : (H 0 0).im = 0 := by
    have := congrArg Complex.im e00
    simp at this
    linarith
  have i11 : (H 1 1).im = 0 := by
    have := congrArg Complex.im e11
    simp at this
    linarith
  have r10 : (H 1 0).re = (H 0 1).re := by
    have := congrArg Complex.re e10
    simp at this
    linarith
  have m10 : (H 1 0).im = -(H 0 1).im := by
    have := congrArg Complex.im e10
    simp at this
    linarith
  have hv0 : vecOfHerm H 0 = ((H 0 0).re + (H 1 1).re) / 2 := by
    show ((H 0 0 + H 1 1) / 2).re = _
    simp
  have hv1 : vecOfHerm H 1 = ((H 0 1).re + (H 1 0).re) / 2 := by
    show ((H 0 1 + H 1 0) / 2).re = _
    simp
  have hv2 : vecOfHerm H 2 = ((H 1 0).im - (H 0 1).im) / 2 := by
    show ((H 1 0 - H 0 1) / (2 * Complex.I)).re = _
    rw [W7b_ChatterjeeQFT_hdiv]
    simp
  have hv3 : vecOfHerm H 3 = ((H 0 0).re - (H 1 1).re) / 2 := by
    show ((H 0 0 - H 1 1) / 2).re = _
    simp
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hermOfVec, hv0, hv1, hv2, hv3] <;> linarith

theorem W7b_ChatterjeeQFT_hermOfVec_det_bijection :
    (∀ x : Fin 4 → ℝ, (hermOfVec x).det = ((minkowskiSq x : ℝ) : ℂ)) ∧
      (∀ x : Fin 4 → ℝ, vecOfHerm (hermOfVec x) = x) ∧
      (∀ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian → hermOfVec (vecOfHerm H) = H) :=
  ⟨W7b_ChatterjeeQFT_det_herm, W7b_ChatterjeeQFT_vec_herm, W7b_ChatterjeeQFT_herm_round⟩

theorem W7b_ChatterjeeQFT_herm_isHerm (x : Fin 4 → ℝ) : (hermOfVec x).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfVec, Matrix.conjTranspose_apply] <;> ring


theorem W7b_ChatterjeeQFT_herm_kappa (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    hermOfVec (kappa A x) = A * hermOfVec x * Aᴴ :=
  W7b_ChatterjeeQFT_herm_round _
    (isHermitian_mul_mul_conjTranspose A (W7b_ChatterjeeQFT_herm_isHerm x))

theorem W7b_ChatterjeeQFT_kappa_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    kappa (A * B) x = kappa A (kappa B x) := by
  show vecOfHerm (A * B * hermOfVec x * (A * B)ᴴ) = vecOfHerm (A * hermOfVec (kappa B x) * Aᴴ)
  rw [W7b_ChatterjeeQFT_herm_kappa B x]
  congr 1
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem W7b_ChatterjeeQFT_herm_add (x y : Fin 4 → ℝ) :
    hermOfVec (x + y) = hermOfVec x + hermOfVec y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hermOfVec] <;> ring

theorem W7b_ChatterjeeQFT_herm_smul (r : ℝ) (x : Fin 4 → ℝ) :
    hermOfVec (r • x) = (r : ℂ) • hermOfVec x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hermOfVec] <;> ring

theorem W7b_ChatterjeeQFT_vec_add (H K : Matrix (Fin 2) (Fin 2) ℂ) :
    vecOfHerm (H + K) = vecOfHerm H + vecOfHerm K := by
  ext i; fin_cases i
  · show ((H 0 0 + K 0 0 + (H 1 1 + K 1 1)) / 2).re = ((H 0 0 + H 1 1) / 2).re + ((K 0 0 + K 1 1) / 2).re
    rw [← Complex.add_re]; ring_nf
  · show ((H 0 1 + K 0 1 + (H 1 0 + K 1 0)) / 2).re = ((H 0 1 + H 1 0) / 2).re + ((K 0 1 + K 1 0) / 2).re
    rw [← Complex.add_re]; ring_nf
  · show ((H 1 0 + K 1 0 - (H 0 1 + K 0 1)) / (2 * Complex.I)).re =
      ((H 1 0 - H 0 1) / (2 * Complex.I)).re + ((K 1 0 - K 0 1) / (2 * Complex.I)).re
    rw [← Complex.add_re]; ring_nf
  · show ((H 0 0 + K 0 0 - (H 1 1 + K 1 1)) / 2).re = ((H 0 0 - H 1 1) / 2).re + ((K 0 0 - K 1 1) / 2).re
    rw [← Complex.add_re]; ring_nf

theorem W7b_ChatterjeeQFT_vec_smul (r : ℝ) (H : Matrix (Fin 2) (Fin 2) ℂ) :
    vecOfHerm ((r : ℂ) • H) = r • vecOfHerm H := by
  ext i; fin_cases i
  · show (((r : ℂ) * H 0 0 + (r : ℂ) * H 1 1) / 2).re = r * ((H 0 0 + H 1 1) / 2).re
    rw [← Complex.re_ofReal_mul]; ring_nf
  · show (((r : ℂ) * H 0 1 + (r : ℂ) * H 1 0) / 2).re = r * ((H 0 1 + H 1 0) / 2).re
    rw [← Complex.re_ofReal_mul]; ring_nf
  · show (((r : ℂ) * H 1 0 - (r : ℂ) * H 0 1) / (2 * Complex.I)).re =
      r * ((H 1 0 - H 0 1) / (2 * Complex.I)).re
    rw [← Complex.re_ofReal_mul]; ring_nf
  · show (((r : ℂ) * H 0 0 - (r : ℂ) * H 1 1) / 2).re = r * ((H 0 0 - H 1 1) / 2).re
    rw [← Complex.re_ofReal_mul]; ring_nf

/-- `κ(A)` as an `ℝ`-linear map. -/
noncomputable def W7b_ChatterjeeQFT_kL (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := kappa A
  map_add' x y := by
    unfold kappa
    rw [W7b_ChatterjeeQFT_herm_add, Matrix.mul_add, Matrix.add_mul, W7b_ChatterjeeQFT_vec_add]
  map_smul' r x := by
    unfold kappa
    rw [W7b_ChatterjeeQFT_herm_smul, Matrix.mul_smul, Matrix.smul_mul, W7b_ChatterjeeQFT_vec_smul]
    rfl

/-- The matrix of `κ(A)`. -/
noncomputable def W7b_ChatterjeeQFT_Lm (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' (W7b_ChatterjeeQFT_kL A)

theorem W7b_ChatterjeeQFT_Lm_mulVec (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    W7b_ChatterjeeQFT_Lm A *ᵥ x = kappa A x := by
  unfold W7b_ChatterjeeQFT_Lm
  rw [LinearMap.toMatrix'_mulVec]; rfl

theorem W7b_ChatterjeeQFT_Lm_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    W7b_ChatterjeeQFT_Lm (A * B) = W7b_ChatterjeeQFT_Lm A * W7b_ChatterjeeQFT_Lm B := by
  unfold W7b_ChatterjeeQFT_Lm
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact W7b_ChatterjeeQFT_kappa_mul A B x

theorem W7b_ChatterjeeQFT_sq_kappa (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1)
    (x : Fin 4 → ℝ) : minkowskiSq (kappa A x) = minkowskiSq x := by
  have h1 := W7b_ChatterjeeQFT_det_herm (kappa A x)
  rw [W7b_ChatterjeeQFT_herm_kappa, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hA,
    W7b_ChatterjeeQFT_det_herm] at h1
  simp only [star_one, one_mul, mul_one] at h1
  exact_mod_cast h1.symm

theorem W7b_ChatterjeeQFT_polar (x y : Fin 4 → ℝ) :
    minkowskiInner x y = (minkowskiSq (x + y) - minkowskiSq x - minkowskiSq y) / 2 := by
  simp only [minkowskiSq, minkowskiInner, Pi.add_apply]; ring

theorem W7b_ChatterjeeQFT_Lm_lorentz (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    IsLorentz (W7b_ChatterjeeQFT_Lm A) := by
  intro x y
  rw [W7b_ChatterjeeQFT_polar, W7b_ChatterjeeQFT_polar x y, ← Matrix.mulVec_add]
  simp only [W7b_ChatterjeeQFT_Lm_mulVec, W7b_ChatterjeeQFT_sq_kappa A hA]

/-- The Minkowski metric matrix. -/
def W7b_ChatterjeeQFT_eta : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

theorem W7b_ChatterjeeQFT_inner_eq (x y : Fin 4 → ℝ) :
    minkowskiInner x y = x ⬝ᵥ (W7b_ChatterjeeQFT_eta *ᵥ y) := by
  simp [minkowskiInner, W7b_ChatterjeeQFT_eta, dotProduct, Fin.sum_univ_four, mulVec_diagonal]
  ring

theorem W7b_ChatterjeeQFT_det_sq (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsLorentz L) :
    L.det ^ 2 = 1 := by
  have hM : Lᵀ * W7b_ChatterjeeQFT_eta * L = W7b_ChatterjeeQFT_eta := by
    ext i j
    have h := hL (Pi.single i 1) (Pi.single j 1)
    rw [W7b_ChatterjeeQFT_inner_eq, W7b_ChatterjeeQFT_inner_eq] at h
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec] at h
    simpa [Matrix.mul_assoc, single_dotProduct, Matrix.mulVec_single, Matrix.vecMul_transpose,
      dotProduct_single] using h
  have hd := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have he : W7b_ChatterjeeQFT_eta.det = -1 := by
    simp [W7b_ChatterjeeQFT_eta, Matrix.det_diagonal, Fin.prod_univ_four]
  rw [he] at hd
  linear_combination -hd

theorem W7b_ChatterjeeQFT_kappa_neg (A : Matrix (Fin 2) (Fin 2) ℂ) :
    W7b_ChatterjeeQFT_Lm (-A) = W7b_ChatterjeeQFT_Lm A := by
  unfold W7b_ChatterjeeQFT_Lm
  congr 1
  apply LinearMap.ext; intro x
  show kappa (-A) x = kappa A x
  unfold kappa
  simp [conjTranspose_neg]

/-- An element of `SL(2,ℂ)` with trace `≠ -2` is a square in `SL(2,ℂ)`. -/
theorem W7b_ChatterjeeQFT_sqrt (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1)
    (ht : A.trace + 2 ≠ 0) : ∃ B : Matrix (Fin 2) (Fin 2) ℂ, B.det = 1 ∧ A = B * B := by
  set t := A.trace + 2 with htdef
  set s : ℂ := t ^ ((2 : ℂ)⁻¹) with hs
  have hs2 : s ^ 2 = t := by
    rw [hs]; exact_mod_cast Complex.cpow_ofNat_inv_pow t 2
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hs2; exact ht (by simpa using hs2.symm)
  have hdet : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
  have htr : A.trace = A 0 0 + A 1 1 := Matrix.trace_fin_two A
  refine ⟨s⁻¹ • (A + 1), ?_, ?_⟩
  · rw [Matrix.det_smul, Matrix.det_fin_two]
    simp only [Fintype.card_fin, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    rw [inv_pow, hs2, htdef, htr]
    have ht' : A 0 0 + A 1 1 + 2 ≠ 0 := by rw [htdef, htr] at ht; exact ht
    rw [inv_mul_eq_iff_eq_mul₀ ht']
    rw [hA] at hdet
    linear_combination -hdet
  · have hs2' : s * s = A 0 0 + A 1 1 + 2 := by rw [← pow_two, hs2, htdef, htr]
    rw [hA] at hdet
    have hsq : (A + 1) * (A + 1) = (s * s) • A := by
      rw [hs2']
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
        first | ring1 | linear_combination hdet
    rw [smul_mul_smul_comm, hsq, smul_smul]
    have : s⁻¹ * s⁻¹ * (s * s) = 1 := by field_simp
    rw [this, one_smul]

theorem W7b_ChatterjeeQFT_det_Lm (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (W7b_ChatterjeeQFT_Lm A).det = 1 := by
  have key : ∀ C : Matrix (Fin 2) (Fin 2) ℂ, C.det = 1 → C.trace + 2 ≠ 0 →
      (W7b_ChatterjeeQFT_Lm C).det = 1 := by
    intro C hC ht
    obtain ⟨B, hB, rfl⟩ := W7b_ChatterjeeQFT_sqrt C hC ht
    rw [W7b_ChatterjeeQFT_Lm_mul, Matrix.det_mul, ← pow_two]
    exact W7b_ChatterjeeQFT_det_sq _ (W7b_ChatterjeeQFT_Lm_lorentz B hB)
  by_cases ht : A.trace + 2 = 0
  · rw [← W7b_ChatterjeeQFT_kappa_neg]
    have hdn : (-A).det = 1 := by rw [Matrix.det_neg]; simp [hA]
    apply key (-A) hdn
    rw [Matrix.trace_neg]
    intro h
    have : (4 : ℂ) = 0 := by linear_combination h + ht
    norm_num at this
  · exact key A hA ht

theorem W7b_ChatterjeeQFT_Lm00 (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    0 < W7b_ChatterjeeQFT_Lm A 0 0 := by
  have h1 : W7b_ChatterjeeQFT_Lm A 0 0 = kappa A (Pi.single 0 1) 0 := by
    unfold W7b_ChatterjeeQFT_Lm
    rw [LinearMap.toMatrix'_apply]; rfl
  have he : hermOfVec (Pi.single 0 1) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hermOfVec]
  have h2 : kappa A (Pi.single 0 1) 0 = (Complex.normSq (A 0 0) + Complex.normSq (A 0 1)
      + Complex.normSq (A 1 0) + Complex.normSq (A 1 1)) / 2 := by
    unfold kappa
    rw [he, Matrix.mul_one]
    show (((A * Aᴴ) 0 0 + (A * Aᴴ) 1 1) / 2).re = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_apply]
    ring
  rw [h1, h2]
  have hdet := Matrix.det_fin_two A
  rw [hA] at hdet
  by_contra hle
  push_neg at hle
  have n1 := Complex.normSq_nonneg (A 0 0)
  have n2 := Complex.normSq_nonneg (A 0 1)
  have n3 := Complex.normSq_nonneg (A 1 0)
  have n4 := Complex.normSq_nonneg (A 1 1)
  have z1 : A 0 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have z2 : A 0 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  rw [z1, z2] at hdet
  norm_num at hdet

theorem solution (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (∃ L : Matrix (Fin 4) (Fin 4) ℝ, IsRestrictedLorentz L ∧ ∀ x : Fin 4 → ℝ, kappa A x = L *ᵥ x)
      ∧ (∀ x : Fin 4 → ℝ, kappa (A * B) x = kappa A (kappa B x)) :=
  ⟨⟨W7b_ChatterjeeQFT_Lm A, ⟨W7b_ChatterjeeQFT_Lm_lorentz A hA, W7b_ChatterjeeQFT_det_Lm A hA,
      W7b_ChatterjeeQFT_Lm00 A hA⟩, fun x => (W7b_ChatterjeeQFT_Lm_mulVec A x).symm⟩,
    W7b_ChatterjeeQFT_kappa_mul A B⟩
