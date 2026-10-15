-- Prove2me | solution 1 for ExpConeIPM.Secant.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T21:56:20.306976+00:00
-- url     : https://prove2.me/submissions/97009f9b-1ab3-4104-beb9-4ac4f7179adb

import Mathlib
import Definitions.Def_ExpConeIPM_Secant_Recursion

set_option autoImplicit false

namespace ExpConeIPM.Secant

open Matrix

section secaux

variable {n p : ℕ}

lemma sec_col (M : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) (r : Fin n) :
    (M *ᵥ unitVec j) r = M r j := by
  have := congrFun (Matrix.mulVec_single_one M j) r
  simpa [unitVec] using this

lemma sec_col' (M : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) (r : Fin p) :
    (M *ᵥ unitVec j) r = M r j := by
  have := congrFun (Matrix.mulVec_single_one M j) r
  simpa [unitVec] using this

lemma sec_sym_dot (M : Matrix (Fin p) (Fin p) ℝ) (hM : Mᵀ = M) (a b : Fin p → ℝ) :
    a ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (M *ᵥ a) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, dotProduct_comm]

lemma sec_colInner (Y S : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) :
    colInner Y S j = (Yᵀ * S) j j := by
  simp [colInner, dotProduct, sec_col, Matrix.mul_apply]

lemma sec_vS (Y S : Matrix (Fin n) (Fin p) ℝ) (hsym : (Yᵀ * S)ᵀ = Yᵀ * S) (j : Fin p) :
    (Y *ᵥ unitVec j) ᵥ* S = (Yᵀ * S) *ᵥ unitVec j := by
  rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, ← Matrix.transpose_transpose Y,
    ← Matrix.transpose_mul, Matrix.transpose_transpose, hsym]

lemma sec_uY (Y S : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) :
    (S *ᵥ unitVec j) ᵥ* Y = (Yᵀ * S) *ᵥ unitVec j := by
  rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]

lemma sec_step_fst (j : Fin p) (Y S : Matrix (Fin n) (Fin p) ℝ) (hsym : (Yᵀ * S)ᵀ = Yᵀ * S) :
    (step j Y S).1 = Y - vecMulVec ((Real.sqrt (colInner Y S j))⁻¹ • (Y *ᵥ unitVec j))
        ((Real.sqrt (colInner Y S j))⁻¹ • ((Yᵀ * S) *ᵥ unitVec j)) := by
  simp only [step]
  rw [Matrix.vecMulVec_mul, Matrix.smul_vecMul, sec_vS Y S hsym]

lemma sec_step_snd (j : Fin p) (Y S : Matrix (Fin n) (Fin p) ℝ) :
    (step j Y S).2 = S - vecMulVec ((Real.sqrt (colInner Y S j))⁻¹ • (S *ᵥ unitVec j))
        ((Real.sqrt (colInner Y S j))⁻¹ • ((Yᵀ * S) *ᵥ unitVec j)) := by
  simp only [step]
  rw [Matrix.vecMulVec_mul, Matrix.smul_vecMul, sec_uY Y S]

lemma sec_cc (d : ℝ) (hd : 0 < d) : (Real.sqrt d)⁻¹ * (Real.sqrt d)⁻¹ * d = 1 := by
  have h : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd.le
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  field_simp
  linarith

lemma sec_step_M (j : Fin p) (Y S : Matrix (Fin n) (Fin p) ℝ) (hsym : (Yᵀ * S)ᵀ = Yᵀ * S)
    (hd : 0 < colInner Y S j) :
    (step j Y S).1ᵀ * (step j Y S).2 = Yᵀ * S -
      vecMulVec ((Real.sqrt (colInner Y S j))⁻¹ • ((Yᵀ * S) *ᵥ unitVec j))
        ((Real.sqrt (colInner Y S j))⁻¹ • ((Yᵀ * S) *ᵥ unitVec j)) := by
  rw [sec_step_fst j Y S hsym, sec_step_snd j Y S]
  set c := (Real.sqrt (colInner Y S j))⁻¹ with hc
  set ℓ : Fin p → ℝ := c • ((Yᵀ * S) *ᵥ unitVec j) with hℓ
  set v : Fin n → ℝ := c • (Y *ᵥ unitVec j) with hv
  set u : Fin n → ℝ := c • (S *ᵥ unitVec j) with hu
  have h1 : Yᵀ *ᵥ u = ℓ := by
    rw [hu, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hℓ]
  have h2 : v ᵥ* S = ℓ := by
    rw [hv, Matrix.smul_vecMul, sec_vS Y S hsym, hℓ]
  have h3 : v ⬝ᵥ u = 1 := by
    rw [hv, hu, smul_dotProduct, dotProduct_smul]
    have := sec_cc _ hd
    simp only [smul_eq_mul]
    rw [← hc] at this
    have e : (Y *ᵥ unitVec j) ⬝ᵥ (S *ᵥ unitVec j) = colInner Y S j := rfl
    rw [e]
    linarith
  rw [Matrix.transpose_sub, Matrix.transpose_vecMulVec, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.mul_vecMulVec, h1, Matrix.vecMulVec_mul, h2,
    Matrix.vecMulVec_mul_vecMulVec, h3, one_smul]
  abel

lemma sec_step_col (j : Fin p) (Y S : Matrix (Fin n) (Fin p) ℝ) (hsym : (Yᵀ * S)ᵀ = Yᵀ * S)
    (hd : 0 < colInner Y S j) (k : ℕ) (hjk : j.val = k)
    (hz : ∀ i : Fin p, i.val < k → ∀ r, Y r i = 0 ∧ S r i = 0) :
    ∀ i : Fin p, i.val < k + 1 → ∀ r, (step j Y S).1 r i = 0 ∧ (step j Y S).2 r i = 0 := by
  intro i hi r
  rw [sec_step_fst j Y S hsym, sec_step_snd j Y S]
  have hcc := sec_cc _ hd
  have hdj : colInner Y S j = (Yᵀ * S) j j := sec_colInner Y S j
  simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, sec_col]
  by_cases hij : i = j
  · subst hij
    rw [← hdj]
    constructor
    · have : Y r i * (1 - (Real.sqrt (colInner Y S i))⁻¹ * (Real.sqrt (colInner Y S i))⁻¹ * colInner Y S i) = 0 := by
        rw [hcc]; ring
      linarith [this]
    · have : S r i * (1 - (Real.sqrt (colInner Y S i))⁻¹ * (Real.sqrt (colInner Y S i))⁻¹ * colInner Y S i) = 0 := by
        rw [hcc]; ring
      linarith [this]
  · have hik : i.val < k := by
      have : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    have hM0 : (Yᵀ * S) i j = 0 := by
      simp [Matrix.mul_apply, (hz i hik _).1]
    rw [hM0, (hz i hik r).1, (hz i hik r).2]
    simp

lemma sec_step_pos (j : Fin p) (Y S : Matrix (Fin n) (Fin p) ℝ) (hsym : (Yᵀ * S)ᵀ = Yᵀ * S)
    (hd : 0 < colInner Y S j) (k : ℕ) (hjk : j.val = k)
    (hB : ∀ x : Fin p → ℝ, (∀ i : Fin p, i.val < k → x i = 0) → x ≠ 0 →
      0 < x ⬝ᵥ ((Yᵀ * S) *ᵥ x)) :
    ∀ x : Fin p → ℝ, (∀ i : Fin p, i.val < k + 1 → x i = 0) → x ≠ 0 →
      0 < x ⬝ᵥ (((step j Y S).1ᵀ * (step j Y S).2) *ᵥ x) := by
  intro x hx hx0
  rw [sec_step_M j Y S hsym hd]
  have hdj : colInner Y S j = (Yᵀ * S) j j := sec_colInner Y S j
  have hcc := sec_cc _ hd
  generalize hM : Yᵀ * S = M at *
  generalize hdd : colInner Y S j = d at *
  have hed : unitVec j ⬝ᵥ (M *ᵥ unitVec j) = d := by
    rw [hdj]
    simp only [unitVec, single_dotProduct, one_mul]
    exact sec_col' M j j
  have hd0 : d ≠ 0 := hd.ne'
  generalize hc : (Real.sqrt d)⁻¹ = c at *
  have hcd : c * c = d⁻¹ := by
    apply eq_inv_of_mul_eq_one_left hcc
  set m := x ⬝ᵥ (M *ᵥ unitVec j) with hm
  set t := m / d with ht
  have hyz : ∀ i : Fin p, i.val < k → (x - t • unitVec j) i = 0 := by
    intro i hi
    have hij : i ≠ j := fun h => by subst h; omega
    simp [unitVec, hx i (by omega), Pi.single_apply, hij]
  have hy0 : x - t • unitVec j ≠ 0 := by
    intro h
    apply hx0
    funext i
    have := congrFun h i
    by_cases hij : i = j
    · subst hij
      exact hx i (by omega)
    · simpa [unitVec, Pi.single_apply, hij] using this
  have hpos := hB _ hyz hy0
  have key : (x - t • unitVec j) ⬝ᵥ (M *ᵥ (x - t • unitVec j)) =
      x ⬝ᵥ (M *ᵥ x) - c * c * m * m := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [sec_sym_dot M hsym (unitVec j) x, hed, ← hm, hcd, ht]
    field_simp
    ring
  have hL : x ⬝ᵥ ((M - vecMulVec (c • (M *ᵥ unitVec j)) (c • (M *ᵥ unitVec j))) *ᵥ x) =
      x ⬝ᵥ (M *ᵥ x) - c * c * m * m := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.vecMulVec_mulVec]
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_smul, smul_eq_mul,
      smul_dotProduct]
    rw [dotProduct_comm (M *ᵥ unitVec j) x, ← hm]
    ring
  rw [hL, ← key]
  exact hpos

noncomputable def sec_v (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : Fin n → ℝ :=
  (Real.sqrt (d Y₀ S₀ j))⁻¹ • (Ys Y₀ S₀ j *ᵥ unitVec j)

noncomputable def sec_u (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : Fin n → ℝ :=
  (Real.sqrt (d Y₀ S₀ j))⁻¹ • (Ss Y₀ S₀ j *ᵥ unitVec j)

noncomputable def sec_l (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : Fin p → ℝ :=
  (Real.sqrt (d Y₀ S₀ j))⁻¹ • (((Ys Y₀ S₀ j)ᵀ * Ss Y₀ S₀ j) *ᵥ unitVec j)

lemma sec_pair_succ (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (hk : k < p) :
    Ys Y₀ S₀ (k + 1) = (step ⟨k, hk⟩ (Ys Y₀ S₀ k) (Ss Y₀ S₀ k)).1 ∧
    Ss Y₀ S₀ (k + 1) = (step ⟨k, hk⟩ (Ys Y₀ S₀ k) (Ss Y₀ S₀ k)).2 := by
  simp [Ys, Ss, pair, hk]

lemma sec_inv (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (hPD : (Y₀ᵀ * S₀).PosDef) :
    ∀ k, k ≤ p →
    ((Ys Y₀ S₀ k)ᵀ * Ss Y₀ S₀ k)ᵀ = (Ys Y₀ S₀ k)ᵀ * Ss Y₀ S₀ k ∧
    (∀ x : Fin p → ℝ, (∀ i : Fin p, i.val < k → x i = 0) → x ≠ 0 →
      0 < x ⬝ᵥ (((Ys Y₀ S₀ k)ᵀ * Ss Y₀ S₀ k) *ᵥ x)) ∧
    (∀ i : Fin p, i.val < k → ∀ r, Ys Y₀ S₀ k r i = 0 ∧ Ss Y₀ S₀ k r i = 0) ∧
    Y₀ = Ys Y₀ S₀ k + ∑ j ∈ Finset.range k,
      (if h : j < p then vecMulVec (sec_v Y₀ S₀ ⟨j, h⟩) (sec_l Y₀ S₀ ⟨j, h⟩) else 0) ∧
    S₀ = Ss Y₀ S₀ k + ∑ j ∈ Finset.range k,
      (if h : j < p then vecMulVec (sec_u Y₀ S₀ ⟨j, h⟩) (sec_l Y₀ S₀ ⟨j, h⟩) else 0) ∧
    Y₀ᵀ * S₀ = (Ys Y₀ S₀ k)ᵀ * Ss Y₀ S₀ k + ∑ j ∈ Finset.range k,
      (if h : j < p then vecMulVec (sec_l Y₀ S₀ ⟨j, h⟩) (sec_l Y₀ S₀ ⟨j, h⟩) else 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : Ys Y₀ S₀ 0 = Y₀ := rfl
    have h0' : Ss Y₀ S₀ 0 = S₀ := rfl
    rw [h0, h0']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hPD.1
    · intro x _ hx
      simpa using hPD.dotProduct_mulVec_pos hx
    · intro i hi; omega
    · simp
    · simp
    · simp
  | succ k ih =>
    intro hk1
    have hk : k < p := hk1
    obtain ⟨hsym, hB, hz, hYs, hSs, hMs⟩ := ih hk.le
    have hd : 0 < colInner (Ys Y₀ S₀ k) (Ss Y₀ S₀ k) ⟨k, hk⟩ := by
      have hpos := hB (unitVec ⟨k, hk⟩) (by
        intro i hi
        have hij : i ≠ ⟨k, hk⟩ := fun h => by subst h; simp at hi
        simp [unitVec, Pi.single_apply, hij]) (by
        intro h
        have := congrFun h ⟨k, hk⟩
        simp [unitVec] at this)
      rw [sec_colInner]
      have h1 : unitVec ⟨k, hk⟩ ⬝ᵥ (((Ys Y₀ S₀ k)ᵀ * Ss Y₀ S₀ k) *ᵥ unitVec ⟨k, hk⟩) =
          ((Ys Y₀ S₀ k)ᵀ * Ss Y₀ S₀ k) ⟨k, hk⟩ ⟨k, hk⟩ := by
        simp only [unitVec, single_dotProduct, one_mul]
        exact sec_col' _ _ _
      rwa [h1] at hpos
    obtain ⟨hY1, hS1⟩ := sec_pair_succ Y₀ S₀ k hk
    have e1 : Ys Y₀ S₀ (k + 1) = Ys Y₀ S₀ k -
        vecMulVec (sec_v Y₀ S₀ ⟨k, hk⟩) (sec_l Y₀ S₀ ⟨k, hk⟩) := by
      rw [hY1, sec_step_fst _ _ _ hsym]; rfl
    have e2 : Ss Y₀ S₀ (k + 1) = Ss Y₀ S₀ k -
        vecMulVec (sec_u Y₀ S₀ ⟨k, hk⟩) (sec_l Y₀ S₀ ⟨k, hk⟩) := by
      rw [hS1, sec_step_snd]; rfl
    have e3 : (Ys Y₀ S₀ (k + 1))ᵀ * Ss Y₀ S₀ (k + 1) = (Ys Y₀ S₀ k)ᵀ * Ss Y₀ S₀ k -
        vecMulVec (sec_l Y₀ S₀ ⟨k, hk⟩) (sec_l Y₀ S₀ ⟨k, hk⟩) := by
      rw [hY1, hS1, sec_step_M _ _ _ hsym hd]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e3, Matrix.transpose_sub, Matrix.transpose_vecMulVec, hsym]
    · rw [hY1, hS1]; exact sec_step_pos _ _ _ hsym hd k rfl hB
    · rw [hY1, hS1]; exact sec_step_col _ _ _ hsym hd k rfl hz
    · rw [Finset.sum_range_succ, dif_pos hk, e1]
      refine hYs.trans ?_
      abel
    · rw [Finset.sum_range_succ, dif_pos hk, e2]
      refine hSs.trans ?_
      abel
    · rw [Finset.sum_range_succ, dif_pos hk, e3]
      refine hMs.trans ?_
      abel

lemma sec_final {m q : ℕ} (A W : Matrix (Fin m) (Fin q) ℝ) (M L : Matrix (Fin q) (Fin q) ℝ)
    (hA : A = W * Lᵀ) (hM : M = L * Lᵀ) (hU : IsUnit M.det) : A * M⁻¹ * Aᵀ = W * Wᵀ := by
  have hL : IsUnit L.det := by
    rw [hM, Matrix.det_mul, Matrix.det_transpose] at hU
    exact isUnit_of_mul_isUnit_left hU
  have hLt : IsUnit Lᵀ.det := by rwa [Matrix.det_transpose]
  rw [hA, hM, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Lᵀ, Matrix.mul_nonsing_inv _ hLt, Matrix.one_mul,
    ← Matrix.mul_assoc L⁻¹, Matrix.nonsing_inv_mul _ hL, Matrix.one_mul]

lemma sec_main {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (hPD : (Y₀ᵀ * S₀).PosDef) :
    Y₀ * (Y₀ᵀ * S₀)⁻¹ * Y₀ᵀ = V Y₀ S₀ * (V Y₀ S₀)ᵀ ∧
      S₀ * (Y₀ᵀ * S₀)⁻¹ * S₀ᵀ = U Y₀ S₀ * (U Y₀ S₀)ᵀ := by
  obtain ⟨_, _, hz, hYs, hSs, hMs⟩ := sec_inv Y₀ S₀ hPD p le_rfl
  have hYp : Ys Y₀ S₀ p = 0 := by
    ext r i; exact (hz i i.2 r).1
  have hSp : Ss Y₀ S₀ p = 0 := by
    ext r i; exact (hz i i.2 r).2
  rw [hYp, zero_add] at hYs
  rw [hSp, zero_add] at hSs
  rw [hYp, hSp, Matrix.transpose_zero, Matrix.zero_mul, zero_add] at hMs
  have hV : (∑ j ∈ Finset.range p,
      (if h : j < p then vecMulVec (sec_v Y₀ S₀ ⟨j, h⟩) (sec_l Y₀ S₀ ⟨j, h⟩) else 0)) =
      V Y₀ S₀ * (L Y₀ S₀)ᵀ := by
    rw [Finset.sum_range]
    ext i c
    simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, V, L, sec_v, sec_l]
    refine Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hU : (∑ j ∈ Finset.range p,
      (if h : j < p then vecMulVec (sec_u Y₀ S₀ ⟨j, h⟩) (sec_l Y₀ S₀ ⟨j, h⟩) else 0)) =
      U Y₀ S₀ * (L Y₀ S₀)ᵀ := by
    rw [Finset.sum_range]
    ext i c
    simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, U, L, sec_u, sec_l]
    refine Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hL : (∑ j ∈ Finset.range p,
      (if h : j < p then vecMulVec (sec_l Y₀ S₀ ⟨j, h⟩) (sec_l Y₀ S₀ ⟨j, h⟩) else 0)) =
      L Y₀ S₀ * (L Y₀ S₀)ᵀ := by
    rw [Finset.sum_range]
    ext i c
    simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, L, sec_l]
    refine Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [hV] at hYs
  rw [hU] at hSs
  rw [hL] at hMs
  have hdet : IsUnit (Y₀ᵀ * S₀).det := (Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit
  exact ⟨sec_final Y₀ (V Y₀ S₀) (Y₀ᵀ * S₀) (L Y₀ S₀) hYs hMs hdet,
    sec_final S₀ (U Y₀ S₀) (Y₀ᵀ * S₀) (L Y₀ S₀) hSs hMs hdet⟩

end secaux

end ExpConeIPM.Secant

open ExpConeIPM.Secant Matrix in
theorem solution {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (hPD : (Y₀ᵀ * S₀).PosDef) :
    Y₀ * (Y₀ᵀ * S₀)⁻¹ * Y₀ᵀ = V Y₀ S₀ * (V Y₀ S₀)ᵀ ∧
      S₀ * (Y₀ᵀ * S₀)⁻¹ * S₀ᵀ = U Y₀ S₀ * (U Y₀ S₀)ᵀ := by
  exact ExpConeIPM.Secant.sec_main Y₀ S₀ hPD

