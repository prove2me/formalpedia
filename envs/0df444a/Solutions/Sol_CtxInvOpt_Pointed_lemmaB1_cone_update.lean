-- Prove2me | solution 1 for CtxInvOpt.Pointed.lemmaB1_cone_update
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:46:07.459988+00:00
-- url     : https://prove2.me/submissions/e748abc8-f4fb-420c-8a80-46495e807759

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_ConeUpdate
import Theorems.Thm_LinearOptimization_ellipsoid_update_halfspace_volume

open Matrix CtxInvOpt.Pointed

namespace B1Red

lemma log_ineq (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (1 / x) * (-Real.log (1 - x ^ 2)) - (Real.log (1 + x) - Real.log (1 - x)) ≤ -x := by
  have hax : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hax2 : |x ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg x)]; nlinarith
  have S1 := (Real.hasSum_pow_div_log_of_abs_lt_one hax2).mul_left (1 / x)
  have S2 := Real.hasSum_log_sub_log_of_abs_lt_one hax
  have S := S1.sub S2
  have B : HasSum (fun n : ℕ => if n = 0 then -x else 0) (-x) := hasSum_ite_eq 0 (-x)
  refine hasSum_le (fun n => ?_) S B
  have hxn : (1 / x) * ((x ^ 2) ^ (n + 1) / ((n:ℝ) + 1)) = x ^ (2 * n + 1) / ((n:ℝ) + 1) := by
    rw [← pow_mul]
    field_simp
    ring
  show (1 / x) * ((x ^ 2) ^ (n + 1) / ((n:ℝ) + 1)) - 2 * (1 / (2 * (n:ℝ) + 1)) * x ^ (2 * n + 1) ≤ _
  rw [hxn]
  have hp : 0 ≤ x ^ (2 * n + 1) := by positivity
  split_ifs with h
  · subst h; simp; ring_nf; linarith
  · have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have : x ^ (2 * n + 1) / ((n:ℝ) + 1) ≤ 2 * (1 / (2 * (n:ℝ) + 1)) * x ^ (2 * n + 1) := by
      rw [div_le_iff₀ (by positivity)]
      have : (1:ℝ) ≤ 2 * (1 / (2 * (n:ℝ) + 1)) * ((n:ℝ) + 1) := by
        rw [show 2 * (1 / (2 * (n:ℝ) + 1)) * ((n:ℝ) + 1) = (2 * n + 2) / (2 * n + 1) by
          field_simp, le_div_iff₀ (by positivity)]
        linarith
      nlinarith
    linarith

lemma rate_ineq (m : ℕ) (hm : 2 ≤ m) :
    ((m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1)) ^ m * (1 - 2 / ((m:ℝ) + 1)) ≤ Real.exp (-(1 / (m:ℝ))) := by
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  set x : ℝ := 1 / m with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hxdef, div_lt_one (by linarith)]; linarith
  have hmx : (m:ℝ) = 1 / x := by rw [hxdef]; field_simp
  have hpos : 0 < ((m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1)) ^ m * (1 - 2 / ((m:ℝ) + 1)) := by
    apply mul_pos
    · apply pow_pos; apply div_pos (by positivity); nlinarith
    · rw [sub_pos, div_lt_one (by linarith)]; linarith
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.2
  have e1 : (m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1) = (1 - x ^ 2)⁻¹ := by
    rw [hmx]; field_simp
  have e2 : 1 - 2 / ((m:ℝ) + 1) = (1 - x) / (1 + x) := by
    rw [hmx]; field_simp; ring
  have h1x : 0 < 1 - x := by linarith
  have h1x2 : 0 < 1 - x ^ 2 := by nlinarith
  rw [Real.log_mul (by rw [e1]; positivity) (by rw [e2]; positivity), Real.log_pow, e1, e2, Real.log_inv,
    Real.log_div h1x.ne' (by linarith)]
  have := log_ineq x hx0 hx1
  rw [← hmx] at this
  linarith


lemma det_ellUpd {m : ℕ} (w : Fin m → ℝ) (a : Fin m → ℝ)
    (hq : a ⬝ᵥ (Matrix.diagonal w *ᵥ a) ≠ 0) :
    (LinearOptimization.ellipsoidUpdateMatrix (Matrix.diagonal w) a).det =
      ((m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1)) ^ m * (∏ i, w i) * (1 - 2 / ((m:ℝ) + 1)) := by
  unfold LinearOptimization.ellipsoidUpdateMatrix
  rw [det_smul, Fintype.card_fin]
  set q := a ⬝ᵥ (Matrix.diagonal w *ᵥ a)
  have hM : Matrix.diagonal w - ((2:ℝ) / (m + 1)) • q⁻¹ • (Matrix.diagonal w * vecMulVec a a * Matrix.diagonal w)
      = Matrix.diagonal w * (1 + replicateCol Unit (-(((2:ℝ) / (m + 1)) * q⁻¹) • a) *
          replicateRow Unit (Matrix.diagonal w *ᵥ a)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal, vecMulVec, replicateCol, replicateRow, Matrix.one_apply,
      Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.add_apply, mul_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    split_ifs <;> ring
  rw [hM, det_mul, det_diagonal, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, dotProduct_comm, ← mul_assoc]
  change _ * (1 + -(2 / ((m:ℝ) + 1) * q⁻¹) * q) = _
  field_simp
  ring

lemma dot_rot {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin k) ℝ)
    (x y : Fin k → ℝ) : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ y) = x ⬝ᵥ y := by
  have h1 : U * Uᵀ = 1 := by simpa using (Matrix.mem_orthogonalGroup_iff (Fin k) ℝ).1 hU
  rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h1, one_mulVec]

lemma inner_eq_dot {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ x y = (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp y) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma core_ineq (y0 y1 a0 p : ℝ) (hy0 : 0 ≤ y0) (hp : 0 ≤ p) (hp2 : p ^ 2 = a0 ^ 2 * y1 ^ 2)
    (hkey : y1 ^ 2 ≤ 2 * y0 * p) :
    (y0 ^ 2 + y1 ^ 2) * (1 + a0 ^ 2) ≤ (1 + 2 * a0 ^ 2) * (y0 + p) ^ 2 := by
  have h1 := mul_nonneg (sq_nonneg a0) (mul_nonneg hy0 hp)
  have h2 := mul_nonneg (sq_nonneg a0) (sq_nonneg p)
  have h3 := mul_nonneg (sq_nonneg a0) (sq_nonneg y0)
  have e : (1 + 2 * a0 ^ 2) * (y0 + p) ^ 2 - (y0 ^ 2 + y1 ^ 2) * (1 + a0 ^ 2) =
      (2 * y0 * p - y1 ^ 2) + a0 ^ 2 * y0 ^ 2 + 4 * (a0 ^ 2 * (y0 * p)) + 2 * (a0 ^ 2 * p ^ 2) +
        (p ^ 2 - a0 ^ 2 * y1 ^ 2) := by ring
  rw [hp2] at e
  nlinarith


lemma dot_self_pos {m : ℕ} (v : Fin m → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  rcases Function.ne_iff.1 hv with ⟨i, hi⟩
  have : v i ^ 2 ≤ v ⬝ᵥ v := by
    unfold dotProduct
    have := Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
      (Finset.mem_univ i)
    simpa [sq] using this
  have : 0 < v i ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))
  linarith


lemma dbar_facts {m : ℕ} (v : Fin m → ℝ) (hv : v ≠ 0) (w : Fin m → ℝ) :
    ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ≠ 0 ∧
    ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) = 1 ∧
    ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ (Matrix.diagonal w *ᵥ ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v)) =
      (∑ i, w i * v i ^ 2) / (v ⬝ᵥ v) := by
  have hpos := dot_self_pos v hv
  have hs : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  have hs0 : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hpos
  refine ⟨smul_ne_zero (inv_ne_zero hs0.ne') hv, ?_, ?_⟩
  · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, inv_pow, hs,
      inv_mul_cancel₀ hpos.ne']
  · rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← sq, inv_pow, hs]
    simp only [Matrix.mulVec_diagonal, dotProduct]
    rw [div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => by ring)



lemma dot_mulVec_left {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (x y : Fin k → ℝ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

lemma VtMV {k : ℕ} (M V : Matrix (Fin k) (Fin k) ℝ) (hV : V ∈ orthogonalGroup (Fin k) ℝ)
    (μ : Fin k → ℝ) (h : M * V = V * diagonal μ) : Vᵀ * M * V = diagonal μ := by
  have h2 : Vᵀ * V = 1 := by simpa using (mem_orthogonalGroup_iff' (Fin k) ℝ).1 hV
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, h2, Matrix.one_mul]

lemma quad_V {k : ℕ} (M V : Matrix (Fin k) (Fin k) ℝ) (hV : V ∈ orthogonalGroup (Fin k) ℝ)
    (μ : Fin k → ℝ) (h : M * V = V * diagonal μ) (c : Fin k → ℝ) :
    (V *ᵥ c) ⬝ᵥ (M *ᵥ (V *ᵥ c)) = ∑ j, μ j * c j ^ 2 := by
  rw [dot_mulVec_left, mulVec_mulVec, mulVec_mulVec, VtMV M V hV μ h]
  simp [dotProduct, mulVec_diagonal, sq]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma bordered_eq {m : ℕ} (a : Fin m → ℝ) (N : Matrix (Fin m) (Fin m) ℝ) :
    borderedMatrix a N = vecMulVec (Fin.cons 1 a : Fin (m+1) → ℝ) (Fin.cons 1 a) -
      Matrix.of (fun i j : Fin (m+1) => Fin.cases (0 : ℝ) (fun i' => Fin.cases 0 (fun j' => N i' j') j) i) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [borderedMatrix, vecMulVec]

lemma quad_bordered {m : ℕ} (a : Fin m → ℝ) (N : Matrix (Fin m) (Fin m) ℝ) (x : Fin (m+1) → ℝ) :
    x ⬝ᵥ (borderedMatrix a N *ᵥ x) =
      (x 0 + a ⬝ᵥ tailVec x) ^ 2 - tailVec x ⬝ᵥ (N *ᵥ tailVec x) := by
  rw [bordered_eq, sub_mulVec, dotProduct_sub]
  congr 1
  · set u : Fin (m+1) → ℝ := Fin.cons 1 a
    have h1 : vecMulVec u u *ᵥ x = (u ⬝ᵥ x) • u := by
      ext i
      simp only [vecMulVec, mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have h2 : u ⬝ᵥ x = x 0 + a ⬝ᵥ tailVec x := by
      simp [u, dotProduct, Fin.sum_univ_succ, tailVec]
    rw [h1, dotProduct_smul, smul_eq_mul, dotProduct_comm x u, h2, sq]
  · simp [mulVec, dotProduct, Fin.sum_univ_succ, tailVec]


lemma dot_rot' {k : ℕ} (V : Matrix (Fin k) (Fin k) ℝ) (hV : V ∈ orthogonalGroup (Fin k) ℝ)
    (x y : Fin k → ℝ) : (V *ᵥ x) ⬝ᵥ (V *ᵥ y) = x ⬝ᵥ y := by
  have h2 : Vᵀ * V = 1 := by simpa using (mem_orthogonalGroup_iff' (Fin k) ℝ).1 hV
  rw [dot_mulVec_left, mulVec_mulVec, h2, one_mulVec]

lemma VVt {k : ℕ} (V : Matrix (Fin k) (Fin k) ℝ) (hV : V ∈ orthogonalGroup (Fin k) ℝ) :
    V * Vᵀ = 1 := by simpa using (mem_orthogonalGroup_iff (Fin k) ℝ).1 hV

lemma mu0_ge_one {m : ℕ} (a : Fin m → ℝ) (N : Matrix (Fin m) (Fin m) ℝ)
    (V : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (hV : V ∈ orthogonalGroup (Fin (m+1)) ℝ)
    (μ : Fin (m+1) → ℝ) (hMV : borderedMatrix a N * V = V * diagonal μ) (hμ0 : 0 < μ 0)
    (hneg : ∀ i : Fin m, μ i.succ < 0) : 1 ≤ μ 0 := by
  set e : Fin (m+1) → ℝ := Pi.single 0 1
  set c := Vᵀ *ᵥ e
  have hVc : V *ᵥ c = e := by rw [mulVec_mulVec, VVt V hV, one_mulVec]
  have hq := quad_V _ V hV μ hMV c
  rw [hVc, quad_bordered] at hq
  have he0 : tailVec e = 0 := by ext i; simp [e, tailVec]
  rw [he0] at hq
  simp [e] at hq
  have hcc : ∑ j, c j ^ 2 = 1 := by
    have := dot_rot' V hV c c
    rw [hVc, dotProduct_single] at this
    simp only [e, Pi.single_eq_same, mul_one] at this
    simp only [dotProduct, ← sq] at this
    exact this.symm
  rw [Fin.sum_univ_succ] at hq hcc
  have : ∑ i : Fin m, μ i.succ * c i.succ ^ 2 ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hneg i).le (sq_nonneg _))
  have h2 : ∑ i : Fin m, c i.succ ^ 2 ≥ 0 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith


lemma seeger {m : ℕ} (a : Fin m → ℝ) (N : Matrix (Fin m) (Fin m) ℝ) (hN : N.PosDef)
    (V : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (hV : V ∈ orthogonalGroup (Fin (m+1)) ℝ)
    (μ : Fin (m+1) → ℝ) (hMV : borderedMatrix a N * V = V * diagonal μ) (hμ0 : 0 < μ 0)
    (hneg : ∀ i : Fin m, μ i.succ < 0) (ξ : Fin m → ℝ)
    (hξ : (ξ - a) ⬝ᵥ (N⁻¹ *ᵥ (ξ - a)) ≤ 1) :
    ∑ i : Fin m, (Vᵀ *ᵥ (Fin.cons 1 ξ : Fin (m+1) → ℝ)) i.succ ^ 2 / (-μ i.succ) ≤
      (Vᵀ *ᵥ (Fin.cons 1 ξ : Fin (m+1) → ℝ)) 0 ^ 2 / μ 0 := by
  set u := N⁻¹ *ᵥ (ξ - a) with hudef
  have hNinv : N * N⁻¹ = 1 := mul_nonsing_inv N ((isUnit_iff_isUnit_det N).1 hN.isUnit)
  have hNu : N *ᵥ u = ξ - a := by rw [hudef, mulVec_mulVec, hNinv, one_mulVec]
  set g : Fin (m+1) → ℝ := Fin.cons (1 + a ⬝ᵥ u) (-u) with hgdef
  have hMg : borderedMatrix a N *ᵥ g = Fin.cons 1 ξ := by
    ext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [borderedMatrix, mulVec, dotProduct, Fin.sum_univ_succ, g]
    · have hj := congrFun hNu j
      simp only [mulVec, dotProduct, Pi.sub_apply] at hj
      simp [borderedMatrix, mulVec, dotProduct, Fin.sum_univ_succ, g, mul_add, sub_mul,
        Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hj]
      have : ∑ i, a j * (a i * u i) = ∑ x, a j * a x * u x :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [this]; ring
  have hgq : g ⬝ᵥ (borderedMatrix a N *ᵥ g) = 1 - (ξ - a) ⬝ᵥ u := by
    rw [hMg]
    simp only [g, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.sub_apply,
      Pi.neg_apply]
    rw [show (∑ i, (ξ i - a i) * u i) = ∑ i, ξ i * u i - ∑ i, a i * u i by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)]
    have : ∑ i, -u i * ξ i = -∑ i, ξ i * u i := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]; ring
  set h := Vᵀ *ᵥ g with hhdef
  have hVh : V *ᵥ h = g := by rw [hhdef, mulVec_mulVec, VVt V hV, one_mulVec]
  have hq := quad_V _ V hV μ hMV h
  rw [hVh, hgq] at hq
  have hz : Vᵀ *ᵥ (Fin.cons 1 ξ : Fin (m+1) → ℝ) = fun j => μ j * h j := by
    rw [← hMg, ← hVh, mulVec_mulVec, mulVec_mulVec, VtMV _ V hV μ hMV]
    ext j; simp [mulVec_diagonal]
  rw [hz]
  simp only
  rw [Fin.sum_univ_succ] at hq
  have e1 : ∑ i : Fin m, (μ i.succ * h i.succ) ^ 2 / -μ i.succ = -∑ i : Fin m, μ i.succ * h i.succ ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := (hneg i).ne
    field_simp
  have e2 : (μ 0 * h 0) ^ 2 / μ 0 = μ 0 * h 0 ^ 2 := by field_simp
  rw [e1, e2]
  linarith


lemma sum_sub_dite {m : ℕ} (A : Finset (Fin m)) (G : {j // j ∈ A} → ℝ) {k : ℕ}
    (f : Fin m → (Fin k → ℝ)) :
    ∑ a : {j // j ∈ A}, G a • f a.1 = ∑ j, (if h : j ∈ A then G ⟨j, h⟩ else 0) • f j := by
  rw [← Finset.sum_subset (Finset.subset_univ A) (fun j _ hj => by simp [hj])]
  rw [← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp [a.2]

lemma sum_single_succ {m : ℕ} (cA : Fin m → ℝ) :
    (∑ j : Fin m, cA j • (Pi.single j.succ (1:ℝ) : Fin (m+1) → ℝ)) = Fin.cons 0 cA := by
  ext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [Finset.sum_apply, Pi.single_apply]
  · simp [Finset.sum_apply, Pi.single_apply, Fin.succ_inj]

lemma sum_single {m : ℕ} (l : Fin m → ℝ) :
    (∑ j : Fin m, l j • (Pi.single j (1:ℝ) : Fin m → ℝ)) = l := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

lemma interlace {m : ℕ} (N P : Matrix (Fin m) (Fin m) ℝ)
    (hP : P ∈ orthogonalGroup (Fin m) ℝ) (w' : Fin m → ℝ) (hN : N = P * diagonal w' * Pᵀ)
    (a : Fin m → ℝ) (V : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (hV : V ∈ orthogonalGroup (Fin (m+1)) ℝ)
    (μ : Fin (m+1) → ℝ) (hMV : borderedMatrix a N * V = V * diagonal μ)
    (hneg : ∀ i : Fin m, μ i.succ < 0)
    (hpair : ∀ i j : Fin m, |μ j.succ| < |μ i.succ| → w' j ≤ w' i) (i : Fin m) :
    |μ i.succ| ≤ w' i := by
  classical
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  set t := |μ i.succ| with htdef
  have htpos : 0 < t := abs_pos.2 (hneg i).ne
  set A := Finset.univ.filter (fun j : Fin m => t ≤ |μ j.succ|) with hAdef
  set B := Finset.univ.filter (fun j : Fin m => w' j < t) with hBdef
  have hiA : i ∈ A := by simp [hAdef, htdef]
  have hcard : m + 1 ≤ A.card + B.card := by
    have h1 : (Finset.univ.filter (fun j => ¬ (w' j < t))) ⊆ A.erase i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · intro hji; subst hji; linarith
      · simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hc
        replace hc := lt_of_not_ge hc
        have := hpair i j hc
        linarith
    have h2 := Finset.card_le_card h1
    rw [Finset.card_erase_of_mem hiA] at h2
    have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun j : Fin m => w' j < t)
    rw [Finset.card_univ, Fintype.card_fin] at h3
    have : 1 ≤ A.card := Finset.card_pos.2 ⟨i, hiA⟩
    rw [hBdef]
    omega
  let v : ({j // j ∈ A} ⊕ Option {j // j ∈ B}) → (Fin (m+1) → ℝ) := fun k => match k with
    | Sum.inl j => V *ᵥ Pi.single j.1.succ 1
    | Sum.inr none => Pi.single 0 1
    | Sum.inr (some j) => Fin.cons 0 (P *ᵥ Pi.single j.1 1)
  have hcardι : Module.finrank ℝ (Fin (m+1) → ℝ) <
      Fintype.card ({j // j ∈ A} ⊕ Option {j // j ∈ B}) := by
    simp only [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_option, Fintype.card_coe]
    omega
  have hnli : ¬ LinearIndependent ℝ v := fun hli =>
    absurd hli.fintype_card_le_finrank (not_le.2 hcardι)
  obtain ⟨g, hg, k, hk⟩ := Fintype.not_linearIndependent_iff.1 hnli
  set cA : Fin m → ℝ := fun j => if h : j ∈ A then g (Sum.inl ⟨j, h⟩) else 0 with hcAdef
  set lB : Fin m → ℝ := fun j => if h : j ∈ B then g (Sum.inr (some ⟨j, h⟩)) else 0 with hlBdef
  set x0 := g (Sum.inr none) with hx0def
  set c : Fin (m+1) → ℝ := Fin.cons 0 cA with hcdef
  have hsum : V *ᵥ c + (Fin.cons x0 (P *ᵥ lB) : Fin (m+1) → ℝ) = 0 := by
    rw [← hg, Fintype.sum_sum_type, Fintype.sum_option]
    have e1 : ∑ a : {j // j ∈ A}, g (Sum.inl a) • v (Sum.inl a) = V *ᵥ c := by
      show ∑ a : {j // j ∈ A}, g (Sum.inl a) • (V *ᵥ Pi.single a.1.succ 1) = _
      rw [sum_sub_dite A (fun a => g (Sum.inl a)) (fun j => V *ᵥ Pi.single j.succ 1)]
      simp_rw [← mulVec_smul]
      rw [← mulVec_sum]
      congr 1
      rw [hcdef, ← sum_single_succ cA]
    have e2 : g (Sum.inr none) • v (Sum.inr none) +
        ∑ b : {j // j ∈ B}, g (Sum.inr (some b)) • v (Sum.inr (some b)) =
        (Fin.cons x0 (P *ᵥ lB) : Fin (m+1) → ℝ) := by
      show x0 • (Pi.single 0 1 : Fin (m+1) → ℝ) +
        ∑ b : {j // j ∈ B}, g (Sum.inr (some b)) •
          (Fin.cons 0 (P *ᵥ Pi.single b.1 1) : Fin (m+1) → ℝ) = _
      rw [sum_sub_dite B (fun b => g (Sum.inr (some b)))
        (fun j => (Fin.cons 0 (P *ᵥ Pi.single j 1) : Fin (m+1) → ℝ))]
      have hPl : P *ᵥ lB = ∑ j, lB j • (P *ᵥ Pi.single j 1) := by
        simp_rw [← mulVec_smul]; rw [← mulVec_sum, sum_single]
      rw [hPl]
      ext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Fin.cons_zero, smul_eq_mul]
        simp
      · simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Fin.cons_succ, smul_eq_mul]
        simp only [Pi.single_apply, Fin.succ_ne_zero, if_false, mul_zero, zero_add]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        by_cases hl : l ∈ B <;> simp [hl, hlBdef]
    rw [e1, e2]
  set x := V *ᵥ c with hxdef
  have hx : x = Fin.cons (-x0) (-(P *ᵥ lB)) := by
    have := eq_neg_of_add_eq_zero_left hsum
    rw [this]; ext k; refine Fin.cases ?_ (fun j => ?_) k <;> simp
  have hQ1 := quad_V _ V hV μ hMV c
  rw [Fin.sum_univ_succ] at hQ1
  simp only [hcdef, Fin.cons_zero, Fin.cons_succ] at hQ1
  have hQ1' : ∑ j : Fin m, μ j.succ * cA j ^ 2 ≤ -t * ∑ j, cA j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hj : j ∈ A
    · have hjA : t ≤ |μ j.succ| := by simpa [hAdef] using hj
      have : μ j.succ = -|μ j.succ| := by rw [abs_of_neg (hneg j)]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    · have : cA j = 0 := by simp [hcAdef, hj]
      simp [this]
  have hxx : x ⬝ᵥ x = ∑ j, cA j ^ 2 := by
    rw [hxdef, dot_rot' V hV c c]
    simp [hcdef, dotProduct, Fin.sum_univ_succ, sq]
  have hxx2 : x ⬝ᵥ x = x0 ^ 2 + ∑ j, lB j ^ 2 := by
    rw [hx]
    have := dot_rot' P hP lB lB
    simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.neg_apply] at this ⊢
    simp only [neg_mul_neg, ← sq, neg_sq] at this ⊢
    rw [this]
  have hPNP : Pᵀ * N * P = diagonal w' := by
    have h2 : Pᵀ * P = 1 := by simpa using (mem_orthogonalGroup_iff' (Fin m) ℝ).1 hP
    rw [hN, show Pᵀ * (P * diagonal w' * Pᵀ) * P = (Pᵀ * P) * diagonal w' * (Pᵀ * P) by
      simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
  have hQ2 := quad_bordered a N x
  have htail : tailVec x = -(P *ᵥ lB) := by rw [hx]; ext j; simp [tailVec]
  rw [htail] at hQ2
  have hNq : (-(P *ᵥ lB)) ⬝ᵥ (N *ᵥ (-(P *ᵥ lB))) = ∑ j, w' j * lB j ^ 2 := by
    rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, dot_mulVec_left, mulVec_mulVec,
      mulVec_mulVec, hPNP]
    simp [dotProduct, mulVec_diagonal, sq]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hNq] at hQ2
  have hQ : -t * (x0 ^ 2 + ∑ j, lB j ^ 2) ≥ -∑ j, w' j * lB j ^ 2 := by
    have hsq : 0 ≤ (x 0 + a ⬝ᵥ -(P *ᵥ lB)) ^ 2 := sq_nonneg _
    rw [← hxx2, hxx]
    linarith
  have hterm : ∀ j, 0 ≤ (t - w' j) * lB j ^ 2 := by
    intro j
    by_cases hj : j ∈ B
    · have : w' j < t := by simpa [hBdef] using hj
      exact mul_nonneg (by linarith) (sq_nonneg _)
    · have : lB j = 0 := by simp [hlBdef, hj]
      simp [this]
  have hsumt : t * x0 ^ 2 + ∑ j, (t - w' j) * lB j ^ 2 ≤ 0 := by
    have : ∑ j, (t - w' j) * lB j ^ 2 = t * ∑ j, lB j ^ 2 - ∑ j, w' j * lB j ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]; nlinarith
  have hS0 : 0 ≤ ∑ j, (t - w' j) * lB j ^ 2 := Finset.sum_nonneg (fun j _ => hterm j)
  have hx0 : x0 = 0 := by
    have : t * x0 ^ 2 ≤ 0 := by linarith
    have : x0 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg x0]) (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hl0 : ∀ j, lB j = 0 := by
    intro j
    have hsum0 : ∑ j, (t - w' j) * lB j ^ 2 = 0 := by
      have : t * x0 ^ 2 = 0 := by rw [hx0]; ring
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).1 hsum0 j (Finset.mem_univ j)
    by_cases hj : j ∈ B
    · have hw : w' j < t := by simpa [hBdef] using hj
      have : lB j ^ 2 = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact h
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    · simp [hlBdef, hj]
  have hc0 : ∀ j, cA j = 0 := by
    have hz : ∑ j, cA j ^ 2 = 0 := by
      rw [← hxx, hxx2, hx0]; simp [hl0]
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (cA j))).1 hz j (Finset.mem_univ j)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  apply hk
  rcases k with a' | _ | b
  · have := hc0 a'.1
    simpa [hcAdef, a'.2] using this
  · exact hx0
  · have := hl0 b.1
    simpa [hlBdef, b.2] using this


end B1Red

set_option maxHeartbeats 1000000 in
open B1Red in
theorem solution {m : ℕ} (hm : 2 ≤ m) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ)
    (δ : EuclideanSpace ℝ (Fin (m + 1))) (hδ : inner ℝ δ (axisVec U) ≤ 0)
    (htail : tailVec (rotCoord U δ) ≠ 0)
    (w' : Fin m → ℝ) (U' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hupd : IsConeUpdate w U δ w' U') :
    ellCone w U ∩ {c | 0 ≤ inner ℝ δ c} ⊆ ellCone w' U' ∧
      (∀ i, 0 < w' i) ∧
      ∏ i, w' i ≤ Real.exp (-(1 / (2 * (m : ℝ)))) * ∏ i, w i := by
  unfold IsConeUpdate at hupd
  dsimp only at hupd
  rw [if_neg (by omega)] at hupd
  obtain ⟨V, hV, μ, hMV, hμ0, hneg, hV00, ⟨P, hP, hNP⟩, hpair, rfl⟩ := hupd
  set r := rotCoord U δ with hrdef
  set v := tailVec r with hvdef
  set db : Fin m → ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v with hdbdef
  set N := LinearOptimization.ellipsoidUpdateMatrix (Matrix.diagonal w) db with hNdef
  set aa := LinearOptimization.ellipsoidUpdateCenter 0 (Matrix.diagonal w) db with haadef
  obtain ⟨hd0, hd1, hdq⟩ := dbar_facts v htail w
  have hDpd : (Matrix.diagonal w).PosDef := Matrix.PosDef.diagonal hw
  obtain ⟨hNpd, hincl, -⟩ := LinearOptimization.ellipsoid_update_halfspace_volume hm 0
    (Matrix.diagonal w) hDpd db hd0
  have hPtP : Pᵀ * P = 1 := by simpa using (mem_orthogonalGroup_iff' (Fin m) ℝ).1 hP
  -- positivity of w'
  have hwpos : ∀ i, 0 < w' i := by
    intro i
    set q := P *ᵥ (Pi.single i 1 : Fin m → ℝ)
    have hq0 : q ≠ 0 := by
      intro h0
      have : Pᵀ *ᵥ q = Pi.single i 1 := by rw [mulVec_mulVec, hPtP, one_mulVec]
      rw [h0, mulVec_zero] at this
      have := congrFun this i
      simp at this
    have hpos := hNpd.dotProduct_mulVec_pos hq0
    have hPNP : Pᵀ * N * P = diagonal w' := by
      rw [hNP, show Pᵀ * (P * diagonal w' * Pᵀ) * P = (Pᵀ * P) * diagonal w' * (Pᵀ * P) by
        simp only [Matrix.mul_assoc], hPtP, Matrix.one_mul, Matrix.mul_one]
    have : star q ⬝ᵥ (N *ᵥ q) = w' i := by
      rw [star_trivial, dot_mulVec_left, mulVec_mulVec, mulVec_mulVec, hPNP]
      simp [mulVec_diagonal]
    linarith
  refine ⟨?_, hwpos, ?_⟩
  · rintro c ⟨⟨hy0, hy1⟩, hc⟩
    simp only [Set.mem_ofPred_eq] at hc
    set y := rotCoord U c with hydef
    have hz : rotCoord (U * V) c = Vᵀ *ᵥ y := by
      rw [hydef]; unfold rotCoord; rw [transpose_mul, ← mulVec_mulVec]
    rw [show ellCone w' (U * V) = {c | 0 ≤ rotCoord (U * V) c 0 ∧
      ∑ i, rotCoord (U * V) c i.succ ^ 2 / w' i ≤ rotCoord (U * V) c 0 ^ 2} from rfl]
    simp only [Set.mem_ofPred_eq]
    rw [hz]
    have hμ1 := mu0_ge_one aa N V hV μ hMV hμ0 hneg
    have hint := interlace N P hP w' hNP aa V hV μ hMV hneg hpair
    rcases hy0.lt_or_eq with hy0p | hy0z
    · set ξ : Fin m → ℝ := (y 0)⁻¹ • tailVec y with hξdef
      have hyξ : y = (y 0) • (Fin.cons 1 ξ : Fin (m+1) → ℝ) := by
        ext k; refine Fin.cases ?_ (fun j => ?_) k
        · simp
        · simp [hξdef, tailVec]; field_simp
      have hvy : 0 ≤ v ⬝ᵥ tailVec y := by
        have hinner : inner ℝ δ c = r ⬝ᵥ y := by
          rw [inner_eq_dot, hrdef, hydef]; unfold rotCoord; rw [dot_rot U hU]
        have hr0 : r 0 = inner ℝ δ (axisVec U) := by
          simp [hrdef, rotCoord, axisVec, mulVec, dotProduct, PiLp.inner_apply, mul_comm]
        have hsplit : r ⬝ᵥ y = r 0 * y 0 + v ⬝ᵥ tailVec y := by
          simp [dotProduct, Fin.sum_univ_succ, hvdef, tailVec]
        have : r 0 * y 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hy0
        linarith
      have hinvD : (Matrix.diagonal w)⁻¹ = Matrix.diagonal (fun i => (w i)⁻¹) := by
        apply Matrix.inv_eq_left_inv
        rw [diagonal_mul_diagonal]
        have : (fun i => (w i)⁻¹ * w i) = fun _ => (1:ℝ) := by
          funext i; exact inv_mul_cancel₀ (hw i).ne'
        rw [this, diagonal_one]
      have hmem : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          (s • ξ - aa) ⬝ᵥ (N⁻¹ *ᵥ (s • ξ - aa)) ≤ 1 := by
        intro s hs0 hs1
        have h1 : s • ξ ∈ LinearOptimization.ellipsoid 0 (Matrix.diagonal w) ∩
            {x | db ⬝ᵥ 0 ≤ db ⬝ᵥ x} := by
          constructor
          · show (s • ξ - 0) ⬝ᵥ ((Matrix.diagonal w)⁻¹ *ᵥ (s • ξ - 0)) ≤ 1
            rw [hinvD, sub_zero]
            have he : (s • ξ) ⬝ᵥ (Matrix.diagonal (fun i => (w i)⁻¹) *ᵥ (s • ξ)) =
                s ^ 2 * ((y 0)⁻¹) ^ 2 * ∑ i, y i.succ ^ 2 / w i := by
              simp only [dotProduct, mulVec_diagonal, Pi.smul_apply, smul_eq_mul, hξdef, tailVec]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              have := (hw i).ne'
              field_simp
            rw [he]
            have h2 : ((y 0)⁻¹) ^ 2 * ∑ i, y i.succ ^ 2 / w i ≤ 1 := by
              rw [inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]; exact hy1
            have h3 : s ^ 2 ≤ 1 := by nlinarith
            have h4 : 0 ≤ ((y 0)⁻¹) ^ 2 * ∑ i, y i.succ ^ 2 / w i :=
              mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hw i).le))
            rw [mul_assoc]
            nlinarith
          · show db ⬝ᵥ 0 ≤ db ⬝ᵥ (s • ξ)
            rw [dotProduct_zero, hdbdef, hξdef, smul_dotProduct, dotProduct_smul, dotProduct_smul,
              smul_eq_mul, smul_eq_mul, smul_eq_mul]
            have : 0 ≤ (Real.sqrt (v ⬝ᵥ v))⁻¹ := by positivity
            have : 0 ≤ (y 0)⁻¹ := by positivity
            positivity
        exact hincl h1
      have hsee : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          ∑ i : Fin m, (Vᵀ *ᵥ (Fin.cons 1 (s • ξ) : Fin (m+1) → ℝ)) i.succ ^ 2 / (-μ i.succ) ≤
            (Vᵀ *ᵥ (Fin.cons 1 (s • ξ) : Fin (m+1) → ℝ)) 0 ^ 2 / μ 0 :=
        fun s hs0 hs1 => seeger aa N hNpd V hV μ hMV hμ0 hneg (s • ξ) (hmem s hs0 hs1)
      set zh := Vᵀ *ᵥ (Fin.cons 1 ξ : Fin (m+1) → ℝ) with hzhdef
      have haff : ∀ s : ℝ, (Vᵀ *ᵥ (Fin.cons 1 (s • ξ) : Fin (m+1) → ℝ)) 0 =
          V 0 0 + s * (zh 0 - V 0 0) := by
        intro s
        simp only [hzhdef, mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          transpose_apply, Pi.smul_apply, smul_eq_mul, mul_one]
        have : ∑ x : Fin m, V x.succ 0 * (s * ξ x) = s * ∑ x : Fin m, V x.succ 0 * ξ x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)
        rw [this]; ring
      have hz0 : 0 ≤ zh 0 := by
        by_contra hneg0
        replace hneg0 := lt_of_not_ge hneg0
        set s0 := V 0 0 / (V 0 0 - zh 0) with hs0def
        have hden : 0 < V 0 0 - zh 0 := by linarith
        have hs0pos : 0 ≤ s0 := div_nonneg hV00.le hden.le
        have hs0le : s0 ≤ 1 := by rw [div_le_one hden]; linarith
        have hzero : (Vᵀ *ᵥ (Fin.cons 1 (s0 • ξ) : Fin (m+1) → ℝ)) 0 = 0 := by
          rw [haff, hs0def]; field_simp; ring
        have hS := hsee s0 hs0pos hs0le
        rw [hzero] at hS
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at hS
        have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)),
            0 ≤ (Vᵀ *ᵥ (Fin.cons 1 (s0 • ξ) : Fin (m+1) → ℝ)) i.succ ^ 2 / (-μ i.succ) :=
          fun i _ => div_nonneg (sq_nonneg _) (by linarith [hneg i])
        have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).1
          (le_antisymm hS (Finset.sum_nonneg hterm))
        have hvec : (Vᵀ *ᵥ (Fin.cons 1 (s0 • ξ) : Fin (m+1) → ℝ)) = 0 := by
          ext k; refine Fin.cases ?_ (fun j => ?_) k
          · exact hzero
          · have := hall j (Finset.mem_univ j)
            rcases div_eq_zero_iff.1 this with h | h
            · simpa using h
            · linarith [hneg j]
        have hback : (Fin.cons 1 (s0 • ξ) : Fin (m+1) → ℝ) = 0 := by
          rw [← one_mulVec (Fin.cons 1 (s0 • ξ) : Fin (m+1) → ℝ), ← VVt V hV, ← mulVec_mulVec,
            hvec, mulVec_zero]
        have := congrFun hback 0
        simp at this
      have hzy : Vᵀ *ᵥ y = (y 0) • zh := by
        rw [hzhdef]; conv_lhs => rw [hyξ]
        rw [mulVec_smul]
      rw [hzy]
      simp only [Pi.smul_apply, smul_eq_mul]
      refine ⟨mul_nonneg hy0 hz0, ?_⟩
      have hS1 := hsee 1 zero_le_one le_rfl
      rw [one_smul] at hS1
      have hle : ∀ i : Fin m, zh i.succ ^ 2 / w' i ≤ zh i.succ ^ 2 / (-μ i.succ) := by
        intro i
        have hμi : |μ i.succ| = -μ i.succ := abs_of_neg (hneg i)
        have := hint i
        rw [hμi] at this
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [hneg i]) this
      have hsum_le : ∑ i, zh i.succ ^ 2 / w' i ≤ zh 0 ^ 2 := by
        calc ∑ i, zh i.succ ^ 2 / w' i ≤ ∑ i : Fin m, zh i.succ ^ 2 / (-μ i.succ) :=
              Finset.sum_le_sum (fun i _ => hle i)
          _ ≤ zh 0 ^ 2 / μ 0 := hS1
          _ ≤ zh 0 ^ 2 := div_le_self (sq_nonneg _) hμ1
      have : ∑ i, (y 0 * zh i.succ) ^ 2 / w' i = (y 0) ^ 2 * ∑ i, zh i.succ ^ 2 / w' i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [this, mul_pow]
      exact mul_le_mul_of_nonneg_left hsum_le (sq_nonneg _)
    · -- y 0 = 0 forces y = 0
      have hyt : ∀ i : Fin m, y i.succ = 0 := by
        have hterm : ∀ i ∈ Finset.univ, 0 ≤ y i.succ ^ 2 / w i :=
          fun i _ => div_nonneg (sq_nonneg _) (hw i).le
        have hs : ∑ i, y i.succ ^ 2 / w i = 0 := by
          rw [← hy0z] at hy1; simp at hy1
          exact le_antisymm hy1 (Finset.sum_nonneg hterm)
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hs i (Finset.mem_univ i)
        rcases div_eq_zero_iff.1 this with h | h
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
        · exact absurd h (hw i).ne'
      have hy : y = 0 := by
        ext k; refine Fin.cases ?_ (fun j => ?_) k
        · exact hy0z.symm
        · exact hyt j
      rw [hy, mulVec_zero]
      simp
  · -- rate
    have hvpos := dot_self_pos v htail
    have hq : 0 < ∑ i, w i * v i ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 htail
      have : 0 < w i * v i ^ 2 :=
        mul_pos (hw i) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => w j * v j ^ 2)
        (fun j _ => mul_nonneg (hw j).le (sq_nonneg _)) (Finset.mem_univ i))
    have hdet := det_ellUpd w db (by rw [hdq]; positivity)
    rw [← hNdef, hNP] at hdet
    have hPP : P.det * Pᵀ.det = 1 := by
      rw [← det_mul]
      have : P * Pᵀ = 1 := by simpa using (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).1 hP
      rw [this, det_one]
    have hprod : ∏ i, w' i =
        ((m:ℝ) ^ 2 / ((m:ℝ) ^ 2 - 1)) ^ m * (∏ i, w i) * (1 - 2 / ((m:ℝ) + 1)) := by
      rw [← hdet, det_mul, det_mul, det_diagonal]
      linear_combination (∏ i, w' i) * hPP.symm
    rw [hprod]
    have hr := rate_ineq m hm
    have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
    have hexp : Real.exp (-(1 / (m:ℝ))) ≤ Real.exp (-(1 / (2 * (m:ℝ)))) := by
      apply Real.exp_le_exp.2
      have : 1 / (2 * (m:ℝ)) ≤ 1 / (m:ℝ) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      linarith
    have hpw : 0 ≤ ∏ i, w i := Finset.prod_nonneg (fun i _ => (hw i).le)
    nlinarith
