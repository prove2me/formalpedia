-- Prove2me | solution 1 for DepthOneQExp.eq_2_51_2_52
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:57:45.681639+00:00
-- url     : https://prove2.me/submissions/c2988cf3-1773-4e03-ac37-7a33d476e571

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_aVec
import Definitions.Def_DepthOneQExp_hOp

open DepthOneQExp Matrix
open scoped Kronecker

namespace DepthOneQExp.Eq25152Aux

variable {n : ℕ}

abbrev κ (n : ℕ) := MITMSynthesis.Q n × MITMSynthesis.Q n

def sg (x : MITMSynthesis.Q n) : ℂ := if bit x 0 = 1 then -1 else 1

def X (n : ℕ) : MITMSynthesis.Q n → MITMSynthesis.Q n := xPerm n 0

theorem X_apply (x : MITMSynthesis.Q n) : X n x = fun (k : Fin n) => if (k : ℕ) = 0 % n then x k + 1 else x k := rfl

theorem X_X (x : MITMSynthesis.Q n) : X n (X n x) = x := by
  funext k
  simp only [X_apply]
  split_ifs
  · generalize x k = c; revert c; decide
  · rfl

theorem xPerm_symm : (xPerm n 0).symm = xPerm n 0 := by
  ext x : 1
  rw [Equiv.symm_apply_eq]
  exact (X_X x).symm

theorem perm_mulVec {α : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (v : α → ℂ) :
    permToMatrix σ *ᵥ v = fun p => v (σ.symm p) := by
  funext p
  simp only [mulVec, dotProduct, permToMatrix, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm p)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h; apply hb; rw [h, Equiv.symm_apply_apply]
  · simp

theorem kron_perm {α : Type} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) :
    permToMatrix σ ⊗ₖ permToMatrix τ = permToMatrix (Equiv.prodCongr σ τ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [kroneckerMap_apply, permToMatrix, Equiv.prodCongr_apply, Prod.map, Prod.mk.injEq]
  by_cases h1 : a = σ c <;> by_cases h2 : b = τ d <;> simp [h1, h2]

theorem zMat_kron : zMat n 0 ⊗ₖ zMat n 0 =
    diagonal (fun p : κ n => sg p.1 * sg p.2) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [kroneckerMap_apply, zMat, diagonal_apply, Prod.mk.injEq, sg]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2]

theorem hOp_mulVec (v : κ n → ℂ) :
    hOp n *ᵥ v = fun p => v (X n p.1, X n p.2) + sg p.1 * sg p.2 * v p := by
  rw [hOp, add_mulVec, kron_perm, perm_mulVec, zMat_kron]
  funext p
  simp only [mulVec_diagonal, Pi.add_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, xPerm_symm, Prod.map]
  rfl

theorem sg_X (hn : 0 < n) (x : MITMSynthesis.Q n) : sg (X n x) = - sg x := by
  have h : 0 % n < n := Nat.mod_lt _ hn
  simp only [sg, bit, h, dif_pos, X_apply, if_true]
  generalize x ⟨0 % n, h⟩ = c
  fin_cases c <;> norm_num

theorem sum_sg (hn : 0 < n) : ∑ x : MITMSynthesis.Q n, sg x = 0 := by
  have h : ∑ x : MITMSynthesis.Q n, sg (X n x) = ∑ x : MITMSynthesis.Q n, sg x :=
    Equiv.sum_comp (xPerm n 0) sg
  simp only [sg_X hn, Finset.sum_neg_distrib] at h
  linear_combination -h / 2

theorem sg_sq (x : MITMSynthesis.Q n) : sg x * sg x = 1 := by
  unfold sg; split_ifs <;> norm_num

theorem sg_zero : sg (0 : MITMSynthesis.Q n) = 1 := by
  unfold sg bit; split_ifs <;> simp_all

theorem X_ne_zero (hn : 0 < n) : X n 0 ≠ 0 := by
  intro h
  have := congrFun h ⟨0 % n, Nat.mod_lt _ hn⟩
  simp [X_apply] at this

theorem X_eq_zero_iff (x : MITMSynthesis.Q n) : X n x = 0 ↔ x = X n 0 := by
  constructor
  · intro h; rw [← h, X_X]
  · rintro rfl; exact X_X 0

theorem X_inj (x y : MITMSynthesis.Q n) : X n x = X n y ↔ x = y :=
  (xPerm n 0).injective.eq_iff

noncomputable def rr (n : ℕ) : ℂ := ((Real.sqrt (2 ^ n))⁻¹ : ℝ)

noncomputable def MM (n : ℕ) : Matrix (κ n) (Fin 5) ℂ := Matrix.of fun p i => aVec n i p

theorem aVec_apply (i : Fin 5) (p : κ n) : aVec n i p =
    ![if p.1 = p.2 then 1 else 0, rr n * rr n,
      (if p.1 = 0 then 1 else 0) * (if p.2 = 0 then 1 else 0),
      (if p.1 = 0 then 1 else 0) * rr n, rr n * (if p.2 = 0 then 1 else 0)] i := by
  fin_cases i <;> rfl

theorem MM_gram (i j : Fin 5) : ((MM n)ᴴ * MM n) i j = ∑ x, ∑ y,
    star (aVec n i (x, y)) * aVec n j (x, y) := by
  simp only [mul_apply, conjTranspose_apply, MM, of_apply, Fintype.sum_prod_type]

theorem MM_H_gram (i j : Fin 5) : ((MM n)ᴴ * hOp n * MM n) i j = ∑ x, ∑ y,
    star (aVec n i (x, y)) * (aVec n j (X n x, X n y) + sg x * sg y * aVec n j (x, y)) := by
  rw [Matrix.mul_assoc]
  simp only [mul_apply, conjTranspose_apply, MM, of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  congr 1
  have := congrFun (hOp_mulVec (n := n) (aVec n j)) (x, y)
  rw [← this]
  simp only [mulVec, dotProduct, Fintype.sum_prod_type]

theorem star_rr : star (rr n) = rr n := by simp [rr]

theorem star_aVec (i : Fin 5) (p : κ n) : star (aVec n i p) = aVec n i p := by
  fin_cases i <;> simp [aVec_apply, apply_ite star, star_rr]

theorem rr_ne : rr n ≠ 0 := by
  simp [rr]

theorem two_pow_eq : (2 : ℂ) ^ n = (rr n ^ 2)⁻¹ := by
  rw [rr, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by positivity)]
  simp

theorem card_Q : (Fintype.card (MITMSynthesis.Q n) : ℂ) = 2 ^ n := by simp

theorem gram1 (_hn : 0 < n) : (MM n)ᴴ * MM n = !![2 ^ n, 1, 1, rr n, rr n; 1, 1, rr n ^ 2, rr n, rr n; 1, rr n ^ 2, 1, rr n, rr n; rr n, rr n, rr n, 1, rr n ^ 2;
      rr n, rr n, rr n, rr n ^ 2, 1] := by
  ext i j
  rw [MM_gram]
  simp only [star_aVec]
  have hr := rr_ne (n := n)
  fin_cases i <;> fin_cases j <;>
  simp [aVec_apply, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq'] <;>
  first | rfl | ring1 | (simp only [two_pow_eq]; field_simp; done)

theorem gram2 (hn : 0 < n) : (MM n)ᴴ * hOp n * MM n = !![2 * 2 ^ n, 2, 2, 2 * rr n, 2 * rr n; 2, 1, 2 * rr n ^ 2, rr n, rr n; 2, 2 * rr n ^ 2, 1, rr n, rr n;
      2 * rr n, rr n, rr n, 0, 2 * rr n ^ 2; 2 * rr n, rr n, rr n, 2 * rr n ^ 2, 0] := by
  ext i j
  rw [MM_H_gram]
  simp only [star_aVec]
  have hr := rr_ne (n := n)
  have h1 := X_ne_zero hn
  have h2 := (X_ne_zero hn).symm
  fin_cases i <;> fin_cases j <;>
  simp [aVec_apply, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', X_inj, X_eq_zero_iff,
    sg_X hn, sg_zero, sg_sq, h1, h2, Finset.sum_add_distrib, mul_add, add_mul, ← Finset.mul_sum,
    ← Finset.sum_mul, sum_sg hn] <;>
  first | rfl | ring1 | (simp only [two_pow_eq]; field_simp; done) | (simp only [two_pow_eq]; field_simp; ring1)

set_option maxHeartbeats 4000000 in
theorem det_formula (N r t : ℂ) (hr : r ≠ 0) (hN : N = (r ^ 2)⁻¹) :
    (!![2 * N, 2, 2, 2 * r, 2 * r; 2, 1, 2 * r ^ 2, r, r; 2, 2 * r ^ 2, 1, r, r;
      2 * r, r, r, 0, 2 * r ^ 2; 2 * r, r, r, 2 * r ^ 2, 0] - t • !![N, 1, 1, r, r; 1, 1, r ^ 2, r, r; 1, r ^ 2, 1, r, r; r, r, r, 1, r ^ 2;
      r, r, r, r ^ 2, 1]).det =
      -((N - 2) / N ^ 4) * (t - 2) * (t * (N - 1) + 2) ^ 2 * (t * (N - 1) - N + 2) ^ 2 := by
  have e : (!![2 * N, 2, 2, 2 * r, 2 * r; 2, 1, 2 * r ^ 2, r, r; 2, 2 * r ^ 2, 1, r, r;
      2 * r, r, r, 0, 2 * r ^ 2; 2 * r, r, r, 2 * r ^ 2, 0] - t • !![N, 1, 1, r, r; 1, 1, r ^ 2, r, r; 1, r ^ 2, 1, r, r; r, r, r, 1, r ^ 2;
      r, r, r, r ^ 2, 1] : Matrix (Fin 5) (Fin 5) ℂ) =
      !![2 * N - t * N, 2 - t, 2 - t, 2 * r - t * r, 2 * r - t * r;
         2 - t, 1 - t, 2 * r ^ 2 - t * r ^ 2, r - t * r, r - t * r;
         2 - t, 2 * r ^ 2 - t * r ^ 2, 1 - t, r - t * r, r - t * r;
         2 * r - t * r, r - t * r, r - t * r, 0 - t, 2 * r ^ 2 - t * r ^ 2;
         2 * r - t * r, r - t * r, r - t * r, 2 * r ^ 2 - t * r ^ 2, 0 - t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e]
  simp only [det_succ_row_zero, Fin.sum_univ_succ, det_unique, Fin.sum_univ_zero]
  simp [Fin.succAbove, Fin.lt_def]
  subst hN
  field_simp
  ring

end DepthOneQExp.Eq25152Aux

open DepthOneQExp.Eq25152Aux in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    let N : ℂ := 2 ^ n
    let r : ℂ := ((Real.sqrt (2 ^ n))⁻¹ : ℝ)
    let M : Matrix (MITMSynthesis.Q n × MITMSynthesis.Q n) (Fin 5) ℂ :=
      Matrix.of fun p i => aVec n i p
    Mᴴ * M = !![N, 1, 1, r, r; 1, 1, r ^ 2, r, r; 1, r ^ 2, 1, r, r; r, r, r, 1, r ^ 2;
      r, r, r, r ^ 2, 1] ∧
    Mᴴ * hOp n * M = !![2 * N, 2, 2, 2 * r, 2 * r; 2, 1, 2 * r ^ 2, r, r; 2, 2 * r ^ 2, 1, r, r;
      2 * r, r, r, 0, 2 * r ^ 2; 2 * r, r, r, 2 * r ^ 2, 0] ∧
    ∀ t : ℂ, (Mᴴ * hOp n * M - t • (Mᴴ * M)).det =
      -((N - 2) / N ^ 4) * (t - 2) * (t * (N - 1) + 2) ^ 2 * (t * (N - 1) - N + 2) ^ 2 := by
  intro N r M
  have g1 : Mᴴ * M = _ := gram1 (n := n) (by omega)
  have g2 : Mᴴ * hOp n * M = _ := gram2 (n := n) (by omega)
  refine ⟨g1, g2, fun t => ?_⟩
  rw [g1, g2]
  exact det_formula _ _ _ rr_ne two_pow_eq
