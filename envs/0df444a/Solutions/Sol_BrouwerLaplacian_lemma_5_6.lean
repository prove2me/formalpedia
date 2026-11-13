-- Prove2me | solution 1 for BrouwerLaplacian.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:20:14.402979+00:00
-- url     : https://prove2.me/submissions/3ffaf5a6-3269-429b-be31-c3aa6dd99f5b

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_routingM
import Theorems.Thm_BrouwerLaplacian_lemma_5_2
import Theorems.Thm_BrouwerLaplacian_lemma_5_3

section
namespace BrouwerLaplacian.Dev.Common

open Matrix

theorem trace_eq_rank {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P * P = P) (hk : P.rank = k) :
    P.trace = k := by
  have hproj : LinearMap.IsProj (LinearMap.range (Matrix.toLin' P)) (Matrix.toLin' P) := by
    have : IsIdempotentElem (Matrix.toLin' P) := by
      show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
    exact (LinearMap.isProj_range_iff_isIdempotentElem _).2 this
  have h := hproj.trace
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin n)), LinearMap.toMatrix_eq_toMatrix'] at h
  rw [LinearMap.toMatrix'_toLin'] at h
  rw [h]
  have : P.rank = Module.finrank ℝ (LinearMap.range (Matrix.toLin' P)) := by
    rw [Matrix.rank]; rfl
  rw [← this, hk]

end BrouwerLaplacian.Dev.Common
end

section
namespace BrouwerLaplacian.Dev.L52

open Finset Matrix

theorem rowsum {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP1 : P *ᵥ (fun _ => 1) = 0) (i : Fin n) :
    ∑ j, P i j = 0 := by
  have := congrFun hP1 i
  simpa [Matrix.mulVec, dotProduct] using this

end BrouwerLaplacian.Dev.L52

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.OpN

open Matrix WainwrightHDS.NucNorm

end BrouwerLaplacian.Dev.OpN
end

section
namespace BrouwerLaplacian.Dev.NLem

open Finset Matrix BrouwerLaplacian

theorem cent_apply {n : ℕ} (i j : Fin n) :
    centering n i j = (if i = j then 1 else 0) - (n : ℝ)⁻¹ := by
  simp [centering, onesMat, Matrix.one_apply]

theorem cent_mulVec {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (centering n *ᵥ x) i = x i - (n : ℝ)⁻¹ * ∑ j, x j := by
  simp only [Matrix.mulVec, dotProduct, cent_apply, sub_mul, sum_sub_distrib, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, if_true]
  rw [← mul_sum]

end BrouwerLaplacian.Dev.NLem

namespace BrouwerLaplacian
open Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L56

open Finset Matrix BrouwerLaplacian

theorem sum_ne {n : ℕ} (g : Fin n → Fin n → ℝ) (h : ∀ i, g i i = 0) :
    ∑ i, ∑ j with i ≠ j, g i j = ∑ i, ∑ j, g i j := by
  refine sum_congr rfl fun i _ => ?_
  rw [sum_filter]
  refine sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst hij; simp [h]
  · simp [hij]

theorem rowM {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) (i : Fin n) :
    (routingM P *ᵥ fun _ => (1 : ℝ)) i = n * P i i + ((k : ℝ) - n + 1) := by
  have htr : ∑ i, P i i = k := Common.trace_eq_rank P hP.2.1 hP.2.2
  have hrow := L52.rowsum hP1 i
  have e : ∀ j, routingM P i j = (P i i + P j j - 2 * P i j - 1) + (if i = j then 1 else 0) := by
    intro j
    by_cases hij : i = j
    · subst hij; simp [routingM]; ring
    · simp [routingM, hij]
  simp only [Matrix.mulVec, dotProduct, mul_one, e, sum_add_distrib, sum_sub_distrib,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum, htr, hrow, sum_ite_eq,
    mem_univ, if_true]
  ring

theorem vdiff {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) (i j : Fin n) :
    routingV P i - routingV P j = n * (P i i - P j j) := by
  unfold routingV
  rw [NLem.cent_mulVec, NLem.cent_mulVec, rowM hP hP1, rowM hP hP1]; ring

theorem sumv {n : ℕ} (w : Fin n → ℝ) : ∑ i, (centering n *ᵥ w) i = 0 := by
  by_cases hn : n = 0
  · subst hn; simp
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [NLem.cent_mulVec, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp; ring

theorem pair_sum {n : ℕ} (v : Fin n → ℝ) (hv : ∑ i, v i = 0) :
    ∑ i, ∑ j, (v i - v j) ^ 2 = 2 * n * ∑ i, v i ^ 2 := by
  have : ∀ i j, (v i - v j) ^ 2 = v i ^ 2 + v j ^ 2 - 2 * (v i * v j) := fun i j => by ring
  simp only [this, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_sum, ← sum_mul, hv]
  ring

theorem d_sum {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    ∑ i, ∑ j with i ≠ j, (P i i - P j j) ^ 2 = (2 / (n : ℝ)) * ∑ i, routingV P i ^ 2 := by
  by_cases hn : n = 0
  · subst hn; simp
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [sum_ne _ (fun i => by ring)]
  have hv : ∑ i, routingV P i = 0 := sumv _
  have h1 := pair_sum (routingV P) hv
  have h2 : ∑ i, ∑ j, (routingV P i - routingV P j) ^ 2
      = (n : ℝ) ^ 2 * ∑ i, ∑ j, (P i i - P j j) ^ 2 := by
    rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
    rw [vdiff hP hP1]; ring
  rw [h2] at h1
  field_simp
  nlinarith [h1, sq_nonneg (n : ℝ), mul_self_pos.2 hn']

theorem pos_part (a : ℝ) : max (a - 1) 0 = (1 / 4) * (a ^ 2 - (1 - |a - 1|) ^ 2) := by
  rcases le_or_gt 1 a with h | h
  · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]; ring
  · rw [abs_of_neg (by linarith), max_eq_right (by linarith)]; ring

theorem main {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    ∑ i, ∑ j with i ≠ j, max (P i i + P j j - 2 * P i j - 1) 0
      ≤ (k : ℝ) * ((k : ℝ) + 1) := by
  have h52 := BrouwerLaplacian.lemma_5_2 P hP hP1
  have h53 := BrouwerLaplacian.lemma_5_3 P hP hP1
  rw [← d_sum hP hP1] at h53
  have hpt : ∀ i, ∑ j with i ≠ j, max (P i i + P j j - 2 * P i j - 1) 0
      = ∑ j with i ≠ j, (1 / 4) * (((P i i + P j j - 2 * P i j) ^ 2 - (P i i - P j j) ^ 2)
          + ((P i i - P j j) ^ 2 - (1 - |routingM P i j|) ^ 2)) := by
    intro i
    refine sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := (mem_filter.1 hj).2
    have : routingM P i j = P i i + P j j - 2 * P i j - 1 := by simp [routingM, hij]
    rw [this, pos_part]; ring_nf
  simp_rw [hpt, ← mul_sum, sum_add_distrib]
  have e : ∑ x, ∑ y with x ≠ y, ((P x x - P y y) ^ 2 - (1 - |routingM P x y|) ^ 2)
      = ∑ x, ∑ y with x ≠ y, (P x x - P y y) ^ 2
        - ∑ x, ∑ y with x ≠ y, (1 - |routingM P x y|) ^ 2 := by
    simp only [sum_sub_distrib]
  rw [e]
  linarith

end BrouwerLaplacian.Dev.L56

namespace BrouwerLaplacian
open Finset Matrix
theorem chk_lemma_5_6 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    ∑ i, ∑ j with i ≠ j, max (P i i + P j j - 2 * P i j - 1) 0
      ≤ (k : ℝ) * ((k : ℝ) + 1) := Dev.L56.main P hP hP1
end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_lemma_5_6 := @BrouwerLaplacian.chk_lemma_5_6
