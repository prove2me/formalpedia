-- Prove2me | solution 1 for BrouwerLaplacian.eq_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:52:22.019029+00:00
-- url     : https://prove2.me/submissions/38fc212c-43ef-4611-bf8c-75c0128160fc

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_routingM
import Definitions.Def_BrouwerLaplacian_splitGraphOf

section
namespace BrouwerLaplacian.Dev.Common

open Matrix

end BrouwerLaplacian.Dev.Common
end

section
namespace BrouwerLaplacian.Dev.L52

open Finset Matrix

theorem symm_of {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : BrouwerLaplacian.IsOrthProj P k)
    (i j : Fin n) : P j i = P i j := by
  have := hP.1.apply i j
  simpa using this

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

theorem cent_symm {n : ℕ} (i j : Fin n) : centering n j i = centering n i j := by
  rw [cent_apply, cent_apply]; simp [eq_comm]

theorem cent_mulVec {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (centering n *ᵥ x) i = x i - (n : ℝ)⁻¹ * ∑ j, x j := by
  simp only [Matrix.mulVec, dotProduct, cent_apply, sub_mul, sum_sub_distrib, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, if_true]
  rw [← mul_sum]

theorem cent_mul_cent {n : ℕ} : centering n * centering n = centering n := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [cent_apply, sub_mul, mul_sub, sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    sum_ite_eq, sum_ite_eq', mem_univ, if_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by have := i.pos; positivity
  field_simp; ring

end BrouwerLaplacian.Dev.NLem

namespace BrouwerLaplacian
open Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L56

open Finset Matrix BrouwerLaplacian

end BrouwerLaplacian.Dev.L56

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L53

open Finset Matrix BrouwerLaplacian

theorem M_symm {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k) (i j : Fin n) :
    routingM P i j = routingM P j i := by
  by_cases hij : i = j
  · subst hij; rfl
  · have : ¬ j = i := fun h => hij h.symm
    simp [routingM, hij, this, L52.symm_of hP i j]; ring

end BrouwerLaplacian.Dev.L53

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.E53

open Finset Matrix BrouwerLaplacian

theorem lap_row {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    ∑ j, G.lapMatrix ℝ i j = 0 := by
  have := congrFun (G.lapMatrix_mulVec_const_eq_zero (R := ℝ)) i
  simpa [Matrix.mulVec, dotProduct] using this

theorem lap_mul_cent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    G.lapMatrix ℝ * centering n = G.lapMatrix ℝ := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [NLem.cent_apply, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq, sum_ite_eq',
    mem_univ, if_true, ← sum_mul, lap_row, zero_mul, sub_zero]

theorem cent_mul_lap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    centering n * G.lapMatrix ℝ = G.lapMatrix ℝ := by
  have h := congrArg Matrix.transpose (lap_mul_cent G)
  rw [Matrix.transpose_mul] at h
  have hc : (centering n)ᵀ = centering n := by ext i j; exact NLem.cent_symm i j
  have hl : (G.lapMatrix ℝ)ᵀ = G.lapMatrix ℝ := (G.isSymm_lapMatrix ℝ)
  rwa [hc, hl] at h

theorem trace_mul_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).trace = ∑ i, ∑ j, A i j * B j i := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem trC_M {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hd : ∀ i, M i i = 0)
    (hs : ∀ i j, M j i = M i j) :
    (centering n * M).trace = -(n : ℝ)⁻¹ * ∑ i, ∑ j, M i j := by
  rw [trace_mul_sum]
  simp only [NLem.cent_apply, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq,
    mem_univ, if_true, hd, sum_const_zero, zero_sub]
  simp only [← mul_sum, hs]
  rw [sum_neg_distrib, ← mul_sum]
  ring

theorem trL_M {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : Matrix (Fin n) (Fin n) ℝ) (hd : ∀ i, M i i = 0) (hs : ∀ i j, M j i = M i j) :
    (G.lapMatrix ℝ * M).trace = -∑ i, ∑ j, (if G.Adj i j then M i j else 0) := by
  rw [trace_mul_sum]
  have : ∀ i j, G.lapMatrix ℝ i j * M j i
      = (if i = j then (G.degree i : ℝ) * M i i else 0) - (if G.Adj i j then M i j else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hd]
    · simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hij, hs i j]
  simp only [this, sum_sub_distrib, sum_ite_eq, mem_univ, if_true, hd, mul_zero, zero_sub,
    sum_neg_distrib]

theorem sum_mem_mem {n : ℕ} (f : Fin n → Fin n → ℝ) (A B : Finset (Fin n)) :
    ∑ i, ∑ j, (if i ∈ A ∧ j ∈ B then f i j else 0) = ∑ i ∈ A, ∑ j ∈ B, f i j := by
  have : ∀ i, ∑ j, (if i ∈ A ∧ j ∈ B then f i j else 0)
      = if i ∈ A then ∑ j ∈ B, f i j else 0 := by
    intro i
    by_cases hi : i ∈ A
    · simp only [hi, true_and, if_true]
      rw [sum_ite_mem, univ_inter]
    · simp [hi]
  simp only [this]
  rw [sum_ite_mem, univ_inter]

theorem ite_max (x : ℝ) : (if 0 ≤ x then x else 0) = max x 0 := by
  rcases le_or_gt 0 x with h | h
  · simp [h]
  · simp [h.not_ge, max_eq_right h.le]

theorem adj_split {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hd : ∀ i, M i i = 0)
    (hs : ∀ i j, M j i = M i j) (K : Finset (Fin n)) :
    ∑ i, ∑ j, (if (splitGraphOf M K).Adj i j then M i j else 0)
      = ∑ i ∈ K, ∑ j ∈ K, M i j + 2 * ∑ i ∈ K, ∑ j ∈ Kᶜ, max (M i j) 0 := by
  have pt : ∀ i j, (if (splitGraphOf M K).Adj i j then M i j else 0)
      = (if i ∈ K ∧ j ∈ K then M i j else 0) + (if i ∈ K ∧ j ∈ Kᶜ then max (M i j) 0 else 0)
        + (if j ∈ K ∧ i ∈ Kᶜ then max (M i j) 0 else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [splitGraphOf, hd]
    · by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;>
        simp [splitGraphOf, hij, hi, hj, hs i j, ite_max]
  simp only [pt, sum_add_distrib]
  have e2 : ∀ i j, (if j ∈ K ∧ i ∈ Kᶜ then max (M i j) 0 else 0)
      = (if i ∈ Kᶜ ∧ j ∈ K then max (M i j) 0 else 0) := fun i j => by simp only [and_comm]
  simp only [e2, sum_mem_mem]
  rw [sum_mem_mem (fun i j => M i j) K K]
  have e3 : ∑ i ∈ Kᶜ, ∑ j ∈ K, max (M i j) 0 = ∑ i ∈ K, ∑ j ∈ Kᶜ, max (M i j) 0 := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hs]
  rw [e3]; ring

theorem v_sum {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (K : Finset (Fin n)) :
    ∑ i ∈ K, routingV P i
      = ∑ i ∈ K, ∑ j, routingM P i j - (#K : ℝ) * (n : ℝ)⁻¹ * ∑ i, ∑ j, routingM P i j := by
  have : ∀ i, routingV P i = (∑ j, routingM P i j) - (n : ℝ)⁻¹ * ∑ i, ∑ j, routingM P i j := by
    intro i
    unfold routingV
    rw [NLem.cent_mulVec]
    simp [Matrix.mulVec, dotProduct]
  simp only [this, sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

theorem main {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) (K : Finset (Fin n)) :
    ∑ i ∈ K, routingV P i + ∑ i ∈ K, ∑ j ∈ Kᶜ, |routingM P i j|
      = -Matrix.trace (((splitGraphOf (routingM P) K).lapMatrix ℝ - (#K : ℝ) • centering n)
          * routingN P) := by
  have hd : ∀ i, routingM P i i = 0 := fun i => by simp [routingM]
  have hs : ∀ i j, routingM P j i = routingM P i j := fun i j => (L53.M_symm hP i j).symm
  set G := splitGraphOf (routingM P) K with hG
  set L := G.lapMatrix ℝ with hLdef
  set M := routingM P with hMdef
  set C := centering n with hCdef
  set r : ℝ := (#K : ℝ) with hr
  have hCC : C * C = C := NLem.cent_mul_cent
  have e : C * (L - r • C) * C = L - r • C := by
    rw [Matrix.mul_sub, Matrix.mul_smul, E53.cent_mul_lap G, hCC, Matrix.sub_mul, E53.lap_mul_cent G,
      Matrix.smul_mul, hCC]
  have hA : ((L - r • C) * routingN P).trace = ((L - r • C) * M).trace := by
    unfold routingN
    rw [← Matrix.mul_assoc _ (C * M) C, Matrix.trace_mul_comm]
    have : C * ((L - r • C) * (C * M)) = (C * (L - r • C) * C) * M := by
      simp only [Matrix.mul_assoc]
    rw [this, e]
  rw [hA, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul,
    trL_M G M hd hs, trC_M M hd hs, adj_split M hd hs K, v_sum P K]
  have hsplit : ∀ i, ∑ j, M i j = ∑ j ∈ K, M i j + ∑ j ∈ Kᶜ, M i j := fun i =>
    (sum_add_sum_compl K (fun j => M i j)).symm
  have hab : ∑ i ∈ K, ∑ j ∈ Kᶜ, M i j + ∑ i ∈ K, ∑ j ∈ Kᶜ, |M i j|
      = 2 * ∑ i ∈ K, ∑ j ∈ Kᶜ, max (M i j) 0 := by
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rcases le_or_gt 0 (M i j) with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_neg h, max_eq_right h.le]; ring
  have hAB : ∑ i ∈ K, ∑ j, M i j = ∑ i ∈ K, ∑ j ∈ K, M i j + ∑ i ∈ K, ∑ j ∈ Kᶜ, M i j := by
    simp only [hsplit, sum_add_distrib]
  rw [hAB, smul_eq_mul]
  linarith [hab]

end BrouwerLaplacian.Dev.E53

namespace BrouwerLaplacian
open Finset Matrix
theorem chk_eq_5_3 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) (K : Finset (Fin n)) (hK1 : 1 ≤ #K) (hKn : #K ≤ n - 1) :
    ∑ i ∈ K, routingV P i + ∑ i ∈ K, ∑ j ∈ Kᶜ, |routingM P i j|
      = -Matrix.trace (((splitGraphOf (routingM P) K).lapMatrix ℝ - (#K : ℝ) • centering n)
          * routingN P) := Dev.E53.main P hP hP1 K
end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_eq_5_3 := @BrouwerLaplacian.chk_eq_5_3
