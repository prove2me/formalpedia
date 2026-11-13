-- Prove2me | solution 1 for BrouwerLaplacian.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:26:41.831734+00:00
-- url     : https://prove2.me/submissions/81e0c7c5-9763-42ad-9168-65ad7aa9cf7a

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_routingM
import Theorems.Thm_BrouwerLaplacian_lemma_5_5

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

end BrouwerLaplacian.Dev.L56

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L53

open Finset Matrix BrouwerLaplacian

theorem half_sum {n : ℕ} (g : Fin n → Fin n → ℝ) (hg : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j with i ≠ j, g i j = 2 * ∑ i, ∑ j with i < j, g i j := by
  have h1 : ∀ i, ∑ j with i ≠ j, g i j
      = ∑ j with i < j, g i j + ∑ j with j < i, g i j := by
    intro i
    have : (univ.filter fun j => i ≠ j) = (univ.filter fun j => i < j) ∪ (univ.filter fun j => j < i) := by
      ext j
      simp only [mem_filter, mem_union, mem_univ, true_and]
      constructor
      · intro h; exact lt_or_gt_of_ne h
      · rintro (h | h)
        · exact ne_of_lt h
        · exact ne_of_gt h
    rw [this, sum_union]
    rw [disjoint_filter]; intro j _ h1 h2; exact absurd h1 (not_lt.2 h2.le)
  simp only [h1, sum_add_distrib]
  have h2 : ∑ i, ∑ j with j < i, g i j = ∑ i, ∑ j with i < j, g i j := by
    simp only [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hg]
  rw [h2]; ring

theorem M_symm {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k) (i j : Fin n) :
    routingM P i j = routingM P j i := by
  by_cases hij : i = j
  · subst hij; rfl
  · have : ¬ j = i := fun h => hij h.symm
    simp [routingM, hij, this, L52.symm_of hP i j]; ring

theorem main {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    ∑ i, ∑ j with i ≠ j, (1 - |routingM P i j|) ^ 2
      ≥ (2 / (n : ℝ)) * ∑ i, routingV P i ^ 2 := by
  obtain ⟨-, h55⟩ := BrouwerLaplacian.lemma_5_5 P hP hP1
  set v := routingV P with hv
  set w : Fin n → Fin n → ℝ := fun i j => 1 - |routingM P i j| with hw
  rw [half_sum (fun i j => (1 - |routingM P i j|) ^ 2) (fun i j => by rw [M_symm hP i j])]
  have hvsum : ∑ i, v i = 0 := L56.sumv _
  have hB : ∑ i, ∑ j with i < j, (v i - v j) ^ 2 = n * ∑ i, v i ^ 2 := by
    have := half_sum (fun i j => (v i - v j) ^ 2) (fun i j => by ring)
    rw [L56.sum_ne _ (fun i => by ring), L56.pair_sum v hvsum] at this
    linarith
  by_cases hn : n = 0
  · subst hn; simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set A := ∑ i, ∑ j with i < j, (1 - |routingM P i j|) ^ 2 with hA
  -- Cauchy–Schwarz over the pairs i < j
  have hcs : (∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |v i - v j|) ^ 2
      ≤ A * (n * ∑ i, v i ^ 2) := by
    rw [← hB]
    have conv : ∀ F : Fin n → Fin n → ℝ, ∑ i, ∑ j with i < j, F i j
        = ∑ p : Fin n × Fin n, if p.1 < p.2 then F p.1 p.2 else 0 := by
      intro F
      rw [Fintype.sum_prod_type]
      simp only [sum_filter]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin n × Fin n))
      (fun p => if p.1 < p.2 then (1 - |routingM P p.1 p.2|) else 0)
      (fun p => if p.1 < p.2 then |v p.1 - v p.2| else 0)
    have e1 : ∑ p : Fin n × Fin n, (if p.1 < p.2 then (1 - |routingM P p.1 p.2|) else 0)
        * (if p.1 < p.2 then |v p.1 - v p.2| else 0)
        = ∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |v i - v j| := by
      rw [conv]; refine sum_congr rfl fun p _ => ?_; split_ifs <;> simp
    have e2 : ∑ p : Fin n × Fin n, (if p.1 < p.2 then (1 - |routingM P p.1 p.2|) else 0) ^ 2
        = A := by
      rw [hA, conv]; refine sum_congr rfl fun p _ => ?_; split_ifs <;> simp
    have e3 : ∑ p : Fin n × Fin n, (if p.1 < p.2 then |v p.1 - v p.2| else 0) ^ 2
        = ∑ i, ∑ j with i < j, (v i - v j) ^ 2 := by
      rw [conv]; refine sum_congr rfl fun p _ => ?_; split_ifs <;> simp [sq_abs]
    rw [e1, e2, e3] at cs
    exact cs
  have hT : ∑ i, v i ^ 2 ≤ ∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |v i - v j| := h55
  have hsq : 0 ≤ ∑ i, v i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  rcases hsq.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
    positivity
  · have h1 : (∑ i, v i ^ 2) ^ 2 ≤ A * (n * ∑ i, v i ^ 2) :=
      le_trans (pow_le_pow_left₀ hsq hT 2) hcs
    have : (∑ i, v i ^ 2) ≤ A * n := by nlinarith
    rw [ge_iff_le, div_mul_eq_mul_div, div_le_iff₀ hnpos]
    nlinarith

end BrouwerLaplacian.Dev.L53

namespace BrouwerLaplacian
open Finset Matrix
theorem chk_lemma_5_3 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    ∑ i, ∑ j with i ≠ j, (1 - |routingM P i j|) ^ 2
      ≥ (2 / (n : ℝ)) * ∑ i, routingV P i ^ 2 := Dev.L53.main P hP hP1
end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_lemma_5_3 := @BrouwerLaplacian.chk_lemma_5_3
