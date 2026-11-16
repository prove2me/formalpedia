-- Prove2me | solution 1 for DetANN.theorem_1_1_correctness
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T03:08:48.113212+00:00
-- url     : https://prove2.me/submissions/06fed5e3-520d-4e44-b6e8-5aa9e56248d4

import Mathlib
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_TupleFamily
import Theorems.Thm_DetANN_sylvester_hadamard
import Theorems.Thm_DetANN_theorem_3_2_greedy
import Theorems.Thm_DetANN_eq_27
import Theorems.Thm_DetANN_lemma_7_2
import Theorems.Thm_DetANN_walk_family_uniform
import Theorems.Thm_DetANN_lemma_7_1_graph
import Theorems.Thm_DetANN_theorem_1_1_parameters

open DetANN

namespace DetANNCorrAux

/-! ### Zero padding is a linear isometry -/

lemma padVec_sub {d : ℕ} (m : ℕ) (x y : EuclideanSpace ℝ (Fin d)) :
    padVec m (x - y) = padVec m x - padVec m y := by
  ext r
  simp only [padVec, PiLp.sub_apply, WithLp.ofLp_sub, Pi.sub_apply]
  split_ifs <;> simp

lemma padVec_norm {d : ℕ} (m : ℕ) (hd : d ≤ m) (x : EuclideanSpace ℝ (Fin d)) :
    ‖padVec m x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [padVec, Real.norm_eq_abs, sq_abs]
  have hm : ∑ r : Fin m, (if h : (r : ℕ) < d then x.ofLp ⟨r, h⟩ else 0) ^ 2 =
      ∑ r ∈ Finset.range m, (if h : r < d then x.ofLp ⟨r, h⟩ ^ 2 else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => if h : r < d then x.ofLp ⟨r, h⟩ ^ 2 else 0) m]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> simp
  have hdd : ∑ r : Fin d, x.ofLp r ^ 2 =
      ∑ r ∈ Finset.range d, (if h : r < d then x.ofLp ⟨r, h⟩ ^ 2 else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => if h : r < d then x.ofLp ⟨r, h⟩ ^ 2 else 0) d]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [r.2]
  rw [hm, hdd, ← Finset.sum_range_add_sum_Ico _ hd]
  have : ∑ r ∈ Finset.Ico d m, (if h : r < d then x.ofLp ⟨r, h⟩ ^ 2 else 0) = 0 :=
    Finset.sum_eq_zero fun r hr => by
      have : ¬ r < d := by simp [Finset.mem_Ico] at hr; omega
      simp [this]
  simp only [WithLp.ofLp_toLp]
  rw [this, add_zero]

lemma padVec_dist {d : ℕ} (m : ℕ) (hd : d ≤ m) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖padVec m x - padVec m y‖ = ‖x - y‖ := by
  rw [← padVec_sub, padVec_norm m hd]

end DetANNCorrAux

open DetANNCorrAux in
theorem solution :
    ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ → ∀ (d n k : ℕ), d ≤ 2 ^ k →
      ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∀ (q : EuclideanSpace ℝ (Fin d)) (x : Fin (2 ^ k) → Fin n),
            LocalGuarantee (annBlocks C₀ k P ε) (annTuples k ε) (paddedSet k P)
                (padVec (2 ^ k) q) (fun v => padVec (2 ^ k) (P (x v))) (1 + ε / 100) →
              ∃ v, ∀ i, ‖q - P (x v)‖ ≤ (1 + ε) * ‖q - P i‖ := by
  obtain ⟨C₀s, hC₀s, hG⟩ := theorem_3_2_greedy
  refine ⟨C₀s, hC₀s, ?_⟩
  intro C₀ hC₀ d n k hdk P hP ε hε0 hε1 q x hloc
  have hv0 : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
  -- one point: nothing to prove
  by_cases hn : n ≤ 1
  · refine ⟨⟨0, hv0⟩, fun i => ?_⟩
    have : x ⟨0, hv0⟩ = i := Fin.ext (by have := (x ⟨0, hv0⟩).2; have := i.2; omega)
    rw [this]
    nlinarith [norm_nonneg (q - P i)]
  push Not at hn
  -- the balanced block system of Theorem 3.2 for the padded points
  set τ := annTau ε with hτdef
  set Pp := paddedSet k P with hPp
  set D := diffSet k P with hD
  have hτ0 : 0 < τ := by rw [hτdef, annTau]; positivity
  have hτ1 : τ < 1 := by
    rw [hτdef, annTau]
    have : ε ^ 2 < 1 := by nlinarith
    rw [div_lt_one (by norm_num)]; nlinarith
  obtain ⟨hpm, hhad, -⟩ := sylvester_hadamard k
  have hDne : ∀ v ∈ D, v ≠ 0 := by
    intro v hv
    simp only [hD, diffSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := hv
    intro h0
    have h1 : ‖padVec (2 ^ k) (P i) - padVec (2 ^ k) (P j)‖ = ‖P i - P j‖ := padVec_dist _ hdk _ _
    rw [h0, norm_zero] at h1
    have : P i = P j := sub_eq_zero.mp (norm_eq_zero.mp h1.symm)
    exact absurd (hP this) (ne_of_lt hij)
  have hcover : ∀ a ∈ Pp, ∀ b ∈ Pp, a ≠ b → a - b ∈ D ∨ b - a ∈ D := by
    intro a ha b hb hab
    simp only [hPp, paddedSet, Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    have hij : i ≠ j := fun e => hab (by rw [e])
    rcases lt_or_gt_of_ne hij with h | h
    · left; simp only [hD, diffSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(i, j), h, rfl⟩
    · right; simp only [hD, diffSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(j, i), h, rfl⟩
  have hcard : 1 ≤ D.card := by
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    refine ⟨padVec (2 ^ k) (P ⟨0, by omega⟩) - padVec (2 ^ k) (P ⟨1, by omega⟩), ?_⟩
    simp only [hD, diffSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def], rfl⟩
  obtain ⟨-, -, hA⟩ := hG C₀ hC₀ (2 ^ k) (Nat.one_le_two_pow) (sylvester k) hpm hhad τ hτ0 hτ1
    Pp D hDne hcover hcard
  -- the expander and the walk tuples
  obtain ⟨hθ0, hθ1, hund, hW⟩ := lemma_7_1_graph k
  obtain ⟨hℓ1, hρ, hκ, hfinal⟩ := theorem_1_1_parameters ε hε0 hε1
  set ℓ := walkLen ε with hℓdef
  have hS : UniformFreq (annTuples k ε) := by
    intro i
    show blockCount (walkEnd (lemma71Nbr k) ℓ) i * 2 ^ k = _
    rw [(walk_family_uniform (lemma71Nbr k) (by norm_num) hund ℓ).1 i]
    simp [Fintype.card_fin, mul_comm, hℓdef]
  -- the nearest neighbor of q
  obtain ⟨istar, -, histar⟩ := Finset.exists_min_image Finset.univ (fun i => ‖q - P i‖)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set ρ := theta0 ^ ℓ with hρdef
  have hρ0 : 0 ≤ ρ := pow_nonneg hθ0.le _
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ (by linarith)
  have hκ0 : 0 ≤ ρ ^ 2 / (1 - ρ ^ 2) := div_nonneg (sq_nonneg _) (by nlinarith)
  have hκV := lemma_7_2 (lemma71Nbr k) (by norm_num) hund theta0 hθ0.le hθ1 hW ℓ hℓ1
    (fun v => padVec (2 ^ k) (P (x v))) (padVec (2 ^ k) (P istar))
  have hmem : ∀ i, padVec (2 ^ k) (P i) ∈ Pp := fun i => by
    simp only [hPp, paddedSet, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨i, rfl⟩
  obtain ⟨-, v, hv⟩ := eq_27 τ (1 + ε / 100) hτ0 hτ1 (by linarith) Pp (annBlocks C₀ k P ε) hA
    (annTuples k ε) hS (padVec (2 ^ k) q) (padVec (2 ^ k) (P istar)) (hmem istar)
    (fun v => padVec (2 ^ k) (P (x v))) (fun v => hmem (x v)) hloc
    (ρ ^ 2 / (1 - ρ ^ 2)) hκ0 hκV
  -- the constant is at most 1 + ε
  set α := 1 + ε / 100 with hαdef
  have hconst : (α + Real.sqrt (2 * α ^ 2 * (ρ ^ 2 / (1 - ρ ^ 2)) + 12 * τ * (1 + α) ^ 2)) /
      Real.sqrt (1 - τ) ≤ 1 + ε := by
    have hτe : ε ^ 2 / 10 ^ 6 = τ := by rw [hτdef, annTau]
    rw [hτe] at hfinal
    refine le_trans ?_ hfinal
    have hs : Real.sqrt (1 - τ) > 0 := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_div_iff_of_pos_right hs]
    have : 2 * α ^ 2 * (ρ ^ 2 / (1 - ρ ^ 2)) + 12 * τ * (1 + α) ^ 2 ≤
        2 * α ^ 2 * (ε ^ 2 / 10 ^ 4) + 12 * τ * (1 + α) ^ 2 := by
      have hκ' : ρ ^ 2 / (1 - ρ ^ 2) ≤ ε ^ 2 / 10 ^ 4 := hκ
      have := mul_le_mul_of_nonneg_left hκ' (by positivity : (0 : ℝ) ≤ 2 * α ^ 2)
      linarith
    linarith [Real.sqrt_le_sqrt this]
  refine ⟨v, fun i => ?_⟩
  rw [padVec_dist _ hdk, padVec_dist _ hdk] at hv
  calc ‖q - P (x v)‖ ≤ _ := hv
    _ ≤ (1 + ε) * ‖q - P istar‖ := mul_le_mul_of_nonneg_right hconst (norm_nonneg _)
    _ ≤ (1 + ε) * ‖q - P i‖ := mul_le_mul_of_nonneg_left (histar i (Finset.mem_univ _)) (by linarith)
