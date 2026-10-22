-- Prove2me | solution 1 for FracPackCover.Covering.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:04:21.11141+00:00
-- url     : https://prove2.me/submissions/143e9f22-4958-48b7-9f5f-19d6b64b4e27

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_Driver

set_option autoImplicit false
open FracPackCover.Covering

lemma fpc_yAx_single {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (x : Fin n → ℝ) :
    yAx A (Pi.single i 1) x = rowVal A x i := by
  unfold yAx
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc) :
    (initCover A b orc = none → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) ∧
    (∀ x, initCover A b orc = some x → x ∈ P ∧ ∀ i, (1 / (m : ℝ)) * b i ≤ rowVal A x i) := by
  classical
  obtain ⟨hA, hb, hconv, hne, hnn⟩ := hdata
  have hsingle : ∀ i : Fin m, ∀ j, 0 ≤ (Pi.single i (1:ℝ) : Fin m → ℝ) j := by
    intro i j; by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have horc' : ∀ i : Fin m, orc (Pi.single i 1) ∈ P ∧
      ∀ x ∈ P, yAx A (Pi.single i 1) x ≤ yAx A (Pi.single i 1) (orc (Pi.single i 1)) :=
    fun i => horc _ (hsingle i)
  have hrow : ∀ x ∈ P, ∀ i, 0 ≤ rowVal A x i := fun x hx i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hnn x hx j)
  constructor
  · intro h
    unfold initCover at h
    split_ifs at h with hex
    obtain ⟨i, hi⟩ := hex
    rintro ⟨x', hx', hx'b⟩
    have := (horc' i).2 x' hx'
    rw [fpc_yAx_single, fpc_yAx_single] at this
    linarith [hx'b i]
  · intro x hx
    unfold initCover at hx
    split_ifs at hx with hex
    push Not at hex
    have hxeq : x = (1 / (m : ℝ)) • ∑ i, orc (Pi.single i 1) := (Option.some.inj hx).symm
    have hmpos : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    constructor
    · rw [hxeq, Finset.smul_sum]
      apply hconv.sum_mem
      · intro i _; positivity
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      · intro i _; exact (horc' i).1
    · intro i
      have hlin : rowVal A x i = (1 / (m:ℝ)) * ∑ k, rowVal A (orc (Pi.single k 1)) i := by
        rw [hxeq]
        simp only [rowVal, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hlin]
      have : rowVal A (orc (Pi.single i 1)) i ≤ ∑ k, rowVal A (orc (Pi.single k 1)) i :=
        Finset.single_le_sum (f := fun k => rowVal A (orc (Pi.single k 1)) i)
          (fun k _ => hrow _ (horc' k).1 i) (Finset.mem_univ i)
      have h2 := hex i
      have h3 : 0 ≤ 1 / (m:ℝ) := by positivity
      nlinarith
