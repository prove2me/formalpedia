-- Prove2me | solution 1 for CPDNetworks.Lower.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:33:15.316986+00:00
-- url     : https://prove2.me/submissions/def20a22-ad05-4a72-910d-6de1a2260732

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting

open scoped Matrix

namespace Aux_CPDeq25
open CPDNetworks.Lower

lemma weight_sum {n T : ℕ} (B : Fin T → Matrix (Fin n) (Fin n) ℝ) :
    ∑ y : Obs n T, weight B y = 1 := by
  have h := Fintype.prod_sum
    (fun (t : Fin T) (yt : Pair n → Bool) => ∏ p, bern (B t p.1.1 p.1.2) (yt p))
  unfold weight
  rw [← h]
  apply Finset.prod_eq_one
  intro t _
  have h2 := Fintype.prod_sum (fun (p : Pair n) (b : Bool) => bern (B t p.1.1 p.1.2) b)
  rw [← h2]
  apply Finset.prod_eq_one
  intro p _
  simp [bern]

lemma weight_nonneg {n T : ℕ} (B : Fin T → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ t i j, 0 ≤ B t i j ∧ B t i j ≤ 1) (y : Obs n T) : 0 ≤ weight B y := by
  unfold weight
  apply Finset.prod_nonneg; intro t _
  apply Finset.prod_nonneg; intro p _
  obtain ⟨h0, h1⟩ := hB t p.1.1 p.1.2
  cases y t p <;> simp [bern] <;> linarith

lemma prob_le_one {n T : ℕ} (B : Fin T → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ t i j, 0 ≤ B t i j ∧ B t i j ≤ 1) (E : Obs n T → Prop) : prob B E ≤ 1 := by
  unfold prob
  rw [← weight_sum B]
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_rfl
  · exact weight_nonneg B hB y

lemma entries_InS {n : ℕ} {ω : ℝ} {Θ Pm : Matrix (Fin n) (Fin n) ℝ} (h : InS ω Θ Pm) :
    ∀ i j, 0 ≤ (Pm ⊙ Θ) i j ∧ (Pm ⊙ Θ) i j ≤ 1 := by
  intro i j
  obtain ⟨a0, a1⟩ := h.1.1.2 i j
  obtain ⟨b0, b1⟩ := h.2.1.1.2 i j
  rw [Matrix.hadamard_apply]
  exact ⟨mul_nonneg b0 a0, mul_le_one₀ b1 a0 a1⟩

end Aux_CPDeq25

open CPDNetworks.Lower Aux_CPDeq25 in
theorem solution {n T : ℕ} (τ : ℕ) (ω α R : ℝ) (ψ : Obs n T → Bool) (hψ : typeI (T := T) ω ψ ≤ α)
    {K₀ K₁ : Type} [Fintype K₀] [Fintype K₁]
    (w₀ : K₀ → ℝ) (Θ₀ Pm₀ : K₀ → Matrix (Fin n) (Fin n) ℝ)
    (hw₀ : ∀ k, 0 ≤ w₀ k) (hw₀1 : ∑ k, w₀ k = 1) (hS : ∀ k, InS ω (Θ₀ k) (Pm₀ k))
    (w₁ : K₁ → ℝ) (Θa Θb Pm₁ : K₁ → Matrix (Fin n) (Fin n) ℝ)
    (hw₁ : ∀ k, 0 ≤ w₁ k) (hw₁1 : ∑ k, w₁ k = 1)
    (hW : ∀ k, InW T τ ω R (Θa k) (Θb k) (Pm₁ k)) :
    let p₀ : Obs n T → ℝ := fun y => ∑ k, w₀ k * weight (nullParam (T := T) (Θ₀ k) (Pm₀ k)) y
    let p₁ : Obs n T → ℝ := fun y => ∑ k, w₁ k * weight (altParam τ (Θa k) (Θb k) (Pm₁ k)) y
    1 - 1 / 2 * ∑ y, |p₁ y - p₀ y| - α ≤ typeII {τ} ω R ψ ∧
      ((∀ y, 0 < p₀ y) →
        1 - 1 / 2 * Real.sqrt (∑ y, p₁ y ^ 2 / p₀ y - 1) - α ≤ typeII {τ} ω R ψ) := by
  intro p₀ p₁
  have hB0 : ∀ k, ∀ t i j, 0 ≤ nullParam (T := T) (Θ₀ k) (Pm₀ k) t i j ∧
      nullParam (T := T) (Θ₀ k) (Pm₀ k) t i j ≤ 1 :=
    fun k t i j => entries_InS (hS k) i j
  have hB1 : ∀ k, ∀ t i j, 0 ≤ altParam (T := T) τ (Θa k) (Θb k) (Pm₁ k) t i j ∧
      altParam (T := T) τ (Θa k) (Θb k) (Pm₁ k) t i j ≤ 1 := by
    intro k t i j
    unfold altParam
    split_ifs
    · exact entries_InS (hW k).2.1 i j
    · exact entries_InS (hW k).1 i j
  -- bounds via sSup
  have bdd0 : BddAbove {p | ∃ Θ Pm, InS ω Θ Pm ∧
      p = prob (nullParam (T := T) Θ Pm) (fun y => ψ y = true)} := by
    refine ⟨1, ?_⟩
    rintro p ⟨Θ, Pm, h, rfl⟩
    exact prob_le_one _ (fun t i j => entries_InS h i j) _
  have bdd1 : BddAbove {p | ∃ τ' ∈ ({τ} : Finset ℕ), ∃ Θa Θb Pm, InW T τ' ω R Θa Θb Pm ∧
      p = prob (altParam τ' Θa Θb Pm) (fun y => ψ y = false)} := by
    refine ⟨1, ?_⟩
    rintro p ⟨τ', _, Θa', Θb', Pm', h, rfl⟩
    refine prob_le_one _ ?_ _
    intro t i j
    unfold altParam
    split_ifs
    · exact entries_InS h.2.1 i j
    · exact entries_InS h.1 i j
  have hI : ∀ k, prob (nullParam (T := T) (Θ₀ k) (Pm₀ k)) (fun y => ψ y = true) ≤ α :=
    fun k => (le_csSup bdd0 ⟨Θ₀ k, Pm₀ k, hS k, rfl⟩).trans hψ
  have hII : ∀ k, prob (altParam τ (Θa k) (Θb k) (Pm₁ k)) (fun y => ψ y = false) ≤
      typeII {τ} ω R ψ :=
    fun k => le_csSup bdd1 ⟨τ, Finset.mem_singleton_self τ, Θa k, Θb k, Pm₁ k, hW k, rfl⟩
  -- sums
  have hp₀sum : ∑ y, p₀ y = 1 := by
    simp only [p₀]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, weight_sum, mul_one, hw₀1]
  have hp₁sum : ∑ y, p₁ y = 1 := by
    simp only [p₁]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, weight_sum, mul_one, hw₁1]
  have ha : ∑ y, (if ψ y = true then p₀ y else 0) ≤ α := by
    have e : ∑ y, (if ψ y = true then p₀ y else 0) =
        ∑ k, w₀ k * prob (nullParam (T := T) (Θ₀ k) (Pm₀ k)) (fun y => ψ y = true) := by
      unfold prob
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      simp only [p₀]
      split_ifs <;> simp
    rw [e]
    calc ∑ k, w₀ k * prob (nullParam (T := T) (Θ₀ k) (Pm₀ k)) (fun y => ψ y = true)
        ≤ ∑ k, w₀ k * α := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hI k) (hw₀ k))
      _ = α := by rw [← Finset.sum_mul, hw₀1, one_mul]
  have hb : ∑ y, (if ψ y = false then p₁ y else 0) ≤ typeII {τ} ω R ψ := by
    have e : ∑ y, (if ψ y = false then p₁ y else 0) =
        ∑ k, w₁ k * prob (altParam τ (Θa k) (Θb k) (Pm₁ k)) (fun y => ψ y = false) := by
      unfold prob
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      simp only [p₁]
      split_ifs <;> simp
    rw [e]
    calc ∑ k, w₁ k * prob (altParam τ (Θa k) (Θb k) (Pm₁ k)) (fun y => ψ y = false)
        ≤ ∑ k, w₁ k * typeII {τ} ω R ψ :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hII k) (hw₁ k))
      _ = typeII {τ} ω R ψ := by rw [← Finset.sum_mul, hw₁1, one_mul]
  have hy : ∀ y, (p₀ y + p₁ y) / 2 - |p₁ y - p₀ y| / 2 ≤
      (if ψ y = false then p₁ y else 0) + (if ψ y = true then p₀ y else 0) := by
    intro y
    have h1 := le_abs_self (p₁ y - p₀ y)
    have h2 := neg_abs_le (p₁ y - p₀ y)
    cases ψ y <;> simp <;> linarith
  have hsumy := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hy y)
  have e1 : ∑ y, ((p₀ y + p₁ y) / 2 - |p₁ y - p₀ y| / 2) =
      (∑ y, p₀ y + ∑ y, p₁ y) / 2 - (∑ y, |p₁ y - p₀ y|) / 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [e1, Finset.sum_add_distrib, hp₀sum, hp₁sum] at hsumy
  have part1 : 1 - 1 / 2 * ∑ y, |p₁ y - p₀ y| - α ≤ typeII {τ} ω R ψ := by linarith
  refine ⟨part1, ?_⟩
  intro hpos
  have hD : ∑ y, |p₁ y - p₀ y| ≤ Real.sqrt (∑ y, p₁ y ^ 2 / p₀ y - 1) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun y => |p₁ y - p₀ y| / Real.sqrt (p₀ y)) (fun y => Real.sqrt (p₀ y))
    have ef : ∀ y, |p₁ y - p₀ y| / Real.sqrt (p₀ y) * Real.sqrt (p₀ y) = |p₁ y - p₀ y| :=
      fun y => div_mul_cancel₀ _ (Real.sqrt_pos.2 (hpos y)).ne'
    have ef2 : ∀ y, (|p₁ y - p₀ y| / Real.sqrt (p₀ y)) ^ 2 = p₁ y ^ 2 / p₀ y - 2 * p₁ y + p₀ y := by
      intro y
      rw [div_pow, sq_abs, Real.sq_sqrt (hpos y).le]
      have := (hpos y).ne'
      field_simp
      ring
    have eg : ∀ y, Real.sqrt (p₀ y) ^ 2 = p₀ y := fun y => Real.sq_sqrt (hpos y).le
    simp only [ef, ef2, eg] at hcs
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp₀sum, hp₁sum] at hcs
    have hnn : 0 ≤ ∑ y, |p₁ y - p₀ y| := Finset.sum_nonneg (fun y _ => abs_nonneg _)
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    linarith
  linarith
