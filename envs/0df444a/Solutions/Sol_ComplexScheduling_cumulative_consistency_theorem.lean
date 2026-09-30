-- Prove2me | solution 1 for ComplexScheduling.cumulative_consistency_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:32:18.562681+00:00
-- url     : https://prove2.me/submissions/5edf56a4-4532-4de6-84cf-4bf6d622b08f

import Mathlib
import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling

lemma cs_work {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S)
    (k : Fin r) (J : Finset (Fin n)) (a b : ℕ) (hab : a ≤ b)
    (hwin : ∀ j ∈ J, a ≤ S j ∧ S j + p j ≤ b) :
    totalWork p demand k J + Rcap k * a ≤ Rcap k * b := by
  classical
  have h1 : ∀ i ∈ J, demand i k * p i =
      ∑ t ∈ Finset.Ico a b, (if InProcess p S t i then demand i k else 0) := by
    intro i hi
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have : (Finset.Ico a b).filter (fun t => InProcess p S t i) = Finset.Ico (S i) (S i + p i) := by
      ext t
      rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico]
      unfold InProcess
      have := hwin i hi
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, by omega⟩, h1, h2⟩
    rw [this, Nat.card_Ico, Nat.add_sub_cancel_left, mul_comm]
  have h2 : totalWork p demand k J =
      ∑ t ∈ Finset.Ico a b, ∑ i ∈ J, (if InProcess p S t i then demand i k else 0) := by
    unfold totalWork
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h3 : ∀ t, ∑ i ∈ J, (if InProcess p S t i then demand i k else 0) ≤ Rcap k := by
    intro t
    calc ∑ i ∈ J, (if InProcess p S t i then demand i k else 0)
        = ∑ i ∈ J.filter (InProcess p S t), demand i k := (Finset.sum_filter _ _).symm
      _ ≤ ∑ i ∈ Finset.univ.filter (InProcess p S t), demand i k :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset_filter _ (Finset.subset_univ J)) (fun _ _ _ => Nat.zero_le _)
      _ = resourceUsage p demand S k t := rfl
      _ ≤ Rcap k := hS.2 k t
  have h4 : totalWork p demand k J ≤ (b - a) * Rcap k := by
    rw [h2]
    calc _ ≤ ∑ t ∈ Finset.Ico a b, Rcap k := Finset.sum_le_sum fun t _ => h3 t
      _ = (b - a) * Rcap k := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  have e : (b - a) * Rcap k + Rcap k * a = Rcap k * b := by
    rw [mul_comm, ← mul_add, Nat.sub_add_cancel hab]
  calc totalWork p demand k J + Rcap k * a ≤ (b - a) * Rcap k + Rcap k * a :=
        Nat.add_le_add_right h4 _
    _ = Rcap k * b := e

theorem cs_cumul {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (k : Fin r) (J J' J'' : Finset (Fin n))
    (hJ' : J' ⊂ J) (hJ'' : J'' ⊂ J)
    (hcond : ∀ ν ∈ J \ J', ∀ μ ∈ J \ J'',
      Rcap k * dl μ < Rcap k * rel ν + totalWork p demand k J)
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S)
    (hw : WithinWindows rel dl p S) :
    (∃ i ∈ J', StartsFirstIn S J i) ∨ ∃ i ∈ J'', EndsLastIn p S J i := by
  classical
  obtain ⟨x, hxJ, -⟩ := Finset.exists_of_ssubset hJ'
  have hJne : J.Nonempty := ⟨x, hxJ⟩
  obtain ⟨ν, hν, hνmin⟩ := J.exists_min_image S hJne
  obtain ⟨μ, hμ, hμmax⟩ := J.exists_max_image (fun i => S i + p i) hJne
  by_cases hν' : ν ∈ J'
  · exact Or.inl ⟨ν, hν', hν, hνmin⟩
  by_cases hμ' : μ ∈ J''
  · exact Or.inr ⟨μ, hμ', hμ, hμmax⟩
  exfalso
  have h1 := hcond ν (Finset.mem_sdiff.mpr ⟨hν, hν'⟩) μ (Finset.mem_sdiff.mpr ⟨hμ, hμ'⟩)
  have hab : S ν ≤ S μ + p μ := (hνmin μ hμ).trans (Nat.le_add_right _ _)
  have h2 := cs_work p Rcap demand prec S hS k J (S ν) (S μ + p μ) hab
    (fun j hj => ⟨hνmin j hj, hμmax j hj⟩)
  have m1 : Rcap k * rel ν ≤ Rcap k * S ν := Nat.mul_le_mul_left _ (hw ν).1
  have m2 : Rcap k * (S μ + p μ) ≤ Rcap k * dl μ := Nat.mul_le_mul_left _ (hw μ).2
  linarith

end ComplexScheduling

open ComplexScheduling

theorem solution {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (k : Fin r) (J J' J'' : Finset (Fin n)) (hJk : ∀ i ∈ J, 0 < demand i k)
    (hJ' : J' ⊂ J) (hJ'' : J'' ⊂ J)
    (hcond : ∀ ν ∈ J \ J', ∀ μ ∈ J \ J'',
      Rcap k * dl μ < Rcap k * rel ν + totalWork p demand k J)
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hw : WithinWindows rel dl p S) :
    (∃ i ∈ J', StartsFirstIn S J i) ∨ ∃ i ∈ J'', EndsLastIn p S J i := by
  exact cs_cumul p Rcap demand prec rel dl k J J' J'' hJ' hJ'' hcond S hS hw
