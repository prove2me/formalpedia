-- Prove2me | solution 1 for DIGing.Undir.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:48:21.735602+00:00
-- url     : https://prove2.me/submissions/2777781c-6eaa-43ee-a375-8ee46a0b09d6

import Mathlib
import Definitions.Def_DIGing_Undir_Common

set_option autoImplicit false

open DIGing.Undir

theorem solution {n p m : ℕ} (hm : 0 < m) (s : Fin m → ℕ → Stack n p) (lam : ℝ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (γ ω : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hprod : ∏ i, γ i < 1)
    (harrow : ∀ K : ℕ, 0 < K → ∀ i : Fin m,
      ergK lam K (fun k => frob (s (finRotate m i) k)) ≤ γ i * ergK lam K (fun k => frob (s i k)) + ω i) :
    ∀ k : ℕ, frob (s ⟨0, hm⟩ k) / lam ^ k ≤
      (1 - ∏ i, γ i)⁻¹ * ∑ j, ω j * ∏ l ∈ Finset.univ.filter (fun l => j < l), γ l := by
  intro k
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  set K := k + 1 with hK
  have hKpos : 0 < K := Nat.succ_pos k
  set e : Fin (m' + 1) → ℝ := fun i => ergK lam K (fun k => frob (s i k)) with he
  have harr : ∀ i : Fin (m' + 1), e (finRotate (m' + 1) i) ≤ γ i * e i + ω i :=
    fun i => harrow K hKpos i
  set e' : ℕ → ℝ := fun j => e ⟨j % (m' + 1), Nat.mod_lt _ hm⟩ with he'
  set γ' : ℕ → ℝ := fun j => γ ⟨j % (m' + 1), Nat.mod_lt _ hm⟩ with hγ'def
  set ω' : ℕ → ℝ := fun j => ω ⟨j % (m' + 1), Nat.mod_lt _ hm⟩ with hω'def
  have hγ' : ∀ j, 0 ≤ γ' j := fun j => hγ _
  have harr' : ∀ j, j < m' + 1 → e' (j + 1) ≤ γ' j * e' j + ω' j := by
    intro j hj
    have h := harr ⟨j, hj⟩
    have hrot : finRotate (m' + 1) ⟨j, hj⟩ = ⟨(j + 1) % (m' + 1), Nat.mod_lt _ hm⟩ := by
      rw [finRotate_succ_apply]
      apply Fin.ext
      simp [Fin.val_add, Fin.val_one', Nat.add_mod]
    rw [hrot] at h
    have hj' : j % (m' + 1) = j := Nat.mod_eq_of_lt hj
    simp only [he', hγ'def, hω'def, hj']
    exact h
  have chain : ∀ j, j ≤ m' + 1 → e' j ≤ (∏ l ∈ Finset.range j, γ' l) * e' 0
      + ∑ i ∈ Finset.range j, ω' i * ∏ l ∈ Finset.Ico (i + 1) j, γ' l := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := harr' j (by omega)
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      have hsum : ∑ i ∈ Finset.range j, ω' i * ∏ l ∈ Finset.Ico (i + 1) (j + 1), γ' l
          = (∑ i ∈ Finset.range j, ω' i * ∏ l ∈ Finset.Ico (i + 1) j, γ' l) * γ' j := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have : i + 1 ≤ j := by have := Finset.mem_range.1 hi; omega
        rw [Finset.prod_Ico_succ_top this]; ring
      rw [hsum]
      simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
      nlinarith [mul_le_mul_of_nonneg_left h1 (hγ' j)]
  have he'm : e' (m' + 1) = e' 0 := by simp [he', Nat.mod_self, Nat.zero_mod]
  have hfin := chain (m' + 1) le_rfl
  rw [he'm] at hfin
  -- conversions
  have hP : ∏ l ∈ Finset.range (m' + 1), γ' l = ∏ i, γ i := by
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [hγ'def, Nat.mod_eq_of_lt i.2]
  have hS : ∑ i ∈ Finset.range (m' + 1), ω' i * ∏ l ∈ Finset.Ico (i + 1) (m' + 1), γ' l
      = ∑ j, ω j * ∏ l ∈ Finset.univ.filter (fun l => j < l), γ l := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ω' i * ∏ l ∈ Finset.Ico (i + 1) (m' + 1), γ' l)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hω'def, Nat.mod_eq_of_lt j.2]
    congr 1
    rw [Finset.prod_filter]
    have : ∏ l ∈ Finset.Ico ((j : ℕ) + 1) (m' + 1), γ' l
        = ∏ l ∈ Finset.range (m' + 1), (if (j : ℕ) < l then γ' l else 1) := by
      rw [← Finset.prod_filter]
      congr 1
      ext l
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
      omega
    rw [this, ← Fin.prod_univ_eq_prod_range (fun l => if (j : ℕ) < l then γ' l else 1)]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    simp only [hγ'def, Nat.mod_eq_of_lt l.2, Fin.lt_def]
  rw [hP, hS] at hfin
  have hE0 : e' 0 = e ⟨0, hm⟩ := by simp [he']
  have h1P : 0 < 1 - ∏ i, γ i := by linarith
  have hfin2 : e ⟨0, hm⟩ ≤ (1 - ∏ i, γ i)⁻¹ * ∑ j, ω j * ∏ l ∈ Finset.univ.filter (fun l => j < l), γ l := by
    rw [hE0] at hfin
    rw [inv_mul_eq_div, le_div_iff₀ h1P]
    nlinarith [hfin]
  refine le_trans ?_ hfin2
  exact Finset.le_sup' (fun k => frob (s ⟨0, hm⟩ k) / lam ^ k) (Finset.mem_range.2 (by omega))
