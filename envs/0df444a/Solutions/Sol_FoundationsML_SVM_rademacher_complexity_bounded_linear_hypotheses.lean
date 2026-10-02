-- Prove2me | solution 1 for FoundationsML.SVM.rademacher_complexity_bounded_linear_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:35:32.317984+00:00
-- url     : https://prove2.me/submissions/581caa9e-334c-4ee5-8cd8-9e28dfaf3009

import Mathlib
import Definitions.Def_FoundationsML_SVM_EmpiricalRademacherComplexity

set_option autoImplicit false

theorem svm_eps_flip (b : Bool) :
    (if (!b) then (1 : ℝ) else -1) = -(if b then (1 : ℝ) else -1) := by
  cases b <;> norm_num

theorem svm_eps_sum {m : ℕ} (i j : Fin m) :
    ∑ σ : Fin m → Bool, (if σ i then (1 : ℝ) else -1) * (if σ j then (1 : ℝ) else -1) =
      if i = j then (2 : ℝ) ^ m else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have h1 : ∀ σ : Fin m → Bool,
        (if σ i then (1 : ℝ) else -1) * (if σ i then (1 : ℝ) else -1) = 1 := by
      intro σ
      cases σ i <;> norm_num
    simp_rw [h1]
    simp [Finset.card_univ]
  · rw [if_neg hij]
    let f : (Fin m → Bool) → (Fin m → Bool) := fun σ => Function.update σ i (!(σ i))
    have hf : Function.Involutive f := by
      intro σ
      funext k
      by_cases hk : k = i
      · subst hk
        simp [f]
      · simp [f, hk]
    have hsum := Equiv.sum_comp (Function.Involutive.toPerm f hf) (fun σ : Fin m → Bool =>
      (if σ i then (1 : ℝ) else -1) * (if σ j then (1 : ℝ) else -1))
    have hneg : ∀ σ : Fin m → Bool,
        (if (Function.Involutive.toPerm f hf σ) i then (1 : ℝ) else -1) *
          (if (Function.Involutive.toPerm f hf σ) j then (1 : ℝ) else -1) =
          -((if σ i then (1 : ℝ) else -1) * (if σ j then (1 : ℝ) else -1)) := by
      intro σ
      have hei : (Function.Involutive.toPerm f hf σ) i = !(σ i) := by
        simp [f]
      have hej : (Function.Involutive.toPerm f hf σ) j = σ j := by
        simp [f, Ne.symm hij]
      rw [hei, hej, svm_eps_flip]
      ring
    simp_rw [hneg, Finset.sum_neg_distrib] at hsum
    linarith

theorem svm_norm_sq_sum {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {m : ℕ} (S : Fin m → X) :
    ∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖ ^ 2 =
      (2 : ℝ) ^ m * ∑ i, ‖S i‖ ^ 2 := by
  have hexp : ∀ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖ ^ 2 =
      ∑ i, ∑ j, ((if σ i then (1 : ℝ) else -1) * (if σ j then (1 : ℝ) else -1)) *
        inner ℝ (S i) (S j) := by
    intro σ
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, svm_eps_sum]
  simp [real_inner_self_eq_norm_sq]

open FoundationsML.SVM in
theorem solution
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {m : ℕ} (S : Fin m → X) (r Λ : ℝ) (hr : 0 ≤ r) (hΛ : 0 ≤ Λ)
    (hS : ∀ i, ‖S i‖ ≤ r) :
    EmpiricalRademacherComplexity
        {h : X → ℝ | ∃ w : X, ‖w‖ ≤ Λ ∧ h = fun x => inner ℝ w x} S
      ≤ Real.sqrt (r ^ 2 * Λ ^ 2 / m) := by
  unfold EmpiricalRademacherComplexity
  have hc0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hsup : ∀ σ : Fin m → Bool,
      (⨆ g ∈ {h : X → ℝ | ∃ w : X, ‖w‖ ≤ Λ ∧ h = fun x => inner ℝ w x},
        (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * g (S i)) ≤
      (1 / (m : ℝ)) * (Λ * ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) := by
    intro σ
    have hB : 0 ≤ (1 / (m : ℝ)) * (Λ * ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) :=
      mul_nonneg hc0 (mul_nonneg hΛ (norm_nonneg _))
    refine Real.iSup_le (fun g => Real.iSup_le (fun hg => ?_) hB) hB
    obtain ⟨w, hw, rfl⟩ := hg
    refine mul_le_mul_of_nonneg_left ?_ hc0
    have hin : ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * inner ℝ w (S i) =
        inner ℝ w (∑ i, (if σ i then (1 : ℝ) else -1) • S i) := by
      rw [inner_sum]
      exact Finset.sum_congr rfl (fun i _ => (real_inner_smul_right _ _ _).symm)
    show ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * inner ℝ w (S i) ≤ _
    rw [hin]
    calc inner ℝ w (∑ i, (if σ i then (1 : ℝ) else -1) • S i)
        ≤ ‖w‖ * ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖ := real_inner_le_norm _ _
      _ ≤ Λ * ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖ :=
          mul_le_mul_of_nonneg_right hw (norm_nonneg _)
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ _ => hsup σ))
    (by positivity)) ?_
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  have hN : (0 : ℝ) < 2 ^ m := by positivity
  have hkey := svm_norm_sq_sum S
  have hCS : (∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) ^ 2 ≤
      (2 : ℝ) ^ m * ∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m → Bool)))
      (f := fun σ : Fin m → Bool => ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖)
    simpa [Finset.card_univ] using h
  have hSsum : ∑ i, ‖S i‖ ^ 2 ≤ (m : ℝ) * r ^ 2 := by
    calc ∑ i, ‖S i‖ ^ 2 ≤ ∑ _i : Fin m, r ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hS i) 2)
      _ = (m : ℝ) * r ^ 2 := by simp
  have hA2 : (∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) ^ 2 ≤
      ((2 : ℝ) ^ m) ^ 2 * ((m : ℝ) * r ^ 2) := by
    calc (∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) ^ 2
        ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ m * ∑ i, ‖S i‖ ^ 2) := hCS.trans_eq (by rw [hkey])
      _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ m * ((m : ℝ) * r ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSsum hN.le) hN.le
      _ = ((2 : ℝ) ^ m) ^ 2 * ((m : ℝ) * r ^ 2) := by ring
  have hA : (1 / (2 : ℝ) ^ m *
      ∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) ^ 2 ≤ (m : ℝ) * r ^ 2 := by
    calc (1 / (2 : ℝ) ^ m *
          ∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) ^ 2
        = (∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) ^ 2 *
            (1 / (2 : ℝ) ^ m) ^ 2 := by ring
      _ ≤ (((2 : ℝ) ^ m) ^ 2 * ((m : ℝ) * r ^ 2)) * (1 / (2 : ℝ) ^ m) ^ 2 :=
          mul_le_mul_of_nonneg_right hA2 (sq_nonneg _)
      _ = ((m : ℝ) * r ^ 2) * ((2 : ℝ) ^ m * (1 / (2 : ℝ) ^ m)) ^ 2 := by ring
      _ = (m : ℝ) * r ^ 2 := by rw [mul_one_div_cancel hN.ne']; ring
  have hcm : (1 / (m : ℝ)) ^ 2 * (m : ℝ) = 1 / (m : ℝ) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · have hm' : (m : ℝ) ≠ 0 := by positivity
      field_simp
  have hsum_eq : ∑ σ : Fin m → Bool,
      (1 / (m : ℝ)) * (Λ * ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) =
      (1 / (m : ℝ)) * Λ * ∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hsum_eq]
  calc (1 / (2 : ℝ) ^ m * ((1 / (m : ℝ)) * Λ *
        ∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖)) ^ 2
      = ((1 / (m : ℝ)) * Λ) ^ 2 * (1 / (2 : ℝ) ^ m *
          ∑ σ : Fin m → Bool, ‖∑ i, (if σ i then (1 : ℝ) else -1) • S i‖) ^ 2 := by ring
    _ ≤ ((1 / (m : ℝ)) * Λ) ^ 2 * ((m : ℝ) * r ^ 2) :=
        mul_le_mul_of_nonneg_left hA (sq_nonneg _)
    _ = ((1 / (m : ℝ)) ^ 2 * (m : ℝ)) * Λ ^ 2 * r ^ 2 := by ring
    _ = r ^ 2 * Λ ^ 2 / m := by rw [hcm]; ring
