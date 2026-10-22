-- Prove2me | solution 1 for CustAssort.Value.thm31_type_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:46:49.997418+00:00
-- url     : https://prove2.me/submissions/39be5708-3cdc-473f-8c46-a3681d21ea9d

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

set_option autoImplicit false
open CustAssort.Value

theorem solution {n m : ℕ} (K : ℕ) (r : Fin n → ℝ)
    (v : Fin n → Fin m → ℝ) (θ : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hv : ∀ i j, 0 ≤ v i j) (hθ : ∀ j, 0 ≤ θ j) :
    ∀ (q : Fin m) (S : Finset (Fin n)), S.card ≤ K →
      θ q * CustAssort.AugGreedy.fj v r q S ≤ zMMNL θ v r K := by
  intro q S hS
  have hrev : ∀ (j : Fin m) (T : Finset (Fin n)), 0 ≤ CustAssort.AugGreedy.rev v r j T := by
    intro j T
    unfold CustAssort.AugGreedy.rev ChoiceCDLP.MNL.mnlObjective
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hr i).le (hv i j))
    · have : 0 ≤ ∑ i ∈ T, v i j := Finset.sum_nonneg (fun i _ => hv i j)
      linarith
  obtain ⟨S', hS', hfj⟩ := Finset.exists_mem_eq_sup' (Finset.powerset_nonempty S)
    (CustAssort.AugGreedy.rev v r q)
  have hsub : S' ⊆ S := Finset.mem_powerset.mp hS'
  have hfeas : S' ∈ feasible n K := by
    simp only [feasible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.card_le_card hsub).trans hS
  have h1 : θ q * CustAssort.AugGreedy.fj v r q S = θ q * CustAssort.AugGreedy.rev v r q S' := by
    unfold CustAssort.AugGreedy.fj
    rw [hfj]
  have h2 : θ q * CustAssort.AugGreedy.rev v r q S' ≤
      ∑ j : Fin m, θ j * CustAssort.AugGreedy.rev v r j S' :=
    Finset.single_le_sum (f := fun j => θ j * CustAssort.AugGreedy.rev v r j S')
      (fun j _ => mul_nonneg (hθ j) (hrev j S')) (Finset.mem_univ q)
  have h3 : ∑ j : Fin m, θ j * CustAssort.AugGreedy.rev v r j S' ≤ zMMNL θ v r K := by
    unfold zMMNL
    exact Finset.le_sup' (fun S => ∑ j : Fin m, θ j * CustAssort.AugGreedy.rev v r j S) hfeas
  linarith

