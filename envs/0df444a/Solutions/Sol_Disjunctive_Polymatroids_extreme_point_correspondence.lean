-- Prove2me | solution 1 for Disjunctive.Polymatroids.extreme_point_correspondence
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:08:35.333055+00:00
-- url     : https://prove2.me/submissions/88b4e195-fa03-40fb-bff3-c17e8c9425d7

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

open Disjunctive.Polymatroids

theorem solution : ¬ (∀ {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) (pi : Fin n → ℝ)
    (hpi : pi ∈ Set.extremePoints ℝ (PiSet r1 r2)),
    ∃ u ∈ Set.extremePoints ℝ (USet r1 r2),
      ∀ j, pi j = ∑ A ∈ Finset.univ.filter (fun A => j ∈ A), u A) := by
  classical
  intro h
  set r1 : Finset (Fin 1) → ℝ := fun A => if A = ∅ then -1 else 5 with hr1
  set r2 : Finset (Fin 1) → ℝ := fun _ => 1 with hr2
  set π : Fin 1 → ℝ := fun _ => 1 with hπ
  have hle : ∀ a ∈ PiSet r1 r2, a 0 ≤ 1 := by
    intro a ha
    have hx : (fun _ => (1 : ℝ)) ∈ PolymatroidP r2 := by
      refine ⟨fun _ => by simp, fun A => ?_⟩
      simp only [SumOver, hr2, Finset.sum_const, nsmul_eq_mul, mul_one]
      have : A.card ≤ 1 := by simpa using Finset.card_le_univ A
      exact_mod_cast this
    have := ha.2 _ (Or.inr hx)
    simpa [dotProduct] using this
  have hmem : π ∈ PiSet r1 r2 := by
    refine ⟨fun _ => by simp [hπ], ?_⟩
    rintro x (hx | hx)
    · exfalso
      have := hx.2 ∅
      simp [SumOver, hr1] at this
      linarith
    · have := hx.2 Finset.univ
      simp only [SumOver, hr2] at this
      simpa [hπ, dotProduct] using this
  have hext : π ∈ Set.extremePoints ℝ (PiSet r1 r2) := by
    refine ⟨hmem, fun a ha b hb hab => ?_⟩
    obtain ⟨s, t, hs, ht, hst, hsum⟩ := hab
    have h0 := congrFun hsum 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hπ] at h0
    have ha1 := hle a ha
    have hb1 := hle b hb
    have ea : a 0 = 1 := by nlinarith
    have eb : b 0 = 1 := by nlinarith
    funext i; fin_cases i; simpa [hπ] using ea
  obtain ⟨u, ⟨⟨hu, h1, h2⟩, _⟩, hcov⟩ := h r1 r2 π hext
  have hcov0 := hcov 0
  simp only [hπ] at hcov0
  have hsum : ∑ A, u A * r1 A + ∑ A, u A * r2 A = ∑ A, u A * (r1 A + r2 A) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    ring
  have hlow : ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 1) => (0 : Fin 1) ∈ A), u A * 6 ≤
      ∑ A, u A * (r1 A + r2 A) := by
    calc ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 1) => (0 : Fin 1) ∈ A), u A * 6
        = ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 1) => (0 : Fin 1) ∈ A),
            u A * (r1 A + r2 A) := by
          refine Finset.sum_congr rfl fun A hA => ?_
          have hne : A ≠ ∅ := by
            intro h0
            simp [h0] at hA
          simp [hr1, hr2, hne]
          norm_num
      _ ≤ ∑ A, u A * (r1 A + r2 A) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro A _ _
          apply mul_nonneg (hu A)
          by_cases hA : A = ∅ <;> simp [hr1, hr2, hA] <;> norm_num
  rw [← Finset.sum_mul] at hlow
  linarith

#print axioms solution
