-- Prove2me | solution 1 for CompOT.Metric.prop_2_2_diag
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:23:39.646751+00:00
-- url     : https://prove2.me/submissions/4c4001bd-c8ba-4cb9-a9aa-10e134e82d61

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

set_option autoImplicit false
open Matrix CompOT.Metric

theorem solution {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k)
    (a : Fin n → ℝ) (ha : a ∈ stdSimplex ℝ (Fin n)) :
    CompOT.Assignment.IsOptimalCoupling (powCost D p) a a (Matrix.diagonal a) ∧
      CompOT.Assignment.frob (powCost D p) (Matrix.diagonal a) = 0 ∧
      W D p a a = 0 := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; norm_num at hp
  have hmem : Matrix.diagonal a ∈ CompOT.Assignment.couplings a a := by
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · by_cases h : i = j
      · subst h; simpa using ha.1 i
      · simp [Matrix.diagonal_apply_ne _ h]
    · simp [Matrix.diagonal_apply]
    · simp [Matrix.diagonal_apply]
  have hD0 : ∀ i, D i i = 0 := fun i => (hD_zero i i).2 rfl
  have hfrob : CompOT.Assignment.frob (powCost D p) (Matrix.diagonal a) = 0 := by
    unfold CompOT.Assignment.frob
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : i = j
    · subst h; simp [powCost, hD0, Real.zero_rpow hp0]
    · simp [Matrix.diagonal_apply_ne _ h]
  have hnn : ∀ Q : Matrix (Fin n) (Fin n) ℝ, Q ∈ CompOT.Assignment.couplings a a →
      0 ≤ CompOT.Assignment.frob (powCost D p) Q := by
    intro Q hQ
    unfold CompOT.Assignment.frob
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (Real.rpow_nonneg (hD_nonneg i j) p) (hQ.1 i j)
  refine ⟨⟨hmem, fun Q hQ => ?_⟩, hfrob, ?_⟩
  · rw [hfrob]; exact hnn Q hQ
  · have hi : (⨅ P : CompOT.Assignment.couplings a a,
        CompOT.Assignment.frob (powCost D p) (P : Matrix (Fin n) (Fin n) ℝ)) = 0 := by
      apply le_antisymm
      · have hbdd : BddBelow (Set.range fun P : CompOT.Assignment.couplings a a =>
            CompOT.Assignment.frob (powCost D p) (P : Matrix (Fin n) (Fin n) ℝ)) :=
          ⟨0, by rintro _ ⟨Q, rfl⟩; exact hnn Q.1 Q.2⟩
        calc _ ≤ CompOT.Assignment.frob (powCost D p) (Matrix.diagonal a) :=
              ciInf_le hbdd ⟨Matrix.diagonal a, hmem⟩
          _ = 0 := hfrob
      · haveI : Nonempty (CompOT.Assignment.couplings a a) := ⟨⟨Matrix.diagonal a, hmem⟩⟩
        exact le_ciInf fun Q => hnn Q.1 Q.2
    unfold W otCost
    rw [hi]
    exact Real.zero_rpow (one_div_ne_zero hp0)
