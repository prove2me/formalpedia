-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.residue_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:44.125923+00:00
-- url     : https://prove2.me/submissions/716bfc61-25cd-4c83-a54b-26390171db57

import Definitions.Def_Formalism_FlagUnipotentLattices_MemLpTwoOfOneTop
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 MeasureTheory Filter Topology TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Residue := by
  intro E _ _ n k lam u a K s₀ s₁ hinj hK H i
  have key : (∏ s ∈ univ.erase i, (lam i - lam s)) • a i = (∏ j, (lam i - s₀ + s₁ - u j)) • K := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    set P : Polynomial ℂ := ∑ i', Polynomial.C (φ (a i')) *
      ∏ s ∈ univ.erase i', (Polynomial.X + Polynomial.C (s₀ - lam s)) with hP
    set Q : Polynomial ℂ := Polynomial.C (φ K) * ∏ j, (Polynomial.X + Polynomial.C (s₁ - u j)) with hQ
    have evP : ∀ x, P.eval x = ∑ i', φ (a i') * ∏ s ∈ univ.erase i', (x + (s₀ - lam s)) := by
      intro x
      simp only [hP, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        Polynomial.eval_add, Polynomial.eval_X]
    have evQ : ∀ x, Q.eval x = φ K * ∏ j, (x + (s₁ - u j)) := by
      intro x
      simp only [hQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        Polynomial.eval_add, Polynomial.eval_X]
    have hPQ : P = Q := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hfin : (Set.range fun s => lam s - s₀).Finite := Set.finite_range _
      refine hfin.infinite_compl.mono ?_
      intro x hx
      have hx' : ∀ s, x + s₀ - lam s ≠ 0 := by
        intro s h0
        apply hx
        exact ⟨s, by linear_combination -h0⟩
      have h1 := congrArg φ (H x hx')
      simp only [map_sum, map_smul, smul_eq_mul] at h1
      have hD : (∏ s, (x + s₀ - lam s)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun s _ => hx' s)
      show P.eval x = Q.eval x
      rw [evP, evQ]
      have h2 : ∀ i', φ (a i') * ∏ s ∈ univ.erase i', (x + (s₀ - lam s)) =
          (∏ s, (x + s₀ - lam s)) * ((x - (lam i' - s₀))⁻¹ * φ (a i')) := by
        intro i'
        rw [← Finset.mul_prod_erase univ (fun s => x + s₀ - lam s) (Finset.mem_univ i')]
        have h3 : x - (lam i' - s₀) = x + s₀ - lam i' := by ring
        have h4 : ∀ s, x + (s₀ - lam s) = x + s₀ - lam s := fun s => by ring
        simp only [h3, h4]
        field_simp [hx' i']
      simp only [h2]
      rw [← Finset.mul_sum, h1]
      have h5 : ∀ j, x + (s₁ - u j) = x + s₁ - u j := fun j => by ring
      simp only [h5]
      field_simp
    have h6 := congrArg (Polynomial.eval (lam i - s₀)) hPQ
    rw [evP, evQ, Finset.sum_eq_single i] at h6
    · rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, sub_eq_zero]
      have h7 : ∀ s, lam i - s₀ + (s₀ - lam s) = lam i - lam s := fun s => by ring
      have h8 : ∀ j, lam i - s₀ + (s₁ - u j) = lam i - s₀ + s₁ - u j := fun j => by ring
      simp only [h7, h8] at h6
      rw [mul_comm, h6, mul_comm]
    · intro i' _ hi'
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi', Finset.mem_univ i⟩) (by ring), mul_zero]
    · simp
  have hc : (∏ s ∈ univ.erase i, (lam i - lam s)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro s hs
    rw [sub_ne_zero]
    intro h
    exact (Finset.mem_erase.mp hs).1 (hinj h).symm
  constructor
  · intro h0
    rw [h0, smul_zero] at key
    have := (smul_eq_zero.mp key.symm).resolve_right hK
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp this
    exact ⟨j, by linear_combination -hj⟩
  · rintro ⟨j, hj⟩
    have : (∏ j, (lam i - s₀ + s₁ - u j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj]; ring)
    rw [this, zero_smul] at key
    exact (smul_eq_zero.mp key).resolve_left hc
end Formalism.HermitianLatticeCounting.P
