-- Prove2me | solution 1 for Birge1985.Degeneracy.feasibility_cut_forces_degeneracy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:47:04.026237+00:00
-- url     : https://prove2.me/submissions/e712f28b-470d-4dee-b3d7-bd288e7f33a5

import Mathlib
import Definitions.Def_BasicSolution
import Definitions.Def_Birge1985_Degeneracy_NodeProblem

set_option autoImplicit false

namespace Birge1985.Degeneracy.P1432

open Matrix LinearOptimization Birge1985.Degeneracy

/-- A nonzero signed multiplier vector whose combinations of constraint vectors and of
right-hand sides both vanish forces every basic feasible solution to be degenerate. -/
theorem degen_of_cert {ι : Type} [Fintype ι] {N : ℕ} (C : ι → LinearConstraint N)
    (lam : ι → ℝ) (hsign : IsSignedMultiplier C lam) (ha : ∑ i, lam i • (C i).a = 0)
    (hb : ∑ i, lam i * (C i).b = 0) (hne : ∃ i, lam i ≠ 0)
    (z : Fin N → ℝ) (hz : IsBasicFeasibleSolution C z) :
    IsDegenerateBasicSolution C z := by
  classical
  obtain ⟨hbas, hfeas⟩ := hz
  refine ⟨hbas, ?_⟩
  have hterm : ∀ i, 0 ≤ lam i * ((C i).a ⬝ᵥ z - (C i).b) := by
    intro i
    have hzi := hfeas i
    obtain ⟨hge, hle⟩ := hsign i
    rcases hrel : (C i).rel with _ | _ | _ <;>
      simp only [LinearConstraint.IsSatisfiedAt, hrel] at hzi
    · exact mul_nonneg (hge hrel) (by linarith)
    · exact mul_nonneg_of_nonpos_of_nonpos (hle hrel) (by linarith)
    · rw [hzi, sub_self, mul_zero]
  have hsum : ∑ i, lam i * ((C i).a ⬝ᵥ z - (C i).b) = 0 := by
    have h1 : ∑ i, lam i * ((C i).a ⬝ᵥ z) = 0 := by
      have := congrArg (fun v => v ⬝ᵥ z) ha
      simpa [sum_dotProduct, smul_dotProduct] using this
    simp only [mul_sub, Finset.sum_sub_distrib, h1, hb, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)).1 hsum
  have hact : ∀ i, lam i ≠ 0 → (C i).IsActiveAt z := by
    intro i hi
    have := hzero i (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hi
    · unfold LinearConstraint.IsActiveAt; linarith
  obtain ⟨-, s, hs, hsact, hli⟩ := hbas
  have hout : ∃ i, lam i ≠ 0 ∧ i ∉ s := by
    by_contra hno
    push Not at hno
    have hsub : ∀ i, i ∉ s → lam i = 0 := fun i hi => by
      by_contra h; exact hi (hno i h)
    have hs0 : ∑ i : s, lam i.1 • (C i.1).a = 0 := by
      rw [Finset.sum_coe_sort s (fun i => lam i • (C i).a), ← ha]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi; simp [hsub i hi]
    have hall := (Fintype.linearIndependent_iff.1 hli) (fun i => lam i.1) hs0
    obtain ⟨j, hj⟩ := hne
    by_cases hjs : j ∈ s
    · exact hj (hall ⟨j, hjs⟩)
    · exact hj (hsub j hjs)
  obtain ⟨i, hi, his⟩ := hout
  have hsub : (↑(insert i s) : Set ι) ⊆ {j | (C j).IsActiveAt z} := by
    intro j hj
    rw [Finset.coe_insert, Set.mem_insert_iff] at hj
    rcases hj with rfl | hj
    · exact hact j hi
    · exact hsact j hj
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem his, hs] at this
  omega

theorem a_eq {nIn : ℕ} (Q : NodeProblem nIn) (x y : Fin nIn → ℝ) (i : Q.Idx) :
    (Q.constraints x i).a = (Q.constraints y i).a ∧
      (Q.constraints x i).rel = (Q.constraints y i).rel := by
  rcases i with k | l | l | i | u <;> exact ⟨rfl, rfl⟩

/-- The dual objective at `x` is the affine function `cutConst - cutSlope ⬝ᵥ x`. -/
theorem dualObj_eq {nIn : ℕ} (P : NodeProblem nIn) (lam : P.Idx → ℝ) (x : Fin nIn → ℝ) :
    ∑ i, lam i * (P.constraints x i).b = P.cutConst lam - P.cutSlope lam ⬝ᵥ x := by
  unfold NodeProblem.cutConst NodeProblem.cutSlope NodeProblem.eqPart
  rw [neg_dotProduct, sub_neg_eq_add, ← Matrix.dotProduct_mulVec]
  simp only [Fintype.sum_sum_type, NodeProblem.constraints, Matrix.mulVec_zero, Pi.zero_apply,
    add_zero, mul_add, Finset.sum_add_distrib, dotProduct]
  ring

theorem main {nIn : ℕ} (P : NodeProblem nIn)
    (Q : NodeProblem P.n) (x0 : Fin P.n → ℝ) (lam : Q.Idx → ℝ) (l' : Fin P.r)
    (hgen : IsGeneratedFeasibilityCut Q x0 lam (P.D l') (P.d l'))
    (xbar : Fin P.n → ℝ) (hbind : P.D l' ⬝ᵥ xbar = P.d l') :
    ∀ z : Fin (Q.n + 1) → ℝ, IsBasicFeasibleSolution (Q.constraints xbar) z →
      IsDegenerateBasicSolution (Q.constraints xbar) z := by
  intro z hz
  obtain ⟨⟨hsign, ha, hpos⟩, hD, hd⟩ := hgen
  apply degen_of_cert (Q.constraints xbar) lam
  · intro i
    rw [(a_eq Q xbar x0 i).2]
    exact hsign i
  · rw [← ha]
    apply Finset.sum_congr rfl
    intro i _
    rw [(a_eq Q xbar x0 i).1]
  · rw [dualObj_eq, ← hD, ← hd, hbind, sub_self]
  · by_contra hno
    push Not at hno
    simp [hno] at hpos
  · exact hz

end Birge1985.Degeneracy.P1432

open Matrix LinearOptimization Birge1985.Degeneracy in
theorem solution {nIn : ℕ} (P : NodeProblem nIn)
    (Q : NodeProblem P.n) (x0 : Fin P.n → ℝ) (lam : Q.Idx → ℝ) (l' : Fin P.r)
    (hgen : IsGeneratedFeasibilityCut Q x0 lam (P.D l') (P.d l'))
    (xbar : Fin P.n → ℝ) (hbind : P.D l' ⬝ᵥ xbar = P.d l') :
    ∀ z : Fin (Q.n + 1) → ℝ, IsBasicFeasibleSolution (Q.constraints xbar) z →
      IsDegenerateBasicSolution (Q.constraints xbar) z := by
  exact Birge1985.Degeneracy.P1432.main P Q x0 lam l' hgen xbar hbind
