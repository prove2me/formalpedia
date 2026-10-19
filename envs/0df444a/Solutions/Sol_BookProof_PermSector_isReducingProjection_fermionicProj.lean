-- Prove2me | solution 1 for BookProof.PermSector.isReducingProjection_fermionicProj
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:36:20.396971+00:00
-- url     : https://prove2.me/submissions/c3450052-0a2b-4821-8f55-418dc1422e72

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.isReducingProjection_fermionicProj
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)
theorem h43_avg_isRed {G F : Type*} [Group G] [Fintype G] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (rep : BookProof.GroupAverage.UnitaryRep G F) :
    BookProof.ReducedEsa.IsReducingProjection rep.avgProj := by
  have hS : ∀ (h : G) (x : F), rep.act h (∑ g : G, rep.act g x) = ∑ g : G, rep.act g x := by
    intro h x
    rw [map_sum]
    simp_rw [← rep.act_mul]
    exact Fintype.sum_bijective (fun g => h * g) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)
  have hav : ∀ x, rep.avgProj x = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, rep.act g x := by
    intro x
    simp [BookProof.GroupAverage.UnitaryRep.avgProj, LinearMap.sum_apply]
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hadj : ∀ (g : G) (x y : F), (inner ℂ (rep.act g x) y : ℂ) = inner ℂ x (rep.act g⁻¹ y) := by
    intro g x y
    have := rep.act_inner g x (rep.act g⁻¹ y)
    rw [← rep.act_mul, mul_inv_cancel, rep.act_one] at this
    exact this
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · rw [hav (rep.avgProj x), hav x]
    simp_rw [map_smul, hS]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    field_simp
  · rw [hav, hav, inner_smul_left, inner_smul_right, sum_inner, inner_sum]
    have hconj : (starRingEnd ℂ) ((Fintype.card G : ℂ))⁻¹ = ((Fintype.card G : ℂ))⁻¹ := by
      simp
    rw [hconj]
    congr 1
    simp_rw [hadj]
    exact Fintype.sum_bijective (fun g => g⁻¹) inv_involutive.bijective _ _ (fun _ => rfl)

theorem solution (n : ℕ) :
    IsReducingProjection (fermionicProj Hs n) := by
  exact h43_avg_isRed (signRep Hs n)

