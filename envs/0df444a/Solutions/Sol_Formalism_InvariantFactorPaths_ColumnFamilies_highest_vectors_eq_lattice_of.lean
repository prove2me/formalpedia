-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.highest_vectors_eq_lattice_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:50:25.05954+00:00
-- url     : https://prove2.me/submissions/44ed3be4-9627-44d3-9395-71f0235411cb

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_high_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_high_add
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_high_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_vec_can_high
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_high_cast
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_highest_vectors_rational_span_of
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_basis_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_canT_std
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LemmaA → HighestVectorsEqLattice := by
  intro hA n _ M CF mu hmu
  classical
  ext x
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => IsHighest M ℤ mu x) ?_ (qd_high_zero M ℤ mu)
      (fun x y _ _ hx hy => qd_high_add M ℤ mu hx hy) (fun c x _ hx => qd_high_smul M ℤ mu c hx) hx
    rintro _ ⟨j, rfl, rfl⟩
    have := qd_vec_can_high CF ℤ j
    simpa using this
  · intro hx
    have hQ := highest_vectors_rational_span_of hA n M CF mu hmu _ (qd_high_cast M mu x hx)
    obtain ⟨b, hb⟩ : ∃ b : qb_Idx CF → ℤ, ∑ y, b y • qb_vecF CF ℤ y = x := by
      have : x ∈ Submodule.span ℤ (Set.range (qb_vecF CF ℤ)) := by rw [(qb_basisR hA CF ℤ).2]; trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
    let S : Set (qb_Idx CF) := {y | CF.mu y.1 = mu ∧ y.2.1 = canT (CF.mu y.1)}
    have hcast : (fun i => (x i : ℚ)) = ∑ y, (b y : ℚ) • qb_basis hA CF ℚ y := by
      funext i
      rw [← hb]
      simp [qb_basis_apply, qb_vecF, Finset.sum_apply]
    have hS : (fun i => (x i : ℚ)) ∈ Submodule.span ℚ (qb_basis hA CF ℚ '' S) := by
      refine Submodule.span_mono ?_ hQ
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨⟨j, ⟨canT (CF.mu j), qd_canT_std _⟩⟩, ⟨hj, rfl⟩, by rw [qb_basis_apply]; rfl⟩
    rw [Module.Basis.mem_span_image, hcast] at hS
    have hsupp : ∀ y, b y ≠ 0 → y ∈ S := by
      intro y hy
      apply hS
      rw [Finset.mem_coe, Finsupp.mem_support_iff, Module.Basis.repr_sum_self]
      exact_mod_cast hy
    rw [← hb]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : b y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      obtain ⟨e1, e2⟩ := hsupp y hy
      refine ⟨y.1, e1, ?_⟩
      funext i
      simp only [qb_vecF, Int.cast_id]
      rw [e2]
end Formalism.InvariantFactorPaths.ColumnFamilies
