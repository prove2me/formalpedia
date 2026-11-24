-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.hull_bound_signed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:47.214142+00:00
-- url     : https://prove2.me/submissions/00ac1ea4-789c-4dfe-902f-a3bbada0def0

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : HullBoundSigned := by
  intro r m x hr hx i
  have hrm : ((r : ℝ) - 1) / 2 = m := by rw [hr]; push_cast; ring
  rw [hrm]
  have hconv : Convex ℝ {y : Fin m → ℝ | |y i| ≤ (m : ℝ)} := by
    have h := (convex_Icc (-(m : ℝ)) (m : ℝ)).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)
    have hset : {y : Fin m → ℝ | |y i| ≤ (m : ℝ)} =
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) ⁻¹' Set.Icc (-(m : ℝ)) (m : ℝ) := by
      ext y
      constructor
      · intro hy; exact abs_le.1 hy
      · intro hy; exact abs_le.2 hy
    rw [hset]; exact h
  refine convexHull_min ?_ hconv hx
  rintro _ ⟨⟨σ, ε⟩, rfl⟩
  have h1 : ((σ i : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (σ i).2.le
  have h0 : (0 : ℝ) ≤ ((σ i : ℕ) : ℝ) := Nat.cast_nonneg _
  show |(((ε i : ℤˣ) : ℤ) : ℝ) * ((m : ℝ) - ((σ i : ℕ) : ℝ))| ≤ (m : ℝ)
  rw [abs_mul]
  have he : |(((ε i : ℤˣ) : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]
  rw [he, one_mul, abs_le]
  constructor <;> linarith
end Formalism.IrreducibleCountingLemmas.Z
