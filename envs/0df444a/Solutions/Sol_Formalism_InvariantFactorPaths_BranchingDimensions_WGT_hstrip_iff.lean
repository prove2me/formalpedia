-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.WGT.hstrip_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:29.096183+00:00
-- url     : https://prove2.me/submissions/d6c0faa3-c53f-429f-914e-35f2be443c25

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_extW_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_extW_val
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_wsize_extW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Formalism.InvariantFactorPaths.BranchingDimensions.WGT
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (gtBox dGT stripsUp)
namespace Formalism.InvariantFactorPaths.BranchingDimensions.WGT
theorem _root_.solution {n : ℕ} (μ ν : Fin n → ℤ) (B : ℕ) :
    (HStrip n (extW μ) (extW ν) ∧ wsize n (extW ν) - wsize n (extW μ) = B) ↔ ν ∈ stripsUp μ B := by
  have hm : ν ∈ stripsUp μ B ↔ (∀ i, ν i ∈ Finset.Icc (μ i) (μ i + B)) ∧
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip ν μ B := by
    classical
    unfold stripsUp
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
  rw [hm]
  simp only [Finset.mem_Icc, HStrip, Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip, wsize_extW]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hle : ∀ i, μ i ≤ ν i := fun i => by
      have := h1 i.val i.isLt
      rwa [extW_val, extW_val] at this
    have hadj : ∀ m m' : Fin n, m.val + 1 = m'.val → ν m' ≤ μ m := by
      intro m m' hmm
      have := h2 m.val (by omega)
      rw [extW_lt μ (by omega), extW_lt ν (by omega)] at this
      have e : (⟨m.val + 1, by omega⟩ : Fin n) = m' := Fin.ext hmm
      rw [e] at this
      exact this
    refine ⟨fun i => ⟨hle i, ?_⟩, hle, hadj, h3⟩
    have hsum : ν i - μ i ≤ ∑ m, ν m - ∑ m, μ m := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.single_le_sum (f := fun m => ν m - μ m) (fun m _ => by linarith [hle m]) (Finset.mem_univ i)
    linarith
  · rintro ⟨_, hle, hadj, h3⟩
    refine ⟨⟨fun m hm => ?_, fun m hm => ?_⟩, h3⟩
    · rw [extW_lt μ hm, extW_lt ν hm]
      exact hle _
    · rw [extW_lt μ (by omega), extW_lt ν (by omega)]
      exact hadj ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl
end Formalism.InvariantFactorPaths.BranchingDimensions.WGT
