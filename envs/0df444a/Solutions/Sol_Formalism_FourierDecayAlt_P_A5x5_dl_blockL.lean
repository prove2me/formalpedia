-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.dl_blockL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:55.157664+00:00
-- url     : https://prove2.me/submissions/ae6add39-5f4b-4ab4-9cb4-2620e0bf9344

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_comap
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mem_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_blockL_mulVec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (S : Matrix ι ι K) :
    dl R (fromBlocks S 0 0 (1 : Matrix Unit Unit K)) = dl R S := by
  unfold dl
  have hB : ∀ w : ι ⊕ Unit → K, mv (fromBlocks S 0 0 (1 : Matrix Unit Unit K)) w =
      Sum.elim (S *ᵥ (w ∘ Sum.inl)) (w ∘ Sum.inr) := fun w => by
    rw [mv_apply, blockL_mulVec]
  have hres : ∀ w : ι ⊕ Unit → K, resL w = w ∘ Sum.inl := fun w => rfl
  refine gi_comap resL _ _ _ _ ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_LL] at hv
    constructor
    · intro hA
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hA
      refine AddSubgroup.mem_map.mpr ⟨x ∘ Sum.inl, ?_, ?_⟩
      · rw [mem_LL] at hx ⊢
        intro i
        exact hx (Sum.inl i)
      · rw [hres, hB, Sum.elim_comp_inl, mv_apply]
    · intro hA
      obtain ⟨y, hy, hyv⟩ := AddSubgroup.mem_map.mp hA
      refine AddSubgroup.mem_map.mpr ⟨Sum.elim y (v ∘ Sum.inr), ?_, ?_⟩
      · rw [mem_LL] at hy ⊢
        rintro (i | u)
        · exact hy i
        · exact hv (Sum.inr u)
      · rw [hB]
        funext j
        rcases j with i | u
        · have h := congrFun hyv i
          rw [mv_apply, hres] at h
          simpa using h
        · rfl
  · intro v hA
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hA
    constructor
    · intro h
      rw [mem_LL] at h ⊢
      intro i
      exact h (Sum.inl i)
    · intro h
      rw [mem_LL] at h hx ⊢
      rintro (i | u)
      · exact h i
      · rw [hB]
        exact hx (Sum.inr u)
  · ext u
    constructor
    · intro hu
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hu
      rw [mem_LL] at hw ⊢
      intro i
      exact hw (Sum.inl i)
    · intro hu
      refine AddSubgroup.mem_map.mpr ⟨Sum.elim u 0, ?_, rfl⟩
      rw [mem_LL] at hu ⊢
      rintro (i | j)
      · exact hu i
      · exact R.zero_mem
  · ext u
    constructor
    · intro hu
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hu
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hw
      refine AddSubgroup.mem_map.mpr ⟨x ∘ Sum.inl, ?_, ?_⟩
      · rw [mem_LL] at hx ⊢
        intro i
        exact hx (Sum.inl i)
      · rw [hres, hB, Sum.elim_comp_inl, mv_apply]
    · intro hu
      obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hu
      refine AddSubgroup.mem_map.mpr
        ⟨mv (fromBlocks S 0 0 (1 : Matrix Unit Unit K)) (Sum.elim y 0),
          AddSubgroup.mem_map.mpr ⟨Sum.elim y 0, ?_, rfl⟩, ?_⟩
      · rw [mem_LL] at hy ⊢
        rintro (i | j)
        · exact hy i
        · exact R.zero_mem
      · rw [hres, hB, Sum.elim_comp_inl, Sum.elim_comp_inl, mv_apply]
end Formalism.FourierDecayAlt.P.A5x5
