-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.dl_blockR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:05.0499+00:00
-- url     : https://prove2.me/submissions/7f5e0b83-9fae-4eac-84a0-26c5762fde40

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_comap
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mem_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_blockR_mulVec
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
theorem _root_.solution (D : Matrix Unit Unit K) :
    dl R (fromBlocks (1 : Matrix ι ι K) 0 0 D) = modK R (D () ()) := by
  unfold dl
  rw [modK_eq]
  have hB : ∀ w : ι ⊕ Unit → K, mv (fromBlocks (1 : Matrix ι ι K) 0 0 D) w =
      Sum.elim (w ∘ Sum.inl) (fun _ => D () () * w (Sum.inr ())) := fun w => by
    rw [mv_apply, blockR_mulVec]
  have hev : ∀ w : ι ⊕ Unit → K, evR w = w (Sum.inr ()) := fun w => rfl
  refine gi_comap evR _ _ _ _ ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_LL] at hv
    constructor
    · intro hA
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hA
      rw [hev, hB]
      exact AddSubgroup.mem_map.mpr ⟨x (Sum.inr ()), mem_LL.mp hx _, rfl⟩
    · intro hA
      obtain ⟨r, hr, hrv⟩ := AddSubgroup.mem_map.mp hA
      refine AddSubgroup.mem_map.mpr ⟨Sum.elim (v ∘ Sum.inl) (fun _ => r), ?_, ?_⟩
      · rw [mem_LL]
        rintro (i | u)
        · exact hv _
        · exact hr
      · rw [hB]
        funext j
        rcases j with i | u
        · rfl
        · exact hrv
  · intro v hA
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hA
    constructor
    · intro h
      exact (mem_LL.mp h) (Sum.inr ())
    · intro h
      rw [mem_LL]
      rintro (i | u)
      · rw [hB]
        exact mem_LL.mp hx (Sum.inl i)
      · exact h
  · ext r
    constructor
    · intro hr
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hr
      exact mem_LL.mp hw (Sum.inr ())
    · intro hr
      exact AddSubgroup.mem_map.mpr ⟨fun _ => r, mem_LL.mpr fun _ => hr, rfl⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hw
      exact AddSubgroup.mem_map.mpr ⟨x (Sum.inr ()), mem_LL.mp hx _, by rw [hev, hB] <;> rfl⟩
    · intro hz
      obtain ⟨r, hr, rfl⟩ := AddSubgroup.mem_map.mp hz
      exact AddSubgroup.mem_map.mpr ⟨mv (fromBlocks (1 : Matrix ι ι K) 0 0 D) (fun _ => r),
        AddSubgroup.mem_map.mpr ⟨fun _ => r, mem_LL.mpr fun _ => hr, rfl⟩, by rw [hev, hB] <;> rfl⟩
end Formalism.FourierDecayAlt.P.A5x5
