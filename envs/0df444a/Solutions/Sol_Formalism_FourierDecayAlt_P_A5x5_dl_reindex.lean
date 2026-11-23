-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.dl_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:42.013659+00:00
-- url     : https://prove2.me/submissions/ce89df1b-dd56-4be5-80d2-23831b48ae9b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mem_LL
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
theorem _root_.solution (e : ι ≃ κ) (M : Matrix ι ι K) : dl R (reindex e e M) = dl R M := by
  unfold dl
  let f : (ι → K) →+ (κ → K) :=
    { toFun := fun u => u ∘ e.symm, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hf_apply : ∀ u, f u = u ∘ e.symm := fun u => rfl
  have hf : Function.Injective f := fun a b h => by
    funext i
    have := congrFun h (e i)
    simpa [hf_apply] using this
  have hL : (LL R ι).map f = LL R κ := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hv
      rw [mem_LL] at hu ⊢
      intro k
      rw [hf_apply]
      exact hu _
    · intro hv
      refine AddSubgroup.mem_map.mpr ⟨v ∘ e, ?_, ?_⟩
      · rw [mem_LL] at hv ⊢
        intro i
        exact hv _
      · rw [hf_apply]
        funext k
        simp
  have hM : ((LL R ι).map (mv M)).map f = (LL R κ).map (mv (reindex e e M)) := by
    rw [← hL, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    refine AddMonoidHom.ext fun u => ?_
    simp only [AddMonoidHom.comp_apply, mv_apply, hf_apply]
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv] <;> simp [Function.comp_assoc]
  rw [← hM, ← hL, gi_map hf]
end Formalism.FourierDecayAlt.P.A5x5
