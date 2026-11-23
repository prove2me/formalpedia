-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.dualSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:42.157481+00:00
-- url     : https://prove2.me/submissions/652f706e-dc68-49d3-8556-8b934fbd0c26

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_char_mem_of_annihilator
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_psiB_sep
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



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution : DualSpan := by
  intro K _ R ψ hsd C _ _ _ ι _ lam μ hμ
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by simpa using (hsd 1).2 R.one_mem r hr
  let χ : (C →ₗ[R] KR R) →+ AddChar C ℂ := AddMonoidHom.mk'
    (fun α => (psiB R ψ hψ).compAddMonoidHom α.toAddMonoidHom) (by
      intro α β
      ext c
      simp [AddChar.add_apply, AddChar.map_add_eq_mul])
  have hχ : ∀ α c, χ α c = psiB R ψ hψ (α c) := fun α c => rfl
  let S := Submodule.span R (Set.range lam)
  have hmem : χ μ ∈ S.toAddSubgroup.map χ := by
    apply char_mem_of_annihilator
    intro c hc
    have hz : ∀ α ∈ S, α c = 0 := by
      intro α hα
      apply psiB_sep R ψ hsd hψ
      intro r
      have := hc (χ (r • α)) ⟨r • α, S.smul_mem r hα, rfl⟩
      rwa [hχ] at this
    rw [hχ, hμ c (fun j => hz _ (Submodule.subset_span ⟨j, rfl⟩)), AddChar.map_zero_eq_one]
  obtain ⟨α, hα, hαμ⟩ := hmem
  have : α = μ := by
    ext c
    rw [← sub_eq_zero]
    apply psiB_sep R ψ hsd hψ
    intro r
    have h1 := DFunLike.congr_fun hαμ (r • c)
    rw [hχ, hχ] at h1
    rw [smul_sub, ← map_smul, ← map_smul, AddChar.map_sub_eq_div, h1, div_self]
    exact (AddChar.val_isUnit _ _).ne_zero
  rw [← this]; exact hα
end Formalism.FourierDecayAlt.P.A5x2
