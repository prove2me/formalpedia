-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GluingBases.glueLocal_of_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:12:56.879926+00:00
-- url     : https://prove2.me/submissions/56da4dc8-5321-49ba-ba4e-225ead2c0a47

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsLatticeSpanO
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegOnOfCompl
import Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_nondegOn_of_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.GluingBases
theorem _root_.solution (hJ : JordanExists) (hV : GlueVecs) (hA : GlueAssemble) :
    Formalism.L2.SG.Pf.G7.GlueLocal := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 hc
  have hne : {c | ∃ b a, IsJordanIn h U M 𝔭 b a ∧ c = cJof 𝔭 a}.Nonempty := by
    obtain ⟨b, a, hba⟩ := (hJ K F V hK hF h hs).1 U M (nondegOn_of_compl hnd hUc) hM hMi 𝔭 h𝔭
    exact ⟨_, b, a, hba, rfl⟩
  obtain ⟨b, a, hba, hca⟩ := Nat.sInf_mem hne
  have hc' : cJof 𝔭 a < finrank K (orthK h U) := by
    rw [← hca]; exact hc
  obtain ⟨π, w, c, τ, hg⟩ := hV K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc'
  exact hA K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
end Formalism.L2.SG.Pf.GluingBases
