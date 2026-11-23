-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.char_mem_of_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:23.28073+00:00
-- url     : https://prove2.me/submissions/765eaca9-50c2-4026-be24-02f55f0185d5

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
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
theorem _root_.solution {C : Type} [AddCommGroup C] [Finite C]
    (H : AddSubgroup (AddChar C ℂ)) (χ : AddChar C ℂ)
    (h : ∀ c : C, (∀ η ∈ H, η c = 1) → χ c = 1) : χ ∈ H := by
  by_contra hχ
  have hne : (QuotientAddGroup.mk χ : AddChar C ℂ ⧸ H) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨Φ, hΦ⟩ := AddChar.exists_apply_ne_zero.2 hne
  let Ψ : AddChar (AddChar C ℂ) ℂ := Φ.compAddMonoidHom (QuotientAddGroup.mk' H)
  obtain ⟨c, hc⟩ := AddChar.doubleDualEmb_bijective.2 Ψ
  have hev : ∀ η : AddChar C ℂ, η c = Φ (QuotientAddGroup.mk η) := by
    intro η
    have := DFunLike.congr_fun hc η
    simpa [Ψ] using this
  apply hΦ
  rw [← hev]
  apply h
  intro η hη
  rw [hev, (QuotientAddGroup.eq_zero_iff η).2 hη, AddChar.map_zero_eq_one]
end Formalism.FourierDecayAlt.P.A5x2
