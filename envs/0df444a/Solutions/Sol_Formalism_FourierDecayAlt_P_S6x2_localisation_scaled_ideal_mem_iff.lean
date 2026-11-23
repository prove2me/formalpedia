-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.localisation_scaled_ideal_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:45.111232+00:00
-- url     : https://prove2.me/submissions/ee080004-f0b3-49d9-8491-b1a551b28221

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_mem_idl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (g : ℕ) (k : ℤ) (hg : 0 < g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (t : E) :
    t ∈ locAt E P (zsub E (idl E g k 0)) ↔ t / (g : E) ^ k ∈ locAt E P (zsub E 1) := by
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    have := (mem_idl E g k 0 _ hg).1 h
    rw [zpow_zero] at this
    show _ ∈ (1 : FI E)
    rwa [mul_div_assoc] at this
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    show _ ∈ idl E g k 0
    rw [mem_idl E g k 0 _ hg, zpow_zero, mul_div_assoc]
    exact h
end Formalism.FourierDecayAlt.P.S6x2
