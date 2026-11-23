-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.mem_idl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:11.004829+00:00
-- url     : https://prove2.me/submissions/e9b7cb35-9a40-47d6-938c-d91f19fa8c10

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff

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
theorem _root_.solution (g : ℕ) (k ν : ℤ) (t : E) (hg : 0 < g) :
    t ∈ idl E g k ν ↔ t / (g : E) ^ k ∈ dd E ^ ν := by
  have hg' : ((g : E) ^ k) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hg.ne')
  unfold idl
  rw [mul_comm, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [mul_div_cancel_left₀ _ hg']
  · intro h
    exact ⟨_, h, by field_simp⟩
end Formalism.FourierDecayAlt.P.S6x2
