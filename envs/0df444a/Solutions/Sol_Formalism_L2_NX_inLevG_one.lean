-- Prove2me | solution 1 for Formalism.L2.NX.inLevG_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:08.471873+00:00
-- url     : https://prove2.me/submissions/752d024a-12dd-484a-8e90-a9f4959d06f9

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
import Theorems.Thm_Formalism_L2_NX_inParah_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => NumberField.maximalRealSubfield L
namespace Formalism.L2.NX
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L⁺)) (r : ℕ) :
    InLevG v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) := by
  refine ⟨inParah_one v r, fun a b _ _ => ⟨fun hba => ?_, fun hab => ?_⟩⟩
  · rw [Matrix.one_apply_ne (ne_of_gt hba), map_zero]
    exact zero_lt_one
  · rw [hab, Matrix.one_apply_eq, sub_self, map_zero]
    exact zero_lt_one
end Formalism.L2.NX
