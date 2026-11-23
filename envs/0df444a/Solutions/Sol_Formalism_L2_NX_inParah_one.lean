-- Prove2me | solution 1 for Formalism.L2.NX.inParah_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:58.069916+00:00
-- url     : https://prove2.me/submissions/2cae4de8-a671-4c96-8975-50f3e0542fb8

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs

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
    InParah v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) := by
  refine ⟨fun a b => ?_, fun a b ha hb => ?_⟩
  · rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Matrix.one_apply_ne (by intro h; rw [h] at ha; omega), map_zero]
    exact zero_lt_one
end Formalism.L2.NX
