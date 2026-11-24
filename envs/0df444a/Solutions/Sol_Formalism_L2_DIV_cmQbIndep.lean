-- Prove2me | solution 1 for Formalism.L2.DIV.cmQbIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:46.708505+00:00
-- url     : https://prove2.me/submissions/794336ed-3002-4d72-a59d-79bbfbdfc526

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : CmQbIndep := by
  have key : ∀ ι ι' : Qb →+* ℂ, ∀ x ∈ cmQb ι, conjQb ι x = conjQb ι' x := by
    intro ι ι' x hx
    apply ι'.injective
    rw [conjQb_spec]
    exact hx ι'
  have le : ∀ ι ι' : Qb →+* ℂ, cmQb ι ≤ cmQb ι' := by
    intro ι ι' x hx τ
    rw [← key ι ι' x hx]
    exact hx τ
  exact fun ι ι' => ⟨le_antisymm (le ι ι') (le ι' ι), key ι ι'⟩
end Formalism.L2.DIV
