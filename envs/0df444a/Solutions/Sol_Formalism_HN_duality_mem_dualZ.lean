-- Prove2me | solution 1 for Formalism.HN.duality_mem_dualZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:01.278849+00:00
-- url     : https://prove2.me/submissions/dc0beab4-34a3-41a1-9b49-08f4f151aadc

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace Formalism.HN
theorem _root_.solution (L : Submodule ℤ E) (y : E) :
    y ∈ dualZ L ↔ y ∈ span ℝ (L : Set E) ∧ ∀ x ∈ L, ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by
  have key : ∀ x : E, y ∈ ((Int.castAddHom ℝ).range.toIntSubmodule).comap
      ((innerSL ℝ x : E →L[ℝ] ℝ).toLinearMap.restrictScalars ℤ) ↔
        ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by
    intro x
    rw [Submodule.mem_comap]
    change (innerSL ℝ x) y ∈ (Int.castAddHom ℝ).range ↔ _
    rw [AddMonoidHom.mem_range]
    simp
  simp only [dualZ, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_iInf, key]
end Formalism.HN
