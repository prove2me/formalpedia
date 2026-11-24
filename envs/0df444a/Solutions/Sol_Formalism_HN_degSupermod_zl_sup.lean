-- Prove2me | solution 1 for Formalism.HN.degSupermod_zl_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:24.718855+00:00
-- url     : https://prove2.me/submissions/4cdf86a9-7aa7-44dd-a6f9-9b43b726fe0b

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod

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
variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)
namespace Formalism.HN
theorem _root_.solution (A B : Submodule R V) : zl ρ (A ⊔ B) = zl ρ A ⊔ zl ρ B := by
  simp only [zl, Submodule.sup_toAddSubgroup, AddSubgroup.map_sup]
  first
    | exact SupHomClass.map_sup AddSubgroup.toIntSubmodule _ _
    | (ext y; simp [Submodule.mem_sup, AddSubgroup.mem_sup])
end Formalism.HN
