-- Prove2me | solution 1 for Formalism.HN.degSupermod_zl_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:10.011483+00:00
-- url     : https://prove2.me/submissions/9ffbfe68-ddc9-4473-9e26-e72b3f4a6c5b

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Theorems.Thm_Formalism_HN_degSupermod_mem_zl

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
theorem _root_.solution {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (degSupermod_mem_zl ρ A y).mp hy
  exact (degSupermod_mem_zl ρ B _).mpr ⟨x, h hx, rfl⟩
end Formalism.HN
