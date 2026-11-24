-- Prove2me | solution 1 for Formalism.HN.imageLattice_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:28.613813+00:00
-- url     : https://prove2.me/submissions/cf1c362f-6f02-44ea-a38e-5b589766154a

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep

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
namespace Formalism.HN
theorem _root_.solution {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) {A B : Submodule R V}
    (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hx
  exact AddSubgroup.mem_map.mpr ⟨y, h hy, rfl⟩
end Formalism.HN
