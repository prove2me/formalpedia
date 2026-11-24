-- Prove2me | solution 1 for Formalism.HN.range_comp_eq_imageLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:28.470448+00:00
-- url     : https://prove2.me/submissions/b85c1a06-67fc-4a42-bfac-e9ff6fdf74d5

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq

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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
namespace Formalism.HN
theorem _root_.solution {R V E G : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [AddCommGroup G] (ρ : V →+ E)
    (N : Submodule R V) (j : G →+ V) (hj : ∀ v, v ∈ N ↔ ∃ g, j g = v) :
    LinearMap.range (ρ.comp j).toIntLinearMap = zl ρ N := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨j g, (hj _).2 ⟨g, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨g, rfl⟩ := (hj v).1 hv
    exact ⟨g, rfl⟩
end Formalism.HN
