-- Prove2me | solution 1 for Formalism.HN.HeightGram.zl_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:18.28303+00:00
-- url     : https://prove2.me/submissions/4170a7ba-460e-4356-97fc-33bf3b23f603

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HN.HeightGram
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) {N L : Submodule (𝓞 K) V} (h : N ≤ L) :
    zl ρ N ≤ zl ρ L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hx
  exact AddSubgroup.mem_map.2 ⟨y, h hy, rfl⟩
end Formalism.HN.HeightGram
