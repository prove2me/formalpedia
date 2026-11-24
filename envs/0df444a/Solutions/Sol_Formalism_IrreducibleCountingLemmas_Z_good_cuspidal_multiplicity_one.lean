-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.good_cuspidal_multiplicity_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:30.693482+00:00
-- url     : https://prove2.me/submissions/9ab53b84-8a99-468b-9671-b4d9e68782db

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_goodCuspidal_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : GoodCuspidalOne := by
  intro k _ P _ r f I _ n d h hr hdeg hsq hprod hn hn1 hd1 hno
  obtain ⟨hd, hcard⟩ := goodCuspidal_holds k P r f I n d h hdeg hsq hprod hn hn1 hd1 hno
  obtain ⟨v₀⟩ := ‹Nonempty P›
  have hne : Nonempty I := by
    by_contra hemp
    have : IsEmpty I := not_nonempty_iff.1 hemp
    have := hdeg v₀
    rw [hprod v₀, Finset.univ_eq_empty, Finset.prod_empty, natDegree_one] at this
    omega
  have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.1 hcard
  refine ⟨le_antisymm hcard (Fintype.card_pos_iff.2 hne), fun i => ⟨hd i, ?_⟩⟩
  have := hdeg v₀
  rw [hprod v₀, Fintype.prod_subsingleton _ i, hd i, pow_one, hn] at this
  exact this
end Formalism.IrreducibleCountingLemmas.Z
