-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LatticeIndexBis.addVal_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:26.0828+00:00
-- url     : https://prove2.me/submissions/f7a7b593-0c3c-42a4-b15c-64373ea794ff

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis
namespace Formalism.LatticeBaseChangeAlt.LatticeIndexBis
theorem _root_.solution {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O)
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ)) (x : O) (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal O' (algebraMap O O' x) = IsDiscreteValuationRing.addVal O x := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def x u hϖ n hu,
    IsDiscreteValuationRing.addVal_def (algebraMap O O' x) (Units.map (algebraMap O O' : O →* O') u) hϖ' n
      (by rw [hu]; simp)]
end Formalism.LatticeBaseChangeAlt.LatticeIndexBis
