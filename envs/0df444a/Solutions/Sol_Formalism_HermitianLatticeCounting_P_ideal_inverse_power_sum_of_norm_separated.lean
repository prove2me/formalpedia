-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_inverse_power_sum_of_norm_separated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:14.750859+00:00
-- url     : https://prove2.me/submissions/fc55fb30-2b81-4324-aeaf-996966c93acc

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_placeEmbedding
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_placeEmbedding_injective
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_absNorm_pos_of_ne_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_idealRadius_pos
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_card_infinite_places_pos
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_radius_sq_pow_card_places
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_embedded_ideal_points_separated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
open Classical
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hn : IdealNormProductLowerBound) (hs : SeparatedSetSumBound) : Formalism.HermitianLatticeCounting.ExpansionTerms.IdealInversePowerSum := by
  intro E _ _ _ aa haa h1 S hS
  have hp := absNorm_pos_of_ne_zero E aa haa
  have hro1 : idealRadius E aa ≤ 1 := Real.rpow_le_one hp.le h1 (by have := card_infinite_places_pos E; positivity)
  have h := hs (InfinitePlace E) (idealRadius E aa) (S.image (infinitePlaceEmbedding E)) (idealRadius_pos E aa haa) hro1
    (embedded_ideal_points_separated hn E aa haa S hS)
  rw [Finset.sum_image (fun x _ y _ hxy => placeEmbedding_injective E hxy), div_pow, radius_sq_pow_card_places E aa haa] at h
  simpa only [norm_placeEmbedding] using h
end Formalism.HermitianLatticeCounting.P
