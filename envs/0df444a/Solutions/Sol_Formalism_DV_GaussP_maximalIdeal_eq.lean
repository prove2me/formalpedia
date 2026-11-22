-- Prove2me | solution 1 for Formalism.DV.GaussP.maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:25:11.445879+00:00
-- url     : https://prove2.me/submissions/8a73026c-c676-4204-9578-26251a411543

import Definitions.Def_Formalism_GaussIdealIdentity_StatementLA
import Definitions.Def_Formalism_GaussIdealIdentity_GaussIdealPrimality_GaussLocalizationLengthHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial IsLocalRing
noncomputable section
open Formalism Formalism.DV Formalism.DV.GaussP
variable (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [(gaussIdeal σ O).IsPrime]
local notation "A" => Localization.AtPrime (gaussIdeal σ O)
namespace Formalism.DV.GaussP
theorem _root_.solution :
    IsLocalRing.maximalIdeal A = Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A,
    ← Ideal.map_map, MvPolynomial.algebraMap_eq]
  try rfl
end Formalism.DV.GaussP
