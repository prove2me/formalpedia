-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_comap_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:55.900196+00:00
-- url     : https://prove2.me/submissions/16c79686-99d0-4461-8a2f-532d5480098e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheafOpenImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
  (g : Y ⟶ X) [IsOpenImmersion g] [LocallyOfFiniteType (g ≫ p)]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    (P A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p P r A).comap g =
      logDerivIdealSheafIterate k (g ≫ p) (P.comap g) r (A.comap g) :=
  Scheme.IdealSheafData.ext
    (funext fun V => logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion k p g P A r V)
end FunctorialResolution.EmbeddedResolution
