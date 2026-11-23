-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.pderiv_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:23.952794+00:00
-- url     : https://prove2.me/submissions/f08ae480-ab94-492f-99c9-584a41e15328

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupCubeJets
open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.ELL.FormalGroupCubeJets
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (i : σ)
    (g : MvPowerSeries σ R) :
    MvPowerSeries.pderiv S i (MvPowerSeries.map f g) =
      MvPowerSeries.map f (MvPowerSeries.pderiv R i g) := by
  ext d
  rw [coeff_pderiv, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, coeff_pderiv, map_mul,
    map_add, map_natCast, map_one]
end Formalism.ELL.FormalGroupCubeJets
