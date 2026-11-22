-- Prove2me | solution 1 for Formalism.UG.P.levelaf_algebraMap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:38:48.839616+00:00
-- url     : https://prove2.me/submissions/705ce4a3-8633-4d24-ab3e-c73e93a133e9

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.UG.P
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0) :
    algebraMap (𝓞 F) (v.adicCompletion F) D ≠ 0 := by
  intro h'
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F),
    map_eq_zero_iff _ (algebraMap F _).injective,
    map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)] at h'
  exact hD h'
end Formalism.UG.P
