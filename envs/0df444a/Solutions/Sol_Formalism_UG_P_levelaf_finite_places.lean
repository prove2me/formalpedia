-- Prove2me | solution 1 for Formalism.UG.P.levelaf_finite_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:03.730567+00:00
-- url     : https://prove2.me/submissions/6778aa6f-5a8c-4eb1-b2c9-500562ac98d2

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelaf_valued_algebraMap

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
theorem _root_.solution (D : 𝓞 F) (hD : D ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1}.Finite := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) =
      v.valuation F (algebraMap (𝓞 F) F D) := fun v => by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), levelaf_valued_algebraMap]
  simp_rw [this, valuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
end Formalism.UG.P
