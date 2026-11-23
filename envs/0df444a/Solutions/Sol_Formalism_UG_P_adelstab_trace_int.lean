-- Prove2me | solution 1 for Formalism.UG.P.adelstab_trace_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:46.045396+00:00
-- url     : https://prove2.me/submissions/0ce9c2fb-32d9-4179-b575-3333e615efb6

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.UG.P
theorem _root_.solution (b : 𝓞 E) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = Algebra.trace F E (algebraMap (𝓞 E) E b) :=
  ⟨⟨_, Algebra.isIntegral_trace (R := ℤ) (RingOfIntegers.isIntegral_coe b)⟩, rfl⟩
end Formalism.UG.P
