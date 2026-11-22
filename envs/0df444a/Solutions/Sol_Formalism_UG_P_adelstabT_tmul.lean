-- Prove2me | solution 1 for Formalism.UG.P.adelstabT_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:09.236517+00:00
-- url     : https://prove2.me/submissions/25ffc97b-5f45-4463-9bdf-d7efc56f331d

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
theorem _root_.solution (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    adelstabT F E (e ⊗ₜ a) = algebraMap F _ (Algebra.trace F E e) * a := by
  simp only [adelstabT, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, Algebra.smul_def]
end Formalism.UG.P
