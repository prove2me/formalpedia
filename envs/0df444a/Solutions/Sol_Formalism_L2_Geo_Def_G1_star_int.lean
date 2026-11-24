-- Prove2me | solution 1 for Formalism.L2.Geo.Def.G1.star_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:37.826869+00:00
-- url     : https://prove2.me/submissions/0f4f7576-a11a-46c7-a2ac-7c97bcb50f1f

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_GlobLatUnimod
import Theorems.Thm_Formalism_L2_Geo_Def_G1_IsFrame_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.Geo.Def.G1
theorem _root_.solution (r : 𝓞 E) :
    star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (star (algebraMap (𝓞 E) E r)) :=
    (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩
end Formalism.L2.Geo.Def.G1
