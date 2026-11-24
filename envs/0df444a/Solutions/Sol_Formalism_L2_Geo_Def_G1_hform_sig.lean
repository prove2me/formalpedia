-- Prove2me | solution 1 for Formalism.L2.Geo.Def.G1.hform_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:35.696617+00:00
-- url     : https://prove2.me/submissions/c6f15522-23ac-4110-83fa-1e41efb12393

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_GlobLatUnimod

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
theorem _root_.solution {n : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ x, σ x = star x) (J : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : Formalism.UG.hform (σ : E →+* E) J x y = Formalism.DivisionValues.hform J x y := by
  simp only [Formalism.UG.hform, Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, AlgHom.coe_toRingHom, hσ,
    starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
end Formalism.L2.Geo.Def.G1
