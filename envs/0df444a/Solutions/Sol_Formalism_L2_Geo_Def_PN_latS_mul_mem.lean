-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PN.latS_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:52:48.31477+00:00
-- url     : https://prove2.me/submissions/23e2f435-1cce-486e-90b6-a1f8a083dfbe

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PNeatB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PN
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PN
theorem _root_.solution {R : Type} [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R))
    (Λ : Submodule (𝓞 E) (n → E)) {c : E ⊗[F] R} (hc : c ∈ S) {w : n → E ⊗[F] R}
    (hw : w ∈ latS (F := F) R S Λ) : (fun i => c * w i) ∈ latS (F := F) R S Λ :=
  Submodule.smul_mem _ (⟨c, hc⟩ : S) hw
end Formalism.L2.Geo.Def.PN
