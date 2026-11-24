-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Br.latS_mono_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:02:21.972449+00:00
-- url     : https://prove2.me/submissions/f17011ea-3a0e-4309-8899-d8399e0e11e3

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_FiniteAdeleRingNontrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Br
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Br
theorem _root_.solution {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} (h : Λ ≤ Λ') :
    latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ ≤ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ' :=
  Submodule.span_mono (Set.image_mono h)
end Formalism.L2.GlobalTheoryTheory.Br
