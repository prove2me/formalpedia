-- Prove2me | solution 1 for Formalism.L2.G.Triv.incl_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:12.04152+00:00
-- url     : https://prove2.me/submissions/555f87a5-f927-4a61-9720-d53d66e51b44

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal

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
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.G.Triv
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (e : E) (he : IsIntegral ℤ e) :
    inclE (F := F) (v.adicCompletion F) e ∈ SV E v := by
  apply Subring.subset_closure
  left
  exact ⟨⟨e, ⟨⟨e, he⟩, rfl⟩⟩, rfl⟩
end Formalism.L2.G.Triv
