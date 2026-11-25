-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Br.latS_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:23.953941+00:00
-- url     : https://prove2.me/submissions/442fb706-3ae8-443d-8d7f-fbfaec6b7526

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Br
open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct
namespace Formalism.L2.GlobalTheoryTheory.Br
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) (hx : x ∈ Λ) :
    (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩
end Formalism.L2.GlobalTheoryTheory.Br
