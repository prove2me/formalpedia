-- Prove2me | solution 1 for Formalism.UG.P.csEquiv_bc_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:14.671091+00:00
-- url     : https://prove2.me/submissions/9df26e35-f67d-4679-8c9b-0b2798d0ce1a

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEquiv

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
open Formalism.UG Formalism.UG.CS
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (γ : GL n E) (x : n → E) :
    (((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i))) =
      fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((γ : Matrix n n E) *ᵥ x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl
end Formalism.UG.P
