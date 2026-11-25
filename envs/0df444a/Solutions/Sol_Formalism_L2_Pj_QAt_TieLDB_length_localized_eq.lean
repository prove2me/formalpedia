-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDB.length_localized_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:42.196284+00:00
-- url     : https://prove2.me/submissions/58f70448-9914-48c3-a4b5-dee2c2b8522b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDB_isLocalizedModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDB
open Module
variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]
variable (H G : Submodule A V)
namespace Formalism.L2.Pj.QAt.TieLDB
theorem _root_.solution {P : Type*} [AddCommGroup P] [Module A P]
    (e : P ≃ₗ[A] H ⧸ G.comap H.subtype) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl P) =
      Module.length (Localization.AtPrime p)
        (↥(Submodule.span (Localization.AtPrime p) (H : Set V)) ⧸
          (Submodule.span (Localization.AtPrime p) (G : Set V)).comap
            (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype) := by
  have := isLocalizedModule p H G
  have : IsLocalizedModule p.primeCompl (locMap p H G ∘ₗ e.toLinearMap) := inferInstance
  exact ((IsLocalizedModule.iso p.primeCompl (locMap p H G ∘ₗ e.toLinearMap)).extendScalarsOfIsLocalization
    p.primeCompl (Localization.AtPrime p)).length_eq
end Formalism.L2.Pj.QAt.TieLDB
