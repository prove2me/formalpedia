-- Prove2me | solution 1 for Formalism.UG.P.easyc_inclE_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:08.294366+00:00
-- url     : https://prove2.me/submissions/ea91e237-a4d4-4d51-8294-2f3d4efe15e3

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard

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
variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type} [Fintype n]
  [DecidableEq n] (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)
namespace Formalism.UG.P
theorem _root_.solution (e : E) (he : e ∈ intOE E) :
    inclE (F := F) R e ∈ tensInt (F := F) R (intOE E) S₂ := by
  apply Subring.subset_closure
  left
  exact ⟨⟨e, he⟩, rfl⟩
end Formalism.UG.P
