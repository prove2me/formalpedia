-- Prove2me | solution 1 for Formalism.UG.P.inclE_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:21.506694+00:00
-- url     : https://prove2.me/submissions/4a4f3c4f-feab-40c3-97e6-af739ec7530a

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution (F E : Type) [Field F] [CommRing E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] :
    Function.Injective (inclE (F := F) (E := E) R) := by
  intro x y hxy
  exact Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F R).injective hxy
end Formalism.UG.P
