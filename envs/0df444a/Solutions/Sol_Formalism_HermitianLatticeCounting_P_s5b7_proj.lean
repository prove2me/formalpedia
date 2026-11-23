-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:21.870522+00:00
-- url     : https://prove2.me/submissions/4084ae79-1405-47c6-b3e5-a615b91dda9e

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module
variable {O : Type} [CommRing O] [IsDedekindDomain O]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
    [Module.IsTorsionFree O Y] : Module.Projective O Y := by
  have : Module.FinitePresentation O Y := Module.finitePresentation_of_finite O Y
  exact Module.Flat.projective_of_finitePresentation
end Formalism.HermitianLatticeCounting.P
