-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_w_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:50.862289+00:00
-- url     : https://prove2.me/submissions/0ebc4768-b0f5-4be2-beb8-d22142e6cc0a

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (o : Option (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K))) :
    ∃ r : NumberField.RingOfIntegers K,
      o.elim (1 : K) (NumberField.integralBasis K) = algebraMap _ K r := by
  cases o with
  | none => exact ⟨1, (map_one _).symm⟩
  | some i =>
    exact ⟨_, NumberField.integralBasis_apply K i⟩
end Formalism.HermitianLatticesTheory
