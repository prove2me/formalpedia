-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_star_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:14.830535+00:00
-- url     : https://prove2.me/submissions/f5efd3cd-2d8b-4be0-994f-607022755751

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (r : RingOfIntegers K) : IsIntegral ℤ (star (r : K)) := by
  exact (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom
end Formalism.HermitianLatticesTheory
