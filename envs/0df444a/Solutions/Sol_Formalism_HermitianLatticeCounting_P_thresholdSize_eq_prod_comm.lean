-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.thresholdSize_eq_prod_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:39.260556+00:00
-- url     : https://prove2.me/submissions/351da110-7f62-4f31-a524-42cf2d25d19c

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι l : Type*} [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (H₂ : ℝ) :
    size E D H₂ = ∏ i ∈ E, ∏ v, max 1 (D i v / H₂) := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.size
  exact Finset.prod_comm
end Formalism.HermitianLatticeCounting.P
