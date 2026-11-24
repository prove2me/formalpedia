-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.one_le_finset_prod_real_of_forall_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:47.172137+00:00
-- url     : https://prove2.me/submissions/f2dd88ab-1a4f-4100-9730-9035864aa288

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem one_le_finset_prod_of_forall_one_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) (h : ∀ v ∈ s, 1 ≤ y v) :
    1 ≤ ∏ v ∈ s, y v := by
  calc (1:ℝ) = ∏ v ∈ s, (1:ℝ) := by simp
    _ ≤ ∏ v ∈ s, y v := Finset.prod_le_prod (fun _ _ => zero_le_one) h
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type*} (s : Finset ι) (y : ι → ℝ) (h : ∀ v ∈ s, 1 ≤ y v) :
    1 ≤ ∏ v ∈ s, y v := one_le_finset_prod_of_forall_one_le s y h
end Formalism.HermitianLatticeCounting.P
