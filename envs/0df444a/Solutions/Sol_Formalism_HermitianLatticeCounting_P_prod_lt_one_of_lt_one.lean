-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prod_lt_one_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:21.175654+00:00
-- url     : https://prove2.me/submissions/a2aece09-ff10-48a3-ac85-d1063ef1608d

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage

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
theorem _root_.solution {ι : Type*} [Fintype ι] (a : ι → ℝ) (h0 : ∀ v, 0 ≤ a v) (h1 : ∀ v, a v < 1)
    (v₀ : ι) : ∏ v, a v < 1 := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ v₀)]
  have : ∏ v ∈ Finset.univ.erase v₀, a v ≤ 1 :=
    Finset.prod_le_one (fun v _ => h0 v) (fun v _ => (h1 v).le)
  calc a v₀ * ∏ v ∈ Finset.univ.erase v₀, a v ≤ a v₀ * 1 := mul_le_mul_of_nonneg_left this (h0 v₀)
    _ < 1 := by rw [mul_one]; exact h1 v₀
end Formalism.HermitianLatticeCounting.P
