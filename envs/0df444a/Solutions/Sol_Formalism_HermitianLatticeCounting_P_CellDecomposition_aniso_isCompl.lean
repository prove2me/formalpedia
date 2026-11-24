-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.CellDecomposition.aniso_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:10.604567+00:00
-- url     : https://prove2.me/submissions/c1a60d06-ea30-4051-bc5c-a51949dccb73

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_CellDecomposition_aniso_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open CellDecomposition
open Formalism.HermitianLatticeCounting.P.CellDecomposition
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P.CellDecomposition
theorem _root_.solution [FiniteDimensional K V] (H : HermSpace K V) (W : Submodule K V)
    (hW : ∀ w ∈ W, H.B w w = 0 → w = 0) : IsCompl W (perpL H W) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact hW x hx (hx' x hx)
  · rw [codisjoint_iff, eq_top_iff]
    intro y _
    obtain ⟨w, ⟨hw, hw'⟩, -⟩ := aniso_decomp H W hW y
    have : y = w + (y - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hw hw'
end Formalism.HermitianLatticeCounting.P.CellDecomposition
