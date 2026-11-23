-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.CellDecomposition.aniso_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:01.750797+00:00
-- url     : https://prove2.me/submissions/9bd93889-cee2-4e31-b6fd-3993a5528e66

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_repr_aniso


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
    (hW : ∀ w ∈ W, H.B w w = 0 → w = 0) (y : V) :
    ∃! w : V, w ∈ W ∧ ∀ w' ∈ W, H.B (y - w) w' = 0 := by
  obtain ⟨v, hv, hvl⟩ := repr_aniso H W hW (H.B.flip y)
  refine ⟨v, ⟨hv, fun w' hw' => ?_⟩, ?_⟩
  · apply B_swap0
    rw [map_sub, hvl w' hw']
    simp
  · rintro v' ⟨hv', h'⟩
    have hd : v' - v ∈ W := W.sub_mem hv' hv
    apply sub_eq_zero.1
    apply hW _ hd
    have h1 : H.B (y - v) (v' - v) = 0 := by
      apply B_swap0
      rw [map_sub, hvl _ hd]
      simp
    have h2 := h' _ hd
    have e : v' - v = (y - v) - (y - v') := by abel
    calc H.B (v' - v) (v' - v) = H.B ((y - v) - (y - v')) (v' - v) := by rw [← e]
      _ = 0 := by rw [LinearMap.map_sub₂, h1, h2, sub_zero]
end Formalism.HermitianLatticeCounting.P.CellDecomposition
