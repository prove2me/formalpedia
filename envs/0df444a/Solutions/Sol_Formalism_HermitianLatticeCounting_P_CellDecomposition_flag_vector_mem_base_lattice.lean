-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.CellDecomposition.flag_vector_mem_base_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:39.262976+00:00
-- url     : https://prove2.me/submissions/e372ec56-320c-424d-89f8-14e67519af3e

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X


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
theorem _root_.solution (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  refine Fin.lastCases ?_ (fun b => ?_) a
  · exact Submodule.mem_sup_right (Submodule.subset_span (by simp [FlagD.z]))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X F b))
end Formalism.HermitianLatticeCounting.P.CellDecomposition
