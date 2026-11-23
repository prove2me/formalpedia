-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.isOpen_isInt_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:28.186665+00:00
-- url     : https://prove2.me/submissions/0a05da06-1322-45e2-a256-3828c8e21ae1

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (R : Subring K) (hR : IsOpen (R : Set K)) (n : ℕ) :
    IsOpen {g : GL (Fin n) K | IsInt R (g : Matrix (Fin n) (Fin n) K) ∧
      IsInt R ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} := by
  have hset : {g : GL (Fin n) K | IsInt R (g : Matrix (Fin n) (Fin n) K) ∧
      IsInt R ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} =
      (⋂ a, ⋂ b, {g : GL (Fin n) K | (g : Matrix (Fin n) (Fin n) K) a b ∈ R}) ∩
      (⋂ a, ⋂ b, {g : GL (Fin n) K | ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ R}) := by
    ext g
    simp [IsInt, Set.mem_iInter]
  rw [hset]
  apply IsOpen.inter
  · refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    exact hR.preimage (Units.continuous_val.matrix_elem a b)
  · refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    exact hR.preimage (Units.continuous_coe_inv.matrix_elem a b)
end Formalism.DoubleCosetMeasures.P
