-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.measure_preimage_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:52.021215+00:00
-- url     : https://prove2.me/submissions/62a0ce5c-79af-4707-bbb3-babc61e8d0ed

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_cls
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cls_leftRel
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isOpen_cls_leftRel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {G : Type} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (μ : Measure G) [μ.IsMulLeftInvariant] (K₀ : Subgroup G)
    (hK : IsOpen (K₀ : Set G)) (S : Set (G ⧸ K₀)) (hS : S.Finite) :
    μ ((QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' S) = (Nat.card S : ENNReal) * μ (K₀ : Set G) := by
  classical
  have hU : (QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' S =
      ⋃ q ∈ hS.toFinset, cls (QuotientGroup.leftRel K₀) q := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.Finite.mem_toFinset, mem_cls,
      exists_prop, exists_eq_right']
  rw [hU, measure_biUnion_finset]
  · simp_rw [cls_leftRel, measure_preimage_mul]
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card S hS]
  · intro q _ q' _ hne
    exact Set.disjoint_left.2 fun x hx hx' => hne (hx.symm.trans hx')
  · exact fun q _ => (isOpen_cls_leftRel K₀ hK q).measurableSet
end Formalism.DoubleCosetMeasures.P
