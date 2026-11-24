-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrs_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:52:37.888783+00:00
-- url     : https://prove2.me/submissions/9e92f66b-acd0-42e0-9c34-b56acde9daf2

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrsSecondCountableAbs
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set Topology
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (μ : Measure G) [SigmaFinite μ] [μ.IsOpenPosMeasure] {V : Set G} (hV : IsOpen V) (h1 : (1 : G) ∈ V) :
    ∃ S : Set G, S.Countable ∧ ∀ y : G, ∃ x ∈ S, y ∈ x • (V * V⁻¹) := by
  classical
  obtain ⟨S, -, hSmax⟩ := zorn_subset_nonempty {S : Set G | S.PairwiseDisjoint (fun x => x • V)}
    (fun c hcS hc _ => ⟨⋃₀ c, (Set.pairwiseDisjoint_sUnion hc.directedOn).2 (fun s hs => hcS hs),
      fun s hs => Set.subset_sUnion_of_mem hs⟩) ∅ (Set.pairwiseDisjoint_empty)
  have hS : S.PairwiseDisjoint (fun x => x • V) := hSmax.prop
  refine ⟨S, ?_, ?_⟩
  · have hc := MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := μ)
      (As := fun x : S => (x : G) • V)
      (fun x => ((hV.smul (x : G)).measurableSet).nullMeasurableSet)
      (fun x y hxy => (hS x.2 y.2 (fun h => hxy (Subtype.ext h))).aedisjoint)
    have huniv : {x : S | 0 < μ ((x : G) • V)} = Set.univ :=
      Set.eq_univ_of_forall fun x => (hV.smul (x : G)).measure_pos μ ⟨(x : G) • 1, Set.smul_mem_smul_set h1⟩
    rw [huniv] at hc
    exact Set.countable_coe_iff.1 (Set.countable_univ_iff.1 hc)
  · intro y
    by_contra hcon
    push_neg at hcon
    have hyS : y ∉ S := fun hy => hcon y hy ⟨1 * 1⁻¹, Set.mul_mem_mul h1 (Set.inv_mem_inv.2 (by simpa using h1)),
      by simp⟩
    have hins : (insert y S).PairwiseDisjoint (fun x => x • V) := by
      refine hS.insert fun x hx _ => Set.disjoint_left.2 ?_
      rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
      apply hcon x hx
      refine ⟨w * v⁻¹, Set.mul_mem_mul hw (Set.inv_mem_inv.2 (by simpa using hv)), ?_⟩
      simp only [smul_eq_mul] at hvw ⊢
      rw [eq_mul_inv_of_mul_eq hvw.symm, mul_assoc]
    exact hyS (hSmax.eq_of_subset hins (Set.subset_insert y S) ▸ Set.mem_insert y S)
end Formalism.MainNotions.LeviCoordinates
