-- Prove2me | solution 1 for BalanceSpecification.generateFrom_centeredCylinderFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:55:25.501797+00:00
-- url     : https://prove2.me/submissions/4a83cf0b-7234-478f-96d7-821ffad777ca

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) :
    (inferInstance : MeasurableSpace X.carrier) =
      MeasurableSpace.generateFrom (centeredCylinderFamily X) := by
  classical
  have hcoord (k : ℤ) (a : A) : MeasurableSet[MeasurableSpace.generateFrom (centeredCylinderFamily X)] {x : X.carrier | x.val k = a} := by
    let N := k.natAbs
    let j := (k + (N : ℤ)).toNat
    have hklo : -(N : ℤ) ≤ k := by
      have h := Int.le_natAbs (a := -k)
      simpa only [N, Int.natAbs_neg, neg_neg] using neg_le_neg h
    have hkhi : k ≤ (N : ℤ) := Int.le_natAbs
    have hjcast : (j : ℤ) = k + (N : ℤ) := Int.toNat_of_nonneg (by omega)
    have hj : j < 2 * N + 1 := by omega
    have heq : {x : X.carrier | x.val k = a} =
        ⋃ f : Fin (2*N+1) → A, ⋃ (_ : f ⟨j, hj⟩ = a),
          cylinder X (List.ofFn f) (-(N : ℤ)) := by
      ext x
      constructor
      · intro hx
        change x.val k = a at hx
        apply Set.mem_iUnion.mpr
        refine ⟨fun i => x.val (-(N : ℤ) + (i.val : ℤ)), ?_⟩
        apply Set.mem_iUnion.mpr
        refine ⟨?_, ?_⟩
        · have hc : -(N : ℤ) + (j : ℤ) = k := by omega
          simpa only [hc] using hx
        · change block x.val (-(N : ℤ)) (List.ofFn _).length = _
          simp only [List.length_ofFn]
          rfl
      · intro hx
        change x.val k = a
        obtain ⟨f, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hf, hx⟩ := Set.mem_iUnion.mp hx
        have h := (mem_wordCylinder_iff.mp hx) ⟨j, by simpa only [List.length_ofFn] using hj⟩
        have hc : -(N : ℤ) + (j : ℤ) = k := by omega
        simpa only [hc, List.getElem_ofFn, hf] using h
    rw [heq]
    apply MeasurableSet.iUnion
    intro f
    apply MeasurableSet.iUnion
    intro hf
    exact measurableSet_generateFrom ⟨N, List.ofFn f, List.length_ofFn, rfl⟩
  apply le_antisymm
  · have hval : @Measurable X.carrier (Configuration A)
        (MeasurableSpace.generateFrom (centeredCylinderFamily X)) inferInstance Subtype.val := by
      let : MeasurableSpace X.carrier := MeasurableSpace.generateFrom (centeredCylinderFamily X)
      apply measurable_pi_iff.mpr
      intro k
      exact measurable_to_countable' (hcoord k)
    intro E hE
    obtain ⟨t, ht, rfl⟩ := hE
    exact hval ht
  · apply generateFrom_le
    rintro E ⟨N, w, _hlen, rfl⟩
    change MeasurableSet (Subtype.val ⁻¹' wordCylinder w (-(N : ℤ)))
    exact ((isOpen_wordCylinder w _).preimage continuous_subtype_val).measurableSet
end BalanceSpecification
