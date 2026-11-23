-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.split_of_snf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:48.085802+00:00
-- url     : https://prove2.me/submissions/5c8408b8-64f5-4daf-b7d7-ae791b659c12

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {O K Z : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [ValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup Z] [Module K Z] [Module O Z]
  [IsScalarTower O K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (N NB : Submodule O Z) (a : O) (ha : a ≠ 0)
    {ι : Type*} [Fintype ι] {n : ℕ} (snf : Basis.SmithNormalForm (NB.comap N.subtype) ι n) :
    ∃ W : Submodule K Z,
      (∀ x ∈ N, ∃ y ∈ N, ∃ t ∈ N, y ∈ W ∧ a • t ∈ NB ∧ x = y + t) ∧
      (∀ x ∈ W, a • x ∈ N → a • x ∈ NB → x ∈ N) := by
  classical
  let v : ι → Z := fun j => (snf.bM j : Z)
  have hvN : ∀ j, v j ∈ N := fun j => (snf.bM j).2
  have hliA : LinearIndependent O v := snf.bM.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).mp hliA
  let good : ι → Prop := fun j => ∃ i, snf.f i = j ∧ snf.a i ∣ a
  have hexp : ∀ (x : Z) (hx : x ∈ N), x = ∑ j, (snf.bM.repr ⟨x, hx⟩ j) • v j := by
    intro x hx
    have := congrArg (N.subtype) (snf.bM.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    simpa using this.symm
  have haK : algebraMap O K a ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact ha
  refine ⟨Submodule.span K (v '' {j | ¬ good j}), ?_, ?_⟩
  · intro x hxN
    refine ⟨∑ j with ¬ good j, (snf.bM.repr ⟨x, hxN⟩ j) • v j, ?_,
      ∑ j with ¬ ¬ good j, (snf.bM.repr ⟨x, hxN⟩ j) • v j, ?_, ?_, ?_, ?_⟩
    · exact Submodule.sum_mem _ (fun j _ => N.smul_mem _ (hvN j))
    · exact Submodule.sum_mem _ (fun j _ => N.smul_mem _ (hvN j))
    · refine Submodule.sum_mem _ (fun j hj => ?_)
      have hj' : ¬ good j := (Finset.mem_filter.mp hj).2
      rw [← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj', rfl⟩)
    · rw [Finset.smul_sum]
      refine Submodule.sum_mem _ (fun j hj => ?_)
      have hj' : good j := not_not.mp (Finset.mem_filter.mp hj).2
      obtain ⟨i, rfl, d, hd⟩ := hj'
      have h1 : (((snf.bN i : ↥(NB.comap N.subtype)) : N) : Z) ∈ NB := (snf.bN i).2
      rw [snf.snf i, Submodule.coe_smul] at h1
      have h2 : a • ((snf.bM.repr ⟨x, hxN⟩ (snf.f i)) • v (snf.f i)) =
          ((snf.bM.repr ⟨x, hxN⟩ (snf.f i)) * d) • (snf.a i • (snf.bM (snf.f i) : Z)) := by
        rw [smul_smul, smul_smul]
        congr 1
        rw [hd]
        ring
      rw [h2]
      exact NB.smul_mem _ h1
    · rw [Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => ¬ good j)]
      exact hexp x hxN
  · intro x hxW haxN hxC
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hxW
    rw [Finsupp.mem_supported'] at hl
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul K (v i))]
      at hlx
    let m : ↥(NB.comap N.subtype) := ⟨⟨a • x, haxN⟩, hxC⟩
    have hsum : ∑ j, (algebraMap O K a * l j - algebraMap O K (snf.bM.repr (m : N) j)) • v j
        = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, algebraMap_smul]
      rw [← Finset.smul_sum, hlx, sub_eq_zero]
      exact hexp (a • x) haxN
    have hco : ∀ j, algebraMap O K a * l j = algebraMap O K (snf.bM.repr (m : N) j) := fun j =>
      sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ hsum j)
    have hint : ∀ j, ∃ s : O, l j = algebraMap O K s := by
      intro j
      by_cases hg : good j
      · exact ⟨0, by rw [hl j (by simpa using hg), map_zero]⟩
      by_cases hr : ∃ i, snf.f i = j
      · obtain ⟨i, rfl⟩ := hr
        have hnd : ¬ snf.a i ∣ a := fun h => hg ⟨i, rfl, h⟩
        obtain ⟨u, hu⟩ := (ValuationRing.dvd_total (snf.a i) a).resolve_left hnd
        have hzi : snf.bM.repr (m : N) (snf.f i) = snf.a i * snf.bN.repr m i := by
          have := snf.repr_apply_embedding_eq_repr_smul m (i := i)
          rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at this
          exact this
        refine ⟨u * snf.bN.repr m i, ?_⟩
        have h4 := hco (snf.f i)
        rw [hzi, hu, map_mul, map_mul, mul_assoc] at h4
        rw [mul_left_cancel₀ haK h4, map_mul]
      · have h0 : snf.bM.repr (m : N) j = 0 :=
          snf.repr_eq_zero_of_notMem_range m (by simpa using hr)
        have h4 := hco j
        rw [h0, map_zero] at h4
        exact ⟨0, by rw [(mul_eq_zero.mp h4).resolve_left haK, map_zero]⟩
    choose s hs using hint
    rw [← hlx]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [hs j, algebraMap_smul]
    exact N.smul_mem (s j) (hvN j)
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
