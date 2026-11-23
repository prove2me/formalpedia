-- Prove2me | solution 1 for Bl.general_b_fact_third_alt_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:14.784862+00:00
-- url     : https://prove2.me/submissions/f31ec047-41e7-483f-b033-b7f98422b723

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdAltForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_alt_form
namespace Bl.general_b_fact_third_alt_form
theorem _root_.solution :
  ∀ {E : Type} [inst : CommRing.{0} E] {O : Subring.{0} E} {V : Type} [inst_1 : AddCommGroup.{0} V]
  [inst_2 : Module.{0, 0} E V] {ι : Type} [inst_3 : Fintype.{0} ι] [inst_4 : DecidableEq.{1} ι] (g b : ι → V),
  LinearIndependent.{0, 0, 0} (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x) g →
    Eq.{1} (Submodule.span.{0, 0} (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x) (Set.range.{0, 1} g))
        (Submodule.span.{0, 0} (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x) (Set.range.{0, 1} b)) →
      Exists.{1} fun (Q : Matrix.{0, 0, 0} ι ι (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x)) ↦
        Exists.{1} fun (P : Matrix.{0, 0, 0} ι ι (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x)) ↦
          And
            (∀ (j : ι),
              Eq.{1} (g j) (Finset.sum.{0, 0} Finset.univ.{0} fun (i : ι) ↦ HSMul.hSMul.{0, 0, 0} (Q i j) (b i)))
            (Eq.{1} (HMul.hMul.{0, 0, 0} P Q) 1) := by
  intro E _ O V _ _ ι _ _ g b hg hspan
  have hgb : ∀ j, g j ∈ Submodule.span O (Set.range b) := fun j => hspan ▸ Submodule.subset_span ⟨j, rfl⟩
  have hbg : ∀ i, b i ∈ Submodule.span O (Set.range g) := fun i => hspan.symm ▸ Submodule.subset_span ⟨i, rfl⟩
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun O).1 (hgb j)
  choose d hd using fun i => (Submodule.mem_span_range_iff_exists_fun O).1 (hbg i)
  have key : ∀ j, ∑ k, ((Matrix.of fun k i => d i k) * (Matrix.of fun i j => c j i)) k j • g k = g j := by
    intro j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    conv_rhs => rw [← hc j]
    simp only [← hd, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  refine ⟨Matrix.of fun i j => c j i, Matrix.of fun k i => d i k, fun j => (hc j).symm, ?_⟩
  ext k j
  have hz := Fintype.linearIndependent_iff.1 hg
    (fun k => ((Matrix.of fun k i => d i k) * (Matrix.of fun i j => c j i)) k j - (1 : Matrix ι ι O) k j) ?_ k
  · exact congrArg Subtype.val (sub_eq_zero.1 hz)
  · simp only [sub_smul, Finset.sum_sub_distrib, key, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
end Bl.general_b_fact_third_alt_form
