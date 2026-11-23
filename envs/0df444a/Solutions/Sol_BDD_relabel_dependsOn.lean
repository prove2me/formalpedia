-- Prove2me | solution 1 for BDD.relabel_dependsOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:22:16.192932+00:00
-- url     : https://prove2.me/submissions/cc2286ca-3518-418d-8717-4348ae656e9a

import Definitions.Def_Bdd_Reduce
import Definitions.Def_Bdd_Apply
import Definitions.Def_Bdd_Relabel
import Definitions.Def_Bdd_Choice
import Definitions.Def_Bdd_Restrict
import Definitions.Def_Bdd_Evaluate
import Definitions.Def_Bdd_Sim
import Definitions.Def_Bdd_Size
import Definitions.Def_Bdd_Count
import Definitions.Def_Bdd_BDD
import Theorems.Thm_Lift_olift_evaluate
import Theorems.Thm_Lift_olift_olift
import Theorems.Thm_Nary_eq_of_forall_dependency_getElem_eq
import Theorems.Thm_Nary_ne_implies_dependency_getElem_ne
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_Reduce_oreduce_evaluate
import Theorems.Thm_Relabel_orelabel_id
attribute [local simp] Lift.olift_evaluate
attribute [local simp] Lift.olift_olift
attribute [local simp] Nary.restrict_const
attribute [local simp] Reduce.oreduce_evaluate
attribute [local simp] Relabel.orelabel_id



set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Lift.olift Relabel.orelabel Reduce.oreduce
open BDD
attribute [local implicit_reducible] lift
attribute [local implicit_reducible] denotation
attribute [local implicit_reducible] const var apply
attribute [local implicit_reducible] relabel'' relabel'
namespace BDD
theorem _root_.solution {n} {B : BDD} {f : Fin B.nvars → Fin n} {hf h i} :
  Nary.DependsOn ((B.relabel f hf).denotation h) i ↔
  ∃ j, i = f j ∧ Nary.DependsOn B.denotation' j :=
  by
    have h1 : ∀ (i i' : Nary.Dependency B.denotation'), f i.val = f i'.val ↔ i = i' := by
      rintro i i'
      have := hf i i'
      specialize hf i i'
      grind only [Subtype.val_inj]
    simp only [Nary.DependsOn, Nary.IndependentOf, BDD.relabel_denotation, BDD.denotation',
      Fin.getElem_fin, Bool.forall_bool, not_and, not_forall]
    constructor
    · intro h2
      rw [imp_iff_not_or, not_forall] at h2
      rcases h2 with ⟨v, h2⟩ | ⟨v, h2⟩
      · have h3 := Nary.ne_implies_dependency_getElem_ne h2
        rcases h3 with ⟨j, h3⟩
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_set, Bool.if_false_left,
          ne_eq, Bool.eq_and_self, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
          Classical.not_imp, Decidable.not_not, Fin.val_inj] at h3
        use j.val, h3.2
        intro h4
        use Vector.ofFn fun j ↦ (v.set i false)[f j]
        apply ne_of_ne_of_eq (ne_comm.1 h2)
        apply Nary.eq_of_forall_dependency_getElem_eq
        intro j'
        specialize h1 j j'
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Vector.getElem_set,
          Bool.if_false_left, Bool.if_true_left]
        grind only [= Lean.Grind.toInt_fin, Vector.getElem_set]
      · have h3 := Nary.ne_implies_dependency_getElem_ne h2
        rcases h3 with ⟨j, h3⟩
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Vector.getElem_set, Fin.val_inj,
          Bool.if_true_left, ne_eq, Bool.eq_or_self, decide_eq_true_eq, Classical.not_imp,
          Bool.not_eq_true] at h3
        use j.val, h3.1
        intro h4
        use Vector.ofFn fun j ↦ v[f j]
        apply ne_of_ne_of_eq h2
        apply Nary.eq_of_forall_dependency_getElem_eq
        rintro j'
        specialize h1 j j'
        simp only [h3, Vector.getElem_set, Bool.if_true_left, Fin.getElem_fin, Vector.getElem_ofFn,
          Fin.eta]
        grind only [= Lean.Grind.toInt_fin]
    · rintro ⟨j, rfl, h2⟩ h3
      simp_all only [Vector.set_set, not_true_eq_false, exists_const, imp_false, not_forall]
      rcases h2 with ⟨v, h2⟩
      apply h2
      have : ∀ i, Decidable (∃ j : Nary.Dependency B.denotation', i = f j.val) := by
        intro i
        apply Classical.propDecidable
      let g := fun i ↦ if h : ∃ j : Nary.Dependency B.denotation', i = f j.val then v[h.choose.val] else false
      have hg : ∀ j' : Nary.Dependency B.denotation', g (f j'.val) = v[j'.val] := by
        rintro ⟨j', hj'⟩
        simp [g]
        split
        next h =>
          obtain ⟨j'', h⟩ := h
          simp_all only [Classical.choose_eq']
          specialize h1 ⟨j', hj'⟩ j''
          simp [h] at h1
          rcases h1 with rfl
          simp
        next h =>
          rw [not_exists] at h
          specialize h ⟨j', hj'⟩
          simp at h
      specialize h3 (Vector.ofFn g)
      simp only [Vector.getElem_ofFn, Fin.eta, Vector.getElem_set, Fin.val_inj,
        Bool.if_false_left] at h3
      calc
        B.denotation le_rfl v
        _ = B.denotation le_rfl (Vector.ofFn fun i ↦ g (f i)) := by
          apply Nary.eq_of_forall_dependency_getElem_eq
          simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, hg, implies_true]
        _ = B.denotation le_rfl (Vector.ofFn fun i ↦ !decide (f j = f i) && g (f i)) := h3
        _ = B.denotation le_rfl (v.set j.val false _) := by
          apply Nary.eq_of_forall_dependency_getElem_eq
          simp only [denotation', Nary.DependsOn, Nary.IndependentOf, Fin.getElem_fin,
            Vector.getElem_ofFn, Fin.eta, Vector.getElem_set, Fin.val_inj, Bool.if_false_left, hg]
          apply Nary.ne_implies_dependency_getElem_ne at h2
          simp [Vector.getElem_set, Fin.val_inj] at h2
          rcases h2 with ⟨j, h2, rfl⟩
          intro j'
          specialize h1 j j'
          simp only [Nary.DependsOn, Nary.IndependentOf] at *
          by_cases hjj : j = j'
          · simp [hjj]
          · have hfj : f j.val ≠ f j'.val := fun h => hjj (h1.mp h)
            have hvj : j.val ≠ j'.val := fun h => hjj (Subtype.ext h)
            simp [hfj, hvj]
end BDD
