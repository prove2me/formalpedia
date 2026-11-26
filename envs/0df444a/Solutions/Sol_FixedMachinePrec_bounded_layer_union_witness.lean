-- Prove2me | solution 1 for FixedMachinePrec.bounded_layer_union_witness
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:34:30.532518+00:00
-- url     : https://prove2.me/submissions/7209dae6-52bd-4ae5-8ab1-63ee323aa864

import Definitions.Def_FixedMachinePrec_GenerateFamily

open FixedMachinePrec

private def leftJob {q : ℕ} (i : Fin q) : Fin (2*q) := ⟨2*i.val, by omega⟩
private def rightJob {q : ℕ} (i : Fin q) : Fin (2*q) := ⟨2*i.val+1, by omega⟩
private def breaks {q : ℕ} (A : Finset (Fin (2*q))) : Finset (Fin q) :=
  Finset.univ.filter fun i => ¬(leftJob i ∈ A ↔ rightJob i ∈ A)

private theorem bounded_breaks {q m : ℕ} (hm : 1 ≤ m) (φ : Formula (2*q)) (hv : φ.Valid m) :
    (breaks (φ.eval (fun _ _ => False) (fun x => x.val+1))).card ≤ m*φ.leaves := by
  have sparse (A : Finset (Fin (2*q))) : (breaks A).card ≤ A.card := by
    let pair (x : Fin (2*q)) : Fin q := ⟨x.val/2, by omega⟩
    apply (Finset.card_le_card (t := A.image pair) ?_).trans (Finset.card_image_le)
    intro i hi
    simp only [breaks,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    by_cases hl : leftJob i ∈ A
    · exact Finset.mem_image.mpr ⟨_,hl,Fin.ext (by simp [pair,leftJob])⟩
    · have hr : rightJob i ∈ A := by tauto
      exact Finset.mem_image.mpr ⟨_,hr,Fin.ext (by dsimp [pair,rightJob]; omega)⟩
  induction φ with
  | atom a =>
    simp only [Formula.eval, Formula.leaves, Nat.mul_one]
    cases a with
    | rankSuffix h =>
      let exceptional := (Finset.univ : Finset (Fin q)).filter fun i => 2*i.val+2 = h
      apply (Finset.card_le_card (t := exceptional) ?_).trans ((Finset.card_le_one.mpr ?_).trans hm)
      · intro i hi
        simp [breaks,Atom.eval,Atom.rankSuffixSet,leftJob,rightJob] at hi
        simp [exceptional]; omega
      · intro i hi j hj
        simp [exceptional] at hi hj
        exact Fin.ext (by omega)
    | univ => simp [breaks,Atom.eval]
    | empty => simp [breaks,Atom.eval]
    | boundary A => exact (sparse A).trans (le_of_eq hv)
    | pred A => simp [Atom.eval,predCone,breaks]
    | succ A => simp [Atom.eval,succCone,breaks]
    | weakPred A => simpa [Atom.eval,weakPredCone,predCone] using (sparse A).trans (le_of_eq hv)
    | weakSucc A => simpa [Atom.eval,weakSuccCone,succCone] using (sparse A).trans (le_of_eq hv)
  | compl φ ih =>
    apply le_trans (Finset.card_le_card ?_) (ih hv)
    intro i hi
    simp [Formula.eval,breaks] at hi ⊢; tauto
  | union φ ψ hφ hψ | inter φ ψ hφ hψ =>
    have step := Nat.add_le_add (hφ hv.1) (hψ hv.2)
    rw [Formula.leaves,Nat.mul_add]
    apply (Finset.card_le_card ?_).trans ((Finset.card_union_le _ _).trans step)
    intro i hi
    simp [breaks, Formula.eval] at hi ⊢
    tauto

theorem solution (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) : ∃ (N : ℕ) (p : Fin N → Fin N → Prop) (_ : DecidableRel p) (r : Fin N → ℕ), IsStrictOrder' p ∧ IsTopoRank p r ∧ ∃ X ∈ family p r m k, ∃ Y ∈ family p r m k, X ∪ Y ∉ family p r m k := by
  classical
  let q := m*k+1
  let p : Fin (2*q) → Fin (2*q) → Prop := fun _ _ => False
  let r := fun x : Fin (2*q) => x.val+1
  let F := family p r m k
  refine ⟨2*q,p,inferInstance,r,by simp [IsStrictOrder',p],?_,?_⟩
  · refine ⟨fun x => ⟨by simp [r], by dsimp [r]; omega⟩,fun x y h => Fin.ext (by simpa [r] using h),by simp [p]⟩
  by_contra! closed
  have un (A B) (ha : A ∈ F) (hb : B ∈ F) : A ∪ B ∈ F := closed A ha B hb
  have co (A) (ha : A ∈ F) : Finset.univ \ A ∈ F := by
    simp only [F,family,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
    obtain ⟨φ,hv,hl,rfl⟩ := ha
    exact ⟨φ.compl,hv,hl,rfl⟩
  have atom (a : Atom (2*q)) (h : a.Valid m) : a.eval p r ∈ F := by
    simp only [F,family,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨.atom a,h,hk,rfl⟩
  have single (x : Fin (2*q)) : {x} ∈ F := by
    let A := (Atom.rankSuffix (N := 2*q) (x.val+1)).eval p r
    let B := (Atom.rankSuffix (N := 2*q) (x.val+2)).eval p r
    have hA : A ∈ F := atom _ ⟨by omega,by omega⟩
    have hB : B ∈ F := atom _ ⟨by omega,by omega⟩
    have hset : Finset.univ \ ((Finset.univ \ A) ∪ B) = {x} := by
      ext y
      simp [A,B,Atom.eval,Atom.rankSuffixSet,r,Fin.ext_iff] <;> omega
    exact hset ▸ co _ (un _ _ (co _ hA) hB)
  have allSets (A : Finset (Fin (2*q))) : A ∈ F := by
    induction A using Finset.induction_on with
    | empty => exact atom .empty trivial
    | insert x A _ ih => simpa using un _ _ (single x) ih
  let alt := (Finset.univ : Finset (Fin (2*q))).filter fun x => x.val%2 = 0
  have allBreak : breaks alt = Finset.univ := by ext i; simp [breaks,alt,leftJob,rightJob]
  have ha := allSets alt
  simp only [F,family,Finset.mem_filter,Finset.mem_univ,true_and] at ha
  obtain ⟨φ,hv,hl,he⟩ := ha
  have bound := bounded_breaks hm φ hv
  change (breaks (φ.eval p r)).card ≤ m*φ.leaves at bound
  rw [he,allBreak,Finset.card_univ,Fintype.card_fin] at bound
  exact (Nat.not_succ_le_self (m*k)) (bound.trans (Nat.mul_le_mul_left _ hl))
