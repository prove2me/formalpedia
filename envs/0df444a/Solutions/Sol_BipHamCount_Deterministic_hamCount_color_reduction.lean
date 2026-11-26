-- Prove2me | solution 1 for BipHamCount.Deterministic.hamCount_color_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:54:15.188697+00:00
-- url     : https://prove2.me/submissions/754b7191-7913-4409-83fe-a4d4a028ed48

import Definitions.Def_BipHamCount_Deterministic_Core
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Nodup
open BipHamCount.Deterministic Equiv
namespace BipHamGraph

private theorem cycle_transport {V W : Type*} (e : V ≃ W) (p : Equiv.Perm V) (h : p.IsCycle) :
    (e.permCongr p).IsCycle := by
  obtain ⟨x,hx,hs⟩ := h
  refine ⟨e x,by simpa [Equiv.permCongr_apply] using hx,?_⟩
  intro y hy
  obtain ⟨y,rfl⟩ := e.surjective y
  obtain ⟨k,hk⟩ := hs (by simpa [Equiv.permCongr_apply] using hy : p y ≠ y)
  refine ⟨k,?_⟩
  change ((e.permCongrHom p)^k) (e x) = e y
  rw [←map_zpow]
  change e ((p ^ k) ((e.symm) (e x))) = _
  simp [hk]

private def ok {V : Type*} [Fintype V] [DecidableEq V] (adj : V → V → Bool) (p : Equiv.Perm V) :=
  p.IsCycle ∧ p.support=Finset.univ ∧ ∀ x, adj x (p x)=true

private theorem forward {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (g : V → V → Bool) (f : W → W → Bool) (h : ∀ x y, f (e x) (e y)=g x y)
    (p : Equiv.Perm V) (hp : ok g p) : ok f (e.permCongr p) := by
  refine ⟨cycle_transport e p hp.1,?_,?_⟩
  · apply Finset.eq_univ_of_forall
    intro z; obtain ⟨x,rfl⟩ := e.surjective z
    have hx : x∈p.support := hp.2.1 ▸ Finset.mem_univ _
    simpa [Equiv.Perm.mem_support,Equiv.permCongr_apply] using hx
  · intro z; obtain ⟨x,rfl⟩ := e.surjective z
    simpa [Equiv.permCongr_apply,h] using hp.2.2 x

theorem hamCount_congr {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (g : V → V → Bool) (f : W → W → Bool) (h : ∀ x y, f (e x) (e y)=g x y) :
    hamCount g = hamCount f := by
  classical
  let P := (Finset.univ : Finset (Equiv.Perm V)).filter (ok g)
  let Q := (Finset.univ : Finset (Equiv.Perm W)).filter (ok f)
  have htV : hamCount g=P.card := by unfold hamCount; congr 1; ext; simp [P,ok]
  have htW : hamCount f=Q.card := by unfold hamCount; congr 1; ext; simp [Q,ok]
  rw [htV,htW]
  have eq : P.map e.permCongr.toEmbedding = Q := by
    ext z; obtain ⟨p,rfl⟩ := e.permCongr.surjective z
    simp only [Finset.mem_map_equiv,P,Q,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply]
    constructor
    · exact forward e g f h p
    · intro hp
      have he := forward e.symm f g (fun x y => by simpa using (h (e.symm x) (e.symm y)).symm) _ hp
      simpa [←Equiv.permCongr_symm] using he
  rw [←eq,Finset.card_map]

theorem hamCount_unbalanced {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V → Bool) (c : V → Bool) (hc : ∀ i j, g i j=true → c i≠c j)
    (hn : (Finset.univ.filter (fun i => c i=false)).card ≠ (Finset.univ.filter (fun i => c i=true)).card) :
    hamCount g = 0 := by
  classical
  unfold hamCount
  apply Finset.card_filter_eq_zero_iff.mpr
  intro p hp hg
  apply hn
  let F := Finset.univ.filter (fun i => c i=false)
  let T := Finset.univ.filter (fun i => c i=true)
  have hs (i : V) := hc i (p i) (hg.2.2 i)
  have he : F.map p.toEmbedding = T := by
    ext j; obtain ⟨i,rfl⟩ := p.surjective j
    simp only [F,T,Finset.mem_map_equiv,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply]
    have hh := hs i
    cases hi : c i <;> cases hj : c (p i) <;> simp_all
  rw [←Finset.card_map (f:=p.toEmbedding) (s:=F),he]
end BipHamGraph
namespace BipHamGraph
open BipHamCount.Deterministic

theorem balanced_sides {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V → Bool) (c : V → Bool) (hc : ∀ i j, g i j=true → c i≠c j)
    (m : ℕ) (left right : Fin m → V) (hl : Function.Injective left) (hr : Function.Injective right)
    (hcl : ∀ v, (∃ i, left i=v) ↔ c v=false) (hcr : ∀ v, (∃ i, right i=v) ↔ c v=true) :
    let A : Matrix (Fin m) (Fin m) ℤ := fun i j => if g (left i) (right j) then 1 else 0
    let B : Matrix (Fin m) (Fin m) ℤ := fun j i => if g (right j) (left i) then 1 else 0
    hamCount g=hamCount (bipDigraph A B) := by
  let e' := Sum.elim left right
  have lcol (i) := (hcl _).mp ⟨i,rfl⟩
  have rcol (j) := (hcr _).mp ⟨j,rfl⟩
  let e : (Fin m ⊕ Fin m) ≃ V := Equiv.ofBijective e' ⟨by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hl h)
      | inr j => have he : left i=right j := h; have hh := lcol i; rw [he,rcol] at hh; contradiction
    | inr i =>
      cases y with
      | inl j => have he : right i=left j := h; have hh := rcol i; rw [he,lcol] at hh; contradiction
      | inr j => exact congrArg Sum.inr (hr h),by
    intro v; cases h : c v with
    | false => obtain ⟨i,hi⟩ := (hcl _).mpr h; exact ⟨.inl i,hi⟩
    | true => obtain ⟨i,hi⟩ := (hcr _).mpr h; exact ⟨.inr i,hi⟩⟩
  dsimp only
  symm
  apply hamCount_congr e
  rintro (i|i) (j|j)
  · change g (left i) (left j) = false
    cases h : g (left i) (left j)
    · rfl
    · exact False.elim ((hc _ _ h) ((lcol i).trans (lcol j).symm))
  · change g (left i) (right j) = decide ((if g (left i) (right j) then 1 else 0 : ℤ)=1)
    cases g (left i) (right j) <;> decide
  · change g (right i) (left j) = decide ((if g (right i) (left j) then 1 else 0 : ℤ)=1)
    cases g (right i) (left j) <;> decide
  · change g (right i) (right j) = false
    cases h : g (right i) (right j)
    · rfl
    · exact False.elim ((hc _ _ h) ((rcol i).trans (rcol j).symm))

theorem side_length {V : Type*} [Fintype V] [DecidableEq V] (l : List V) (hn : l.Nodup) (c : V → Bool) (b : Bool)
    (hm : ∀ v, v∈l ↔ c v=b) : l.length=(Finset.univ.filter (fun v => c v=b)).card := by
  rw [←List.toFinset_card_of_nodup hn]
  congr 1
  ext v; simp [hm]

end BipHamGraph
namespace BipHamGraph
open BipHamCount.Deterministic

def side (n : ℕ) (c : Fin n → Bool) (b : Bool) := (List.finRange n).filter (fun i => decide (c i=b))

theorem color_reduction (n : ℕ) (g : Fin n → Fin n → Bool) (c : Fin n → Bool)
    (hc : ∀ i j, g i j=true → c i≠c j) :
    let L := side n c false
    let R := side n c true
    if h : L.length=R.length then
      let f := L.get
      let t := fun i : Fin L.length => R.get (Fin.cast h i)
      let A : Matrix (Fin L.length) (Fin L.length) ℤ := fun i j => if g (f i) (t j) then 1 else 0
      let B : Matrix (Fin L.length) (Fin L.length) ℤ := fun j i => if g (t j) (f i) then 1 else 0
      hamCount g=hamCount (bipDigraph A B)
    else hamCount g=0 := by
  dsimp only
  have sm (b : Bool) (v : Fin n) : v ∈ side n c b ↔ c v=b := by simp [side]
  have sn (b : Bool) : (side n c b).Nodup := (List.nodup_finRange n).filter _
  split
  next h =>
    apply balanced_sides g c hc _ _ _ (sn false).injective_get
      ((sn true).injective_get.comp (Fin.cast_injective h))
    · intro v; rw [← sm false]
      exact List.mem_iff_get.symm
    · intro v; rw [← sm true]
      constructor
      · rintro ⟨i,hi⟩
        exact List.mem_iff_get.mpr ⟨_,hi⟩
      · intro hv
        obtain ⟨j,hj⟩ := List.mem_iff_get.mp hv
        exact ⟨Fin.cast h.symm j,by simpa using hj⟩
  next h =>
    apply hamCount_unbalanced g c hc
    rw [←side_length _ (sn false) c false (sm false),←side_length _ (sn true) c true (sm true)]
    exact h
end BipHamGraph

open BipHamCount.Deterministic
theorem solution (n : ℕ) (g : Fin n → Fin n → Bool) (c : Fin n → Bool)
    (hc : ∀ i j, g i j=true → c i≠c j) :
    let L := (List.finRange n).filter (fun i => decide (c i=false))
    let R := (List.finRange n).filter (fun i => decide (c i=true))
    if h : L.length=R.length then
      let f := L.get
      let t := fun i : Fin L.length => R.get (Fin.cast h i)
      let A : Matrix (Fin L.length) (Fin L.length) ℤ := fun i j => if g (f i) (t j) then 1 else 0
      let B : Matrix (Fin L.length) (Fin L.length) ℤ := fun j i => if g (t j) (f i) then 1 else 0
      hamCount g=hamCount (bipDigraph A B)
    else hamCount g=0 := BipHamGraph.color_reduction n g c hc
