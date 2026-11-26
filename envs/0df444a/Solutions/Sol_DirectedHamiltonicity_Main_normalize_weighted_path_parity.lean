-- Prove2me | solution 1 for DirectedHamiltonicity.Main.normalize_weighted_path_parity
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:24:47.382607+00:00
-- url     : https://prove2.me/submissions/864de25c-9795-4fde-82df-8d3866a41dfb

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_DetSum


namespace DirectedHamiltonicity.Normalize
open Main Main.Multidigraph Finset
variable {V E F : Type} [Fintype V] [Fintype E] [Fintype F]

abbrev Len (V : Type) [Fintype V] := Fin (Fintype.card V - 1)
def Valid (H : Multidigraph V E) (w : E → ℕ) (s t : V) (B : ℤ) (p : Len V → E) :=
  H.IsHamPath s t p ∧ (pathWeight w p : ℤ) = B

private theorem counted (H : Multidigraph V E) (w : E → ℕ) (s t : V) (B : ℤ)
    [Fintype {p // Valid H w s t B p}] :
    H.weightedPathCount w s t B = Fintype.card {p // Valid H w s t B p} := by
  classical
  let Q := (H.hamPaths s t).filter (fun q => (pathWeight w q : ℤ) = B)
  have iff (p : Len V → E) : p ∈ Q ↔ Valid H w s t B p := by
    simp only [Q,hamPaths,mem_filter,mem_univ,true_and,Valid]
  let equiv : Q ≃ {p // Valid H w s t B p} :=
    { toFun := fun p => ⟨p.val,(iff _).mp p.property⟩
      invFun := fun p => ⟨p.val,(iff _).mpr p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_coe Q).symm.trans (Fintype.card_congr equiv)

/-- The fiber of a projected arc sequence consists of independent label choices at its positions. -/
private abbrev fibers (π : E → F) (p : Len V → F) :=
  (i : Len V) → {e : E // π e = p i}

open Classical in
/-- Count labeled weighted paths by projecting to arcs of a second multigraph.
The map need not be surjective; empty fibers contribute zero. -/
theorem countByFibers (H : Multidigraph V E) (G : Multidigraph V F)
    (w : E → ℕ) (z : F → ℕ) (π : E → F)
    (ht : ∀ e, H.tail e=G.tail (π e)) (hh : ∀ e, H.head e=G.head (π e))
    (hw : ∀ e, w e=z (π e)) (s t : V) (B : ℤ) :
    H.weightedPathCount w s t B =
      ∑ p ∈ (G.hamPaths s t).filter (fun p => (pathWeight z p : ℤ)=B),
        ∏ i, (univ.filter (fun e => π e = p i)).card := by
  classical
  have ok (p : Len V → E) : Valid H w s t B p ↔ Valid G z s t B (π ∘ p) := by
    have v : H.walkVerts s p = G.walkVerts s (π ∘ p) := by
      apply funext; intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact hh (p j)
    simp only [Valid,IsHamPath,v,ht,Function.comp_apply,pathWeight,hw]
  let morph : {p // Valid H w s t B p} ≃
      (q : {p // Valid G z s t B p}) × fibers π q.val :=
    { toFun := fun p => ⟨⟨π ∘ p.val,(ok _).mp p.property⟩,fun i => ⟨p.val i,rfl⟩⟩
      invFun := fun q => ⟨fun i => (q.2 i).val,(ok _).mpr (by
        have eq : (π ∘ fun i => (q.2 i).val) = q.1.val := funext (fun i => (q.2 i).property)
        rw [eq]; exact q.1.property)⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨p,h⟩,v⟩
        have inner : (fun i => π (v i).val) = p := funext fun i => (v i).property
        apply Sigma.ext (Subtype.ext inner)
        exact Function.hfunext (by rfl) (fun i j e => by
          cases eq_of_heq e
          exact Subtype.heq_iff_coe_eq (by simp [(v i).property]) |>.2 rfl) }
  rw [counted H w s t B,Fintype.card_congr morph,Fintype.card_sigma]
  change (∑ q : {p // Valid G z s t B p}, Fintype.card ((i : Len V) → {e // π e = q.val i})) = _
  simp only [Fintype.card_pi,Fintype.card_subtype]
  symm
  apply Finset.sum_subtype _ (fun p => ?_)
  simp only [hamPaths,mem_filter,mem_univ,true_and,Valid]
def Usable (G : Multidigraph V F) (s t : V) (f : F) :=
  G.tail f ≠ G.head f ∧ G.head f ≠ s ∧ G.tail f ≠ t

private theorem usableOnPath (G : Multidigraph V F) (s t : V) (p : Len V → F)
    (hp : G.IsHamPath s t p) (i : Len V) : Usable G s t (p i) := by
  obtain ⟨tail,inj,last⟩ := hp
  have head : G.head (p i) = G.walkVerts s p i.succ := rfl
  have first : G.walkVerts s p 0 = s := rfl
  constructor
  · intro eq
    have same := inj ((tail i).symm.trans (eq.trans head))
    have := congrArg Fin.val same
    simp at this
  constructor
  · intro eq
    have same := inj (head.symm.trans (eq.trans first.symm))
    exact Fin.succ_ne_zero _ same
  · intro eq
    have same := inj ((tail i).symm.trans (eq.trans last.symm))
    exact Fin.castSucc_ne_last i same

open Classical in
private theorem subfiber {F : Type} [Fintype F] (P : F → Prop) (f : F) :
    (univ.filter (fun e : {x // P x} => e.val=f)).card = if P f then 1 else 0 := by
  classical
  by_cases hf : P f
  · rw [if_pos hf]
    have eq : univ.filter (fun e : {x // P x} => e.val=f) = {⟨f,hf⟩} := by
      ext e; simp only [mem_filter,mem_univ,true_and,mem_singleton]
      constructor
      · intro h; apply Subtype.ext; exact h
      · rintro rfl; rfl
    rw [eq,card_singleton]
  · rw [if_neg hf,card_eq_zero]; apply eq_empty_iff_forall_notMem.mpr
    intro x h
    obtain ⟨_,eq⟩ := mem_filter.mp h
    exact hf (eq ▸ x.property)

open Classical in
/-- Delete inadmissible arcs and keep precisely one representative of each odd-multiplicity
arc class. Projecting along labels preserves the exact count modulo two. -/
theorem cancelParallel (H : Multidigraph V E) (G : Multidigraph V F)
    (w : E → ℕ) (z : F → ℕ) (π : E → F)
    (ht : ∀ e, H.tail e=G.tail (π e)) (hh : ∀ e, H.head e=G.head (π e))
    (hw : ∀ e, w e=z (π e)) (s t : V) (B : ℤ)
    (keep : F → Prop) [Fintype {f // keep f}]
    (keep_iff : ∀ f, keep f ↔ Usable G s t f ∧ (univ.filter (fun e => π e=f)).card % 2 = 1) :
    (H.weightedPathCount w s t B : ZMod 2) =
      ((G.restrictArcs keep).weightedPathCount (fun e => z e.val) s t B : ZMod 2) := by
  classical
  rw [countByFibers H G w z π ht hh hw, countByFibers (G.restrictArcs keep) G (fun e => z e.val) z Subtype.val
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  simp only [Nat.cast_sum,Nat.cast_prod]
  apply sum_congr rfl
  intro q hq
  apply prod_congr rfl
  intro i _
  have path : G.IsHamPath s t q := (mem_filter.mp (mem_filter.mp hq).1).2
  have usable := usableOnPath G s t q path i
  trans ((if keep (q i) then 1 else 0 : ℕ) : ZMod 2)
  rotate_left
  · apply congrArg (Nat.cast : ℕ → ZMod 2)
    convert (subfiber keep (q i)).symm using 1 <;> congr! 4
  let m := (univ.filter (fun e => π e=q i)).card
  have eq : (keep (q i)) ↔ m%2=1 := (keep_iff _).trans ⟨And.right,fun h => ⟨usable,h⟩⟩
  by_cases odd : m%2=1
  · rw [if_pos (eq.mpr odd)]
    apply ZMod.val_injective
    change (m : ZMod 2).val = _
    rw [ZMod.val_natCast]; exact odd
  · rw [if_neg (fun h => odd (eq.mp h))]
    apply ZMod.val_injective
    change (m : ZMod 2).val = 0
    rw [ZMod.val_natCast]; omega

open Classical in
noncomputable def labels (H : Multidigraph V E) (w : E → ℕ) : Finset (V × V × ℕ) :=
  univ.image fun e => (H.tail e,H.head e,w e)

def labelMap (H : Multidigraph V E) (w : E → ℕ) (e : E) : labels H w :=
  ⟨(H.tail e,H.head e,w e),by
    classical
    exact mem_image.mpr ⟨e,mem_univ _,rfl⟩⟩

def quotientGraph (H : Multidigraph V E) (w : E → ℕ) : Multidigraph V (labels H w) :=
  ⟨fun f => f.val.1,fun f => f.val.2.1⟩
def labelWeight (H : Multidigraph V E) (w : E → ℕ) (f : labels H w) : ℕ := f.val.2.2
open Classical in
def Keep (H : Multidigraph V E) (w : E → ℕ) (s t : V) (f : labels H w) : Prop :=
  Usable (quotientGraph H w) s t f ∧ (univ.filter (fun e => labelMap H w e=f)).card % 2=1

abbrev Arc (H : Multidigraph V E) (w : E → ℕ) (s t : V) := {f : labels H w // Keep H w s t f}
def normalGraph (H : Multidigraph V E) (w : E → ℕ) (s t : V) : Multidigraph V (Arc H w s t) :=
  (quotientGraph H w).restrictArcs (Keep H w s t)
def normalWeight (H : Multidigraph V E) (w : E → ℕ) (s t : V) (f : Arc H w s t) : ℕ :=
  labelWeight H w f.val

open Classical in
/-- A single canonical graph on the same vertices satisfies every normalization
hypothesis and preserves every weighted path parity, even with parallel arcs. -/
theorem normalize (H : Multidigraph V E) (w : E → ℕ) (s t : V) :
    let G := normalGraph H w s t
    let z := normalWeight H w s t
    G.IsNormalized z s t ∧ Fintype.card (Arc H w s t) ≤ Fintype.card E ∧
    (∀ v, G.incomingWeights z v ⊆ H.incomingWeights w v) ∧
    (∀ B : ℤ, (H.weightedPathCount w s t B : ZMod 2) = (G.weightedPathCount z s t B : ZMod 2)) := by
  classical
  intro G z
  refine ⟨⟨fun a => a.property.1.1,fun a => a.property.1.2.1,fun a => a.property.1.2.2,?_⟩,?_,?_,?_⟩
  · intro a b ne tail head eq
    apply ne; apply Subtype.ext; apply Subtype.ext
    apply Prod.ext tail
    exact Prod.ext head eq
  · apply (Fintype.card_subtype_le (Keep H w s t)).trans
    rw [Fintype.card_coe]
    exact card_image_le.trans_eq card_univ
  · intro v b hb
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hb
    have vertex := (mem_filter.mp hf).2
    have fl := f.val.property
    obtain ⟨e,_,eq⟩ := mem_image.mp fl
    have sizeEq : w e=z f := congrArg (fun k : V × V × ℕ => k.2.2) eq
    have headEq : H.head e = G.head f := congrArg (fun k : V × V × ℕ => k.2.1) eq
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,headEq.trans vertex⟩,sizeEq⟩
  · intro B
    apply cancelParallel H (quotientGraph H w) w (labelWeight H w) (labelMap H w)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s t B (Keep H w s t)
    intro f
    unfold Keep
    constructor <;> rintro ⟨u,k⟩ <;> refine ⟨u,?_⟩ <;> convert k using 2 <;> congr! 4

end DirectedHamiltonicity.Normalize

namespace DirectedHamiltonicity.Normalize
open Main Main.Multidigraph
end DirectedHamiltonicity.Normalize

open DirectedHamiltonicity.Normalize DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph
open Classical in
theorem solution {V E : Type} [Fintype V] [Fintype E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V) :
    ∃ (F : Type) (ff : Fintype F) (G : Multidigraph V F) (z : F → ℕ),
      letI := ff
      G.IsNormalized z s t ∧ Fintype.card F ≤ Fintype.card E ∧
      (∀ v, G.incomingWeights z v ⊆ H.incomingWeights w v) ∧
      (∀ f, ∃ e, H.tail e=G.tail f ∧ H.head e=G.head f ∧ w e=z f) ∧
      ∀ B : ℤ, (H.weightedPathCount w s t B : ZMod 2) = (G.weightedPathCount z s t B : ZMod 2) := by
  classical
  let F := Arc H w s t
  refine ⟨F,inferInstance,normalGraph H w s t,normalWeight H w s t,?_⟩
  obtain ⟨norm,size,degrees,parity⟩ := normalize H w s t
  refine ⟨norm,size,degrees,?_,parity⟩
  intro f
  obtain ⟨e,_,eq⟩ := Finset.mem_image.mp f.val.property
  exact ⟨e,congrArg Prod.fst eq,congrArg (fun k : V × V × ℕ => k.2.1) eq,
    congrArg (fun k : V × V × ℕ => k.2.2) eq⟩
