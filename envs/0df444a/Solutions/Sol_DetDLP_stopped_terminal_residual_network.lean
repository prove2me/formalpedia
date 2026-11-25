-- Prove2me | solution 1 for DetDLP.stopped_terminal_residual_network
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:22:47.05536+00:00
-- url     : https://prove2.me/submissions/83e1859e-0ec1-48bb-8917-9e6fc0d7b5f2

import Definitions.Def_DetDLP_TerminalBTN
import Definitions.Def_DetDLP_BTN

section

namespace DetDLP.ResidualChildGraph
open Finset
variable {L P E R : Type*} [Fintype L] [Fintype P] [Fintype E] [CommRing R]

abbrev vertex := L ⊕ P
noncomputable def network (owner : E → L) (pkt : E → P) : BipartiteMultigraph where
  nV := Fintype.card (L ⊕ P)
  nE := Fintype.card E
  endpoints i := (Fintype.equivFin _ (Sum.inl (owner ((Fintype.equivFin E).symm i)) : L ⊕ P),
    Fintype.equivFin _ (Sum.inr (pkt ((Fintype.equivFin E).symm i)) : L ⊕ P))
  side v := ((Fintype.equivFin (L ⊕ P)).symm v).isRight
  bipartite e := by simp

/-- Provide the entry tensor with exactly the bits at its incident ports. -/
def supplied (G : BipartiteMultigraph) (v : Fin G.nV) (α : Fin (G.deg v) → Bool) (e : Fin G.nE) : Bool :=
  if h : e ∈ G.ports v then α ⟨(G.ports v).idxOf e,List.idxOf_lt_length_iff.mpr h⟩ else false

private theorem supplied_eq (G : BipartiteMultigraph) (v : Fin G.nV) (x : Fin G.nE → Bool)
    (e : Fin G.nE) (h : (G.endpoints e).1=v ∨ (G.endpoints e).2=v) :
    supplied G v (fun i => x ((G.ports v).get i)) e = x e := by
  have he : e ∈ G.ports v := by simp [BipartiteMultigraph.ports,h]
  rw [supplied,dif_pos he]; exact congrArg x (List.idxOf_get _)

abbrev fiber {A B : Type*} (f : A → B) (b : B) := {a : A // f a=b}

noncomputable def tensor (owner : E → L) (pkt : E → P)
    (old : (l : L) → (fiber owner l → Bool) → R)
    (fresh : (p : P) → (fiber pkt p → Bool) → R)
    (j : Fin (network owner pkt).nV) (α : Fin ((network owner pkt).deg j) → Bool) : R :=
  let bit (e : E) := supplied _ j α (Fintype.equivFin E e)
  match (Fintype.equivFin (L ⊕ P)).symm j with
  | .inl l => old l (fun e => bit e.val)
  | .inr p => fresh p (fun e => bit e.val)

theorem contract [DecidableEq E] (owner : E → L) (pkt : E → P)
    (old : (l : L) → (fiber owner l → Bool) → R)
    (fresh : (p : P) → (fiber pkt p → Bool) → R) :
    BTNContract (network owner pkt) (tensor owner pkt old fresh) =
      ∑ x : E → Bool,(∏ l,old l (fun e => x e.val))*(∏ p,fresh p (fun e => x e.val)) := by
  classical
  let G := network owner pkt
  let v := Fintype.equivFin (L ⊕ P)
  let e := Fintype.equivFin E
  let re : (Fin (Fintype.card E) → Bool) ≃ (E → Bool) := (e.arrowCongr (Equiv.refl Bool)).symm
  unfold BTNContract
  apply Fintype.sum_equiv re; intro x
  let V (j : L ⊕ P) := Sum.elim (fun l => old l (fun k => re x k.val))
    (fun p => fresh p (fun k => re x k.val)) j
  have eq : (∏ j : Fin G.nV, tensor owner pkt old fresh j (fun i => x ((G.ports j).get i))) = ∏ j, V j := by
    symm; apply Fintype.prod_equiv v; intro j
    cases j with
    | inl l =>
      dsimp only [V,Sum.elim_inl]
      simp only [tensor,v,Equiv.symm_apply_apply]
      apply congrArg (old l); funext k; symm
      apply supplied_eq; left
      simp [G,network,v,k.property]
    | inr p =>
      dsimp only [V,Sum.elim_inr]
      simp only [tensor,v,Equiv.symm_apply_apply]
      apply congrArg (fresh p); funext k; symm
      apply supplied_eq; right
      simp [G,network,v,k.property]
  rw [eq,Fintype.prod_sum_type]
  rfl

/-- Degrees count actual incident edges, including parallel copies. -/
theorem degree [DecidableEq L] [DecidableEq P] (owner : E → L) (pkt : E → P) (j : L ⊕ P) :
    let G := network owner pkt
    G.deg (Fintype.equivFin _ j) =
      Fintype.card {e : E // (Sum.inl (owner e) : L ⊕ P)=j ∨ Sum.inr (pkt e)=j} := by
  classical
  intro G
  let v := Fintype.equivFin (L ⊕ P)
  let e := Fintype.equivFin E
  let l := G.ports (v j)
  have hn : l.Nodup := (List.nodup_finRange _).filter _
  have hm (a : Fin G.nE) : a ∈ l ↔ (Sum.inl (owner (e.symm a)) : L ⊕ P)=j ∨ Sum.inr (pkt (e.symm a))=j := by
    change a ∈ List.filter _ (List.finRange _) ↔ _
    rw [List.mem_filter]; simp [G,network,v,e]; exact fun _ => List.mem_finRange a
  let f : {a : Fin G.nE // a∈l} ≃ {a : E // (Sum.inl (owner a) : L ⊕ P)=j ∨ Sum.inr (pkt a)=j} :=
    { toFun := fun a => ⟨e.symm a.val,(hm _).mp a.property⟩
      invFun := fun a => ⟨e a.val,(hm _).mpr (by simpa using a.property)⟩
      left_inv := by intro a; exact Subtype.ext (e.apply_symm_apply a.val)
      right_inv := by intro a; exact Subtype.ext (e.symm_apply_apply a.val) }
  change l.length = _
  rw [← Nat.card_eq_fintype_card,← Nat.card_fin l.length]; exact Nat.card_congr ((List.Nodup.getEquiv l hn).trans f)

end DetDLP.ResidualChildGraph
end

section

namespace DetDLP.TerminalCoreCut
open Finset
variable (G : BipartiteMultigraph) (L : Finset (Fin G.nV))

def boundary (e : Fin G.nE) : Prop := (G.endpoints e).1∈L ∨ (G.endpoints e).2∈L
instance (e : Fin G.nE) : Decidable (boundary G L e) := inferInstanceAs (Decidable (_ ∨ _))
abbrev B := {e : Fin G.nE // boundary G L e}
abbrev I := {e : Fin G.nE // ¬boundary G L e}
abbrev V := {v : Fin G.nV // v∉L}

noncomputable def vertEquiv := Fintype.equivFin (V G L)
noncomputable def edgeEquiv := Fintype.equivFin (I G L)

def incident (v : Fin G.nV) (e : Fin G.nE) : Prop := (G.endpoints e).1=v ∨ (G.endpoints e).2=v
theorem atPort (v : Fin G.nV) (i : Fin (G.deg v)) : incident G v ((G.ports v).get i) := by
  simpa [BipartiteMultigraph.ports,incident] using List.get_mem (G.ports v) i

noncomputable def core : BipartiteMultigraph where
  nV := Fintype.card (V G L)
  nE := Fintype.card (I G L)
  endpoints j :=
    let e := (edgeEquiv G L).symm j
    (vertEquiv G L ⟨(G.endpoints e.val).1,fun h => e.property (Or.inl h)⟩,
     vertEquiv G L ⟨(G.endpoints e.val).2,fun h => e.property (Or.inr h)⟩)
  side v := G.side ((vertEquiv G L).symm v).val
  bipartite j := by simp; apply G.bipartite

theorem core_inc (v : V G L) (e : I G L) :
    incident (core G L) (vertEquiv G L v) (edgeEquiv G L e) ↔ incident G v.val e.val := by
  simp [incident,core,Subtype.ext_iff]

noncomputable def joinBits (η : B G L→Bool) (x : I G L→Bool) (e : Fin G.nE) : Bool :=
  if h : boundary G L e then η ⟨e,h⟩ else x ⟨e,h⟩

variable {R : Type} [CommRing R] (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→R)
def lookupTensor (η : B G L→Bool) (v : ↥L) : R := T v.val fun j =>
  let e := (G.ports v.val).get j
  η ⟨e,by
    rcases atPort G v.val j with h|h
    · exact Or.inl ((congrArg (fun v => v∈L) h).mpr v.property)
    · exact Or.inr ((congrArg (fun v => v∈L) h).mpr v.property)⟩

def lifted (η : B G L→Bool) (v : V G L) (read : I G L→Bool) : R :=
  T v.val fun j =>
    let e := (G.ports v.val).get j
    if h : boundary G L e then η ⟨e,h⟩ else read ⟨e,h⟩

noncomputable def coreTensor (η : B G L→Bool) (v : Fin (core G L).nV)
    (α : Fin ((core G L).deg v)→Bool) : R :=
  lifted G L T η ((vertEquiv G L).symm v) fun e =>
    ResidualChildGraph.supplied (core G L) v α (edgeEquiv G L e)

set_option backward.isDefEq.respectTransparency false in
theorem coreEntry (v : V G L) (η : B G L→Bool) (x : I G L→Bool) :
    coreTensor G L T η (vertEquiv G L v) (fun j =>
      x ((edgeEquiv G L).symm (((core G L).ports (vertEquiv G L v)).get j))) =
    T v.val (fun j => joinBits G L η x ((G.ports v.val).get j)) := by
  unfold coreTensor
  rw [(vertEquiv G L).symm_apply_apply v]
  unfold lifted
  apply congrArg (T v.val); funext j
  let e := (G.ports v.val).get j
  by_cases h : boundary G L e
  · dsimp only [e] at h; simp only [joinBits,dif_pos h]
  · dsimp only [e] at h; simp only [joinBits,dif_neg h]
    have d := (core_inc G L v ⟨e,h⟩).mpr (atPort G _ j)
    have mem : edgeEquiv G L ⟨e,h⟩∈(core G L).ports (vertEquiv G L v) := by
      simpa [BipartiteMultigraph.ports,incident] using d
    rw [ResidualChildGraph.supplied,dif_pos mem,List.idxOf_get,Equiv.symm_apply_apply]

theorem coreValue (η : B G L→Bool) :
    BTNContract (core G L) (coreTensor G L T η) =
      ∑ x : I G L→Bool,∏ v : V G L,T v.val (fun j => joinBits G L η x ((G.ports v.val).get j)) := by
  classical
  let e := edgeEquiv G L
  let re := e.arrowCongr (Equiv.refl Bool)
  unfold BTNContract; symm
  apply Fintype.sum_equiv re; intro x
  apply Fintype.prod_equiv (vertEquiv G L); intro v
  exact (coreEntry G L T v η x).symm

private theorem sameProduct {A : Type} (a b : Fintype A) (f g : A→R) (h : ∀ x,f x=g x) :
    (@univ A a).prod f=(@univ A b).prod g := by
  cases Subsingleton.elim a b
  exact prod_congr rfl fun x _ => h x

theorem cut :
    BTNContract G T = ∑ η : B G L→Bool,(∏ v : {v : Fin G.nV // v∈L},lookupTensor G L T η v)*
      BTNContract (core G L) (coreTensor G L T η) := by
  classical
  let W (x : Fin G.nE→Bool) (v : Fin G.nV) := T v (fun j => x ((G.ports v).get j))
  let e := Equiv.piEquivPiSubtypeProd (boundary G L) (fun _ => Bool)
  have eq (z : (B G L→Bool)×(I G L→Bool)) : e.symm z=joinBits G L z.1 z.2 := by
    funext j; by_cases h : boundary G L j <;> simp [e,Equiv.piEquivPiSubtypeProd,joinBits,h]
  change ∑ x,∏ v,W x v=_
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  apply sum_congr rfl; intro η _
  rw [coreValue,mul_sum]; apply sum_congr rfl; intro x _
  rw [eq]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : Fin G.nV => v∈L)]
  congr 1
  apply sameProduct; intro v
  unfold W lookupTensor; apply congrArg (T v.val); funext j
  have h : boundary G L ((G.ports v.val).get j) := by
    rcases atPort G v.val j with h|h
    · exact Or.inl ((congrArg (fun v => v∈L) h).mpr v.property)
    · exact Or.inr ((congrArg (fun v => v∈L) h).mpr v.property)
  simp [joinBits,h]
end DetDLP.TerminalCoreCut
end

section

namespace DetDLP.TerminalCoreGeometry
open TerminalCoreCut Finset
variable {G : BipartiteMultigraph} {m k S D : ℕ} (s : LookupSeparatorSpec G m k S D)
abbrev L := s.lookupVerts
abbrev terminal := ↥s.termSubdivVerts

def host (e : B G s.lookupVerts) : terminal s :=
  if h : (G.endpoints e.val).1∈s.lookupVerts then
    ⟨_,(s.lookup_edges_to_subdiv e.val).1 h⟩
  else ⟨_,(s.lookup_edges_to_subdiv e.val).2 (e.property.resolve_left h)⟩

def crosses (v : Fin G.nV) (e : Fin G.nE) : Prop :=
  ((G.endpoints e).1=v ∧ (G.endpoints e).2∈s.lookupVerts) ∨
  ((G.endpoints e).2=v ∧ (G.endpoints e).1∈s.lookupVerts)

theorem host_spec (e : B G s.lookupVerts) : crosses s (host s e).val e.val := by
  by_cases h : (G.endpoints e.val).1∈s.lookupVerts
  · exact Or.inr ⟨by simp [host,h],h⟩
  · exact Or.inl ⟨by simp [host,h],e.property.resolve_left h⟩

theorem host_unique {v : Fin G.nV} (hv : v∉s.lookupVerts) (e : B G s.lookupVerts) :
    incident G v e.val ↔ (host s e).val=v := by
  obtain ⟨a,b⟩|⟨a,b⟩ := host_spec s e
  · constructor
    · rintro (h|h)
      · exact a.symm.trans h
      · exact False.elim (hv (h ▸ b))
    · intro h; exact Or.inl (a.trans h)
  · constructor
    · rintro (h|h)
      · exact False.elim (hv (h ▸ b))
      · exact a.symm.trans h
    · intro h; exact Or.inr (a.trans h)

theorem uniqueEdge (v : terminal s) : ∃! e : Fin G.nE,crosses s v.val e := by
  simpa [crosses] using card_eq_one_iff_existsUnique.mp (s.subdiv_one_lookup_edge v.val v.property)

theorem host_bijective : Function.Bijective (host s) := by
  constructor
  · intro e e' h
    apply Subtype.ext
    obtain ⟨a,_,ha⟩ := uniqueEdge s (host s e)
    exact (ha _ (host_spec s e)).trans (ha _ (h ▸ host_spec s e')).symm
  · intro v
    obtain ⟨e,he,_⟩ := uniqueEdge s v
    have vb : v.val∉s.lookupVerts := fun H => Finset.disjoint_left.mp s.disjoint_verts H v.property
    obtain ⟨h,hl⟩|⟨h,hl⟩ := he
    · let b : B G s.lookupVerts := ⟨e,Or.inr hl⟩
      exact ⟨b,Subtype.ext ((host_unique s vb b).mp (Or.inl h))⟩
    · let b : B G s.lookupVerts := ⟨e,Or.inl hl⟩
      exact ⟨b,Subtype.ext ((host_unique s vb b).mp (Or.inr h))⟩

theorem boundary_card : Fintype.card (B G s.lookupVerts)=4*m*k := by
  rw [Fintype.card_congr (Equiv.ofBijective _ (host_bijective s))]
  exact (Fintype.card_coe _).trans s.card_termSubdiv

theorem core_edges : (core G s.lookupVerts).nE≤S := by
  change Fintype.card (I G s.lookupVerts)≤S
  rw [Fintype.card_subtype]
  simpa [boundary,not_or] using s.core_edges_le

theorem core_vertices : (core G s.lookupVerts).nV≤G.nV := by
  exact (Fintype.card_subtype_le (fun v : Fin G.nV => v∉s.lookupVerts)).trans_eq (Fintype.card_fin G.nV)

theorem ports_inj (H : BipartiteMultigraph) (v : Fin H.nV) :
    Function.Injective ((H.ports v).get) := by
  have hn : (H.ports v).Nodup := (List.nodup_finRange _).filter _
  exact hn.injective_get

theorem core_degrees (v : V G s.lookupVerts) :
    (core G s.lookupVerts).deg (vertEquiv G s.lookupVerts v)≤G.deg v.val := by
  let H := core G s.lookupVerts
  let w := vertEquiv G s.lookupVerts v
  let read (j : Fin (H.deg w)) := (edgeEquiv G s.lookupVerts).symm ((H.ports w).get j)
  have old (j : Fin (H.deg w)) : (read j).val∈G.ports v.val := by
    have h := atPort H w j
    have e := (core_inc G s.lookupVerts v (read j)).mp ((congrArg (incident H w) ((edgeEquiv G s.lookupVerts).apply_symm_apply ((H.ports w).get j))).mpr h)
    simpa [BipartiteMultigraph.ports,incident] using e
  let idx (j : Fin (H.deg w)) : Fin (G.deg v.val) :=
    ⟨(G.ports v.val).idxOf (read j).val,List.idxOf_lt_length_iff.mpr (old j)⟩
  have inj : Function.Injective idx := by
    intro a b h
    have eq := congrArg (G.ports v.val).get h
    change (G.ports v.val).get ⟨_,_⟩=(G.ports v.val).get ⟨_,_⟩ at eq
    simp only [idx,List.idxOf_get] at eq
    apply ports_inj H w
    apply (edgeEquiv G s.lookupVerts).symm.injective
    exact Subtype.ext eq
  simpa using Fintype.card_le_of_injective idx inj

theorem max_degree : (core G s.lookupVerts).maxDeg≤D := by
  apply Finset.sup_le; intro j _
  obtain ⟨v,rfl⟩ := (vertEquiv G s.lookupVerts).surjective j
  exact (core_degrees s v).trans (s.core_deg_le v.val v.property)
end DetDLP.TerminalCoreGeometry
end

section
namespace DetDLP.TerminalReattachment
open TerminalCoreCut Finset
variable {G : BipartiteMultigraph} {m k S D : ℕ} (s : LookupSeparatorSpec G m k S D)
abbrev Look := ↥s.lookupVerts
abbrev Ed := B G s.lookupVerts
def owner (e : Ed s) : Look s :=
  if h : (G.endpoints e.val).1∈s.lookupVerts then ⟨_,h⟩ else ⟨_,e.property.resolve_left h⟩

theorem uniqueOwner (v : Look s) (e : Ed s) : incident G v.val e.val ↔ owner s e=v := by
  have dis := Finset.disjoint_left.mp s.disjoint_verts v.property
  by_cases h : (G.endpoints e.val).1∈s.lookupVerts
  · have other := (s.lookup_edges_to_subdiv e.val).1 h
    simp only [owner,dif_pos h,incident,Subtype.ext_iff]
    exact or_iff_left (fun eq => dis (eq ▸ other))
  · simp only [owner,dif_neg h,incident,Subtype.ext_iff]
    exact or_iff_right (fun eq => h (eq ▸ v.property))

def originalEdge (v : Look s) (j : Fin (G.deg v.val)) : Ed s :=
  ⟨(G.ports v.val).get j,by
    rcases atPort G v.val j with h|h
    · exact Or.inl (h.symm ▸ v.property)
    · exact Or.inr (h.symm ▸ v.property)⟩

def localPort (v : Look s) : Fin (G.deg v.val) ≃ ResidualChildGraph.fiber (owner s) v where
  toFun i := ⟨originalEdge s v i,(uniqueOwner s v _).mp (atPort G v.val i)⟩
  invFun e := ⟨(G.ports v.val).idxOf e.val.val,List.idxOf_lt_length_iff.mpr (by
    have inc := (uniqueOwner s v e.val).mpr e.property
    simpa [BipartiteMultigraph.ports,incident] using inc)⟩
  left_inv i := by apply TerminalCoreGeometry.ports_inj G v.val; exact List.idxOf_get _
  right_inv e := by apply Subtype.ext; apply Subtype.ext; exact List.idxOf_get _

variable {n : ℕ} (atLeaf : Ed s→Fin n)
noncomputable abbrev graph := ResidualChildGraph.network (owner s) atLeaf
noncomputable def vertex : Look s ⊕ Fin n ≃ Fin (graph s atLeaf).nV := Fintype.equivFin _
theorem leftDeg (v : Look s) : (graph s atLeaf).deg (vertex s atLeaf (.inl v))=k := by
  have hd := ResidualChildGraph.degree (owner s) atLeaf (.inl v)
  have eq : Fintype.card (ResidualChildGraph.fiber (owner s) v)=G.deg v.val := by
    simpa using (Fintype.card_congr (localPort s v)).symm
  change (ResidualChildGraph.network (owner s) atLeaf).deg (Fintype.equivFin _ (.inl v))=k
  rw [hd]; simpa only [Sum.inl.injEq,Sum.inr_ne_inl,or_false] using eq.trans (s.lookup_deg v.val v.property)

theorem rightDeg (j : Fin n) :
    (graph s atLeaf).deg (vertex s atLeaf (.inr j))=Fintype.card (ResidualChildGraph.fiber atLeaf j) := by
  change (ResidualChildGraph.network (owner s) atLeaf).deg (Fintype.equivFin _ (.inr j))=_
  rw [ResidualChildGraph.degree]; simp only [Sum.inl_ne_inr,Sum.inr.injEq,false_or]

theorem maximum (upper : ℕ) (cap : ∀ j,Fintype.card (ResidualChildGraph.fiber atLeaf j)≤upper) :
    (graph s atLeaf).maxDeg ≤ max k upper := by
  apply Finset.sup_le; intro w _
  obtain ⟨v,rfl⟩ := (vertex s atLeaf).surjective w
  cases v with
  | inl v => rw [leftDeg]; exact le_max_left .. 
  | inr j => rw [rightDeg]; exact (cap j).trans (le_max_right ..)

theorem attach (R : Type) [CommRing R]
    (T : (v : Look s)→(Fin (G.deg v.val)→Bool)→R)
    (F : (j : Fin n)→(ResidualChildGraph.fiber atLeaf j→Bool)→R) :
    ∃ A : (v : Fin (graph s atLeaf).nV)→(Fin ((graph s atLeaf).deg v)→Bool)→R,
    BTNContract (graph s atLeaf) A =
      ∑ x : Ed s→Bool,(∏ v,T v (fun j => x (originalEdge s v j)))*
        ∏ j,F j (fun e => x e.val) := by
  let old (v : Look s) (bits : ResidualChildGraph.fiber (owner s) v→Bool) :=
    T v (fun j => bits (localPort s v j))
  exact ⟨_,ResidualChildGraph.contract (owner s) atLeaf old F⟩
end DetDLP.TerminalReattachment
end

open DetDLP Finset

theorem solution {G : BipartiteMultigraph} {m k S D n : ℕ} (s : LookupSeparatorSpec G m k S D) :
    let B := {e : Fin G.nE // (G.endpoints e).1∈s.lookupVerts ∨ (G.endpoints e).2∈s.lookupVerts}
    ∀ (leaf : B→Fin n) (U : ℕ), (∀ j,Fintype.card {e : B // leaf e=j}≤U) →
    ∃ (H : BipartiteMultigraph) (vertices : (↥s.lookupVerts ⊕ Fin n) ≃ Fin H.nV)
      (boundaryPort : (v : ↥s.lookupVerts)→Fin (G.deg v.val)→B),
      H.nE=4*m*k ∧ H.nV=4*m+n ∧ H.maxDeg ≤ max k U ∧
      (∀ v,H.deg (vertices (.inl v))=k) ∧
      (∀ j,H.deg (vertices (.inr j))=Fintype.card {e : B // leaf e=j}) ∧
      (∀ v i,(boundaryPort v i).val=(G.ports v.val).get i) ∧
      ∀ (R : Type) [CommRing R] (T : (v : ↥s.lookupVerts)→(Fin (G.deg v.val)→Bool)→R)
        (F : (j : Fin n)→({e : B // leaf e=j}→Bool)→R),
      ∃ A : (v : Fin H.nV)→(Fin (H.deg v)→Bool)→R, BTNContract H A =
        ∑ x : B→Bool,(∏ v,T v (fun i => x (boundaryPort v i)))*
          ∏ j,F j (fun e => x e.val) := by
  intro B leaf U cap
  refine ⟨TerminalReattachment.graph s leaf,TerminalReattachment.vertex s leaf,
    TerminalReattachment.originalEdge s,TerminalCoreGeometry.boundary_card s,?_,
    TerminalReattachment.maximum s leaf U cap,TerminalReattachment.leftDeg s leaf,
    TerminalReattachment.rightDeg s leaf,fun _ _ => rfl,TerminalReattachment.attach s leaf⟩
  change Fintype.card (↥s.lookupVerts ⊕ Fin n)=4*m+n
  simp [s.card_lookup]
