-- Prove2me | solution 1 for DetDLP.d4_core_cut_poly_and_spec
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T09:08:48.810436+00:00
-- url     : https://prove2.me/submissions/203d24a0-b415-4f18-91c2-3251279c7902

import Definitions.Def_DetDLP_D4CoreCut
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_DetDLP_lookup_separator_core_contraction
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace DetDLP.D4CoreCut.Check
open Groundwork Groundwork.PolyT Raw DetDLP_W1_Queries
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst
  Groundwork.PolyT.snd Groundwork.PolyT.prodMk Groundwork.PolyT.flatMap Groundwork.PolyT.filter
  Groundwork.PolyT.map Groundwork.PolyT.length Groundwork.PolyT.idxOf
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
  first_poly more_poly frame_poly w5_M6Sort.cw_poly w5_M6Sort.encode_poly
variable {α β : Type} [Enc α] [Enc β]
@[local fun_prop] theorem fieldP (k : ℕ) {w : α → Word} (hw : PolyT w) : PolyT (fun x => field k (w x)) := by
  induction k generalizing w with
  | zero => exact first_poly hw
  | succ k ih => exact ih (more_poly hw)
@[local fun_prop] theorem rangeP {w : α → List β} (hw : PolyT w) : PolyT (fun x => List.range (w x).length) := Groundwork.PolyT.range (Unary.of_length hw)
@[local fun_prop] theorem decP {w : α → Word} (hw : PolyT w) : PolyT (fun x => w5_M6Sort.decode (w x)) := w5_M6Sort.decode_poly.comp hw
@[local fun_prop] theorem packP {w : α → List Word} (hw : PolyT w) : PolyT (fun x => pack (w x)) := by unfold pack; fun_prop
@[local fun_prop] theorem wordP {w : α → Word} {e : α → List ℕ} {n : α → ℕ} (hw : PolyT w) (he : PolyT e) (hn : PolyT n) : PolyT (fun x => graphWord (w x) (e x) (n x)) := by unfold graphWord; fun_prop
@[local fun_prop] theorem endsP {w : α → Word} (hw : PolyT w) : PolyT (fun x => ends (w x)) := by unfold ends; fun_prop
@[local fun_prop] theorem sidesP {w : α → Word} (hw : PolyT w) : PolyT (fun x => sides (w x)) := by unfold sides; fun_prop
@[local fun_prop] theorem maskP {w : α → Word} (hw : PolyT w) : PolyT (fun x => mask (w x)) := by unfold mask; fun_prop
@[local fun_prop] theorem doubleP {f : α → ℕ} (hf : PolyT f) : PolyT (fun x => 2 * f x) := by simp only [two_mul]; fun_prop
@[local fun_prop] theorem lhsP {w : α → Word} {e : α → ℕ} (hw : PolyT w) (he : PolyT e) : PolyT (fun x => lhs (w x) (e x)) := by unfold lhs; fun_prop
@[local fun_prop] theorem rhsP {w : α → Word} {e : α → ℕ} (hw : PolyT w) (he : PolyT e) : PolyT (fun x => rhs (w x) (e x)) := by unfold rhs; fun_prop
@[local fun_prop] theorem verticesP {w : α → Word} {b : α → Bool} (hw : PolyT w) (hb : PolyT b) : PolyT (fun x => vertices (w x) (b x)) := by unfold vertices; fun_prop
@[local fun_prop] theorem edgesP {w : α → Word} (hw : PolyT w) : PolyT (fun x => edges (w x)) := by unfold edges; fun_prop
@[local fun_prop] theorem boundaryP {w : α → Word} {e : α → ℕ} (hw : PolyT w) (he : PolyT e) : PolyT (fun x => boundary (w x) (e x)) := by unfold boundary; fun_prop
@[local fun_prop] theorem selP {w : α → Word} {b : α → Bool} (hw : PolyT w) (hb : PolyT b) : PolyT (fun x => selected (w x) (b x)) := by unfold selected; fun_prop
@[local fun_prop] theorem otherP {w : α → Word} {e : α → ℕ} (hw : PolyT w) (he : PolyT e) : PolyT (fun x => other (w x) (e x)) := by unfold other; fun_prop
@[local fun_prop] theorem lookP {w : α → Word} {e : α → ℕ} (hw : PolyT w) (he : PolyT e) : PolyT (fun x => lookup (w x) (e x)) := by unfold lookup; fun_prop
@[local fun_prop] theorem portsP {w : α → Word} {es : α → List ℕ} {v : α → ℕ} (hw : PolyT w) (he : PolyT es) (hv : PolyT v) : PolyT (fun x => ports (w x) (es x) (v x)) := by unfold ports; fun_prop
@[local fun_prop] theorem tableP {w : α → Word} {v : α → ℕ} (hw : PolyT w) (hv : PolyT v) : PolyT (fun x => portTable (w x) (v x)) := by unfold portTable; fun_prop

theorem rawReattachPoly : PolyT reattachRaw := by unfold reattachRaw Raw.residual; dsimp only; fun_prop
@[local fun_prop] theorem pinP {h : α → List ℕ} {v : α → ℕ} (hh : PolyT h) (hv : PolyT v) : PolyT (fun x => if v x ∈ h x then (h x).idxOf (v x) + 1 else 0) := by
  simp only [← List.idxOf_lt_length_iff]
  fun_prop
theorem rawCutPoly : PolyT cutCoreRaw := by unfold cutCoreRaw Raw.cut; dsimp only; fun_prop
end DetDLP.D4CoreCut.Check
set_option autoImplicit false
namespace DetDLP.D4CoreCut.Check
open Raw OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP_W1_Queries
variable {C c : ℕ} (x : D4Plan.Input C c)
abbrev w := D4Plan.input x
abbrev L := x.spec.lookupVerts
@[simp] theorem pack_ok (ws : List Word) : pack ws = Encoding.encodeList id ws := by
  induction ws with
  | nil => rfl
  | cons a l ih => simpa [pack,Encoding.encodeList,List.flatMap,List.append_assoc] using congrArg (fun z => true :: (Encoding.frame a ++ z)) ih
@[simp] theorem sides_ok : sides (w x) = List.ofFn x.G.side := by simp [sides,w,D4Plan.input,encodeTerminalBTNInstance,BipartiteMultigraph.encode,field]
@[simp] theorem mask_ok : mask (w x) = List.ofFn fun v => decide (v ∈ L x) := by simp [mask,w,D4Plan.input,encodeTerminalBTNInstance,field,L]
@[simp] theorem ends_ok : ends (w x) = (List.finRange x.G.nE).flatMap (fun e => [(x.G.endpoints e).1.val,(x.G.endpoints e).2.val]) := by simp [ends,w,D4Plan.input,encodeTerminalBTNInstance,BipartiteMultigraph.encode,field]
@[simp] theorem flat_len {α : Type} (a b : α → ℕ) (xs : List α) : (xs.flatMap (fun i => [a i,b i])).length = 2 * xs.length := by induction xs <;> simp_all [List.flatMap, Nat.mul_succ]
theorem flat_get {α : Type} (a b : α → ℕ) (xs : List α) (j : Fin xs.length) :
  (xs.flatMap (fun i => [a i,b i])).getD (2*j.val) 0 = a (xs.get j) ∧
  (xs.flatMap (fun i => [a i,b i])).getD (2*j.val+1) 0 = b (xs.get j) := by
  induction xs with
  | nil => exact Fin.elim0 j
  | cons z zs ih =>
    refine Fin.cases ?_ (fun t => ?_) j
    · exact ⟨rfl,rfl⟩
    · change (a z :: b z :: zs.flatMap (fun i => [a i,b i])).getD (2*(t.val+1)) 0 = a (zs.get t) ∧ (a z :: b z :: zs.flatMap (fun i => [a i,b i])).getD (2*(t.val+1)+1) 0 = b (zs.get t)
      simpa only [Fin.val_succ,Nat.mul_succ,List.flatMap_cons,List.cons_append,List.nil_append,List.get_cons_succ,List.getD_cons_succ] using ih t
@[simp] theorem lhs_ok (e : Fin x.G.nE) : lhs (w x) e.val = (x.G.endpoints e).1.val := by
  unfold lhs; rw [ends_ok]; simpa using (flat_get (fun e => (x.G.endpoints e).1.val) (fun e => (x.G.endpoints e).2.val) (List.finRange x.G.nE) ⟨e.val,by simpa using e.isLt⟩).1
@[simp] theorem rhs_ok (e : Fin x.G.nE) : rhs (w x) e.val = (x.G.endpoints e).2.val := by
  unfold rhs; rw [ends_ok]; simpa using (flat_get (fun e => (x.G.endpoints e).1.val) (fun e => (x.G.endpoints e).2.val) (List.finRange x.G.nE) ⟨e.val,by simpa using e.isLt⟩).2
@[simp] theorem vals_range (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by apply List.ext_getElem <;> simp
@[simp] theorem idx_map {n : ℕ} (vs : List (Fin n)) (v : Fin n) : (vs.map Fin.val).idxOf v.val = vs.idxOf v := by
  induction vs with
  | nil => rfl
  | cons a l ih => by_cases h : a = v
                   · subst a; simp [List.idxOf_cons]
                   · have hn := Fin.val_ne_of_ne h; simp [List.idxOf_cons,h,hn,ih]
@[simp] theorem getD_fn {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) : (List.ofFn f).getD i.val d = f i := by rw [List.getD_eq_getElem _ _ (by simp)]; simp
@[simp] theorem getD_vals {n : ℕ} (l : List (Fin n)) (j : Fin l.length) : (l.map Fin.val).getD j.val 0 = (l.get j).val := by rw [List.getD_eq_getElem _ _ (by simp)]; simp
@[simp] theorem vertsT : vertices (w x) true = (lookupVerts x.G (L x)).map Fin.val := by
  unfold vertices lookupVerts; rw [sides_ok,List.length_ofFn,← vals_range,List.filter_map]; congr 1; apply List.filter_congr; intro v _; simp [Function.comp_def]
@[simp] theorem vertsF : vertices (w x) false = (coreVerts x.G (L x)).map Fin.val := by
  unfold vertices coreVerts; rw [sides_ok,List.length_ofFn,← vals_range,List.filter_map]; congr 1; apply List.filter_congr; intro v _; simp [Function.comp_def]
theorem range_clip (n k : ℕ) : (List.range (n+k)).filter (fun e => decide (2*e+1 < 2*n)) = List.range n := by
  induction k with
  | zero => simp only [Nat.add_zero]; apply List.filter_eq_self.mpr; intro i hi; have := List.mem_range.mp hi; simp; omega
  | succ k ih => rw [← Nat.add_assoc,List.range_succ,List.filter_append,ih]; simp [show ¬2*(n+k)+1<2*n by omega]
@[simp] theorem edges_ok : edges (w x) = (List.finRange x.G.nE).map Fin.val := by
  unfold edges; rw [ends_ok,flat_len,List.length_finRange,vals_range]; simpa only [two_mul] using range_clip x.G.nE x.G.nE
@[simp] theorem bound_ok (e : Fin x.G.nE) : Raw.boundary (w x) e.val = decide ((x.G.endpoints e).1 ∈ L x ∨ (x.G.endpoints e).2 ∈ L x) := by simp [Raw.boundary]
@[simp] theorem selT : selected (w x) true = (boundaryEdges x.G (L x)).map Fin.val := by
  unfold selected boundaryEdges; rw [edges_ok,List.filter_map]; congr 1; apply List.filter_congr; intro e _; simp [Function.comp_def]
@[simp] theorem selF : selected (w x) false = (coreEdges x.G (L x)).map Fin.val := by
  unfold selected coreEdges; rw [edges_ok,List.filter_map]; congr 1; apply List.filter_congr; intro e _; simp [Function.comp_def]
@[simp] theorem owner_ok (i : B x.G (L x)) : ((lookupVerts x.G (L x)).map Fin.val).idxOf (lookup (w x) (origB x.G (L x) i).val) = (lookupIdx x.G (L x) i).val := by
  unfold lookup lookupIdx; by_cases h : (x.G.endpoints (origB x.G (L x) i)).1 ∈ L x <;> simp [h,idx]
theorem sidesR (n : ℕ) (leaf : B x.G (L x) → Fin n) : List.ofFn (reattach x.G (L x) n leaf).side = List.replicate (L x).card false ++ List.replicate n true := by
  change List.ofFn (fun i : Fin ((L x).card+n) => decide ((L x).card ≤ i.val)) = _
  rw [List.ofFn_add]; simp [List.ofFn_const]; simp_rw [show ∀ i : Fin (L x).card, decide ((L x).card ≤ i.val) = false by intro i; simp [i.isLt]]; apply List.ofFn_const

theorem reattach_ok (n : ℕ) (leaf : B x.G (L x) → Fin n) :
  reattachRaw (reattachInput (w x) n (List.ofFn (fun i => (leaf i).val))) = (reattach x.G (L x) n leaf).encode := by
  unfold reattachInput reattachRaw Raw.residual
  simp only [field,first_cons,more_cons,id_eq,w5_M6Sort.decode_encode,vertsT,selT,List.length_map,lookup_length,List.map_const',List.length_replicate]
  unfold graphWord BipartiteMultigraph.encode
  rw [pack_ok,sidesR]
  simp only [List.length_append,List.length_replicate]
  congr 3
  rw [← vals_range,List.flatMap_map]; congr 1; apply congrArg (fun z => [encodeNatListBin z]); congr 1; funext i
  simp only [getD_fn,getD_vals]; exact congrArg (fun a => [a,(L x).card + (leaf i).val]) (owner_ok x i)
end DetDLP.D4CoreCut.Check
set_option autoImplicit false
namespace DetDLP.D4CoreCut.Geom
open Finset
variable (G : Graph) (L : Finset (Fin G.nV))
def IsB (e : Fin G.nE) := (G.endpoints e).1 ∈ L ∨ (G.endpoints e).2 ∈ L
instance (e : Fin G.nE) : Decidable (IsB G L e) := inferInstanceAs (Decidable (_ ∨ _))
def cutEquiv : B G L ≃ {e : Fin G.nE // IsB G L e} :=
  ((List.nodup_finRange _).filter _ |>.getEquiv (boundaryEdges G L)).trans
    (Equiv.subtypeEquivRight (fun e => by simp [boundaryEdges,IsB]))
def lookEquiv : Fin L.card ≃ ↥L :=
  (finCongr (lookup_length G L).symm).trans <|
    ((List.nodup_finRange _).filter _ |>.getEquiv (lookupVerts G L)).trans
      (Equiv.subtypeEquivRight (fun e => by simp [lookupVerts]))
theorem cut_card {m k S D : ℕ} (s : LookupSeparatorSpec G m k S D) : (boundaryEdges G s.lookupVerts).length = 4*m*k := by
  obtain ⟨_,_,_,_,_,_,_,hc,_⟩ := lookup_separator_core_contraction s
  exact (Fintype.card_fin _).symm.trans ((Fintype.card_congr (cutEquiv G s.lookupVerts)).trans hc)

def incident (v : Fin G.nV) (e : Fin G.nE) := (G.endpoints e).1=v ∨ (G.endpoints e).2=v
instance (v : Fin G.nV) (e : Fin G.nE) : Decidable (incident G v e) := inferInstanceAs (Decidable (_ ∨ _))
def portEq (v : Fin G.nV) : Fin (G.deg v) ≃ {e : Fin G.nE // incident G v e} :=
  ((List.nodup_finRange _).filter _ |>.getEquiv (G.ports v)).trans (Equiv.subtypeEquivRight (fun e => by simp [BipartiteMultigraph.ports,incident]))

theorem owner_val (e : B G L) : (lookEquiv G L (lookupIdx G L e)).val = if (G.endpoints (origB G L e)).1∈L then (G.endpoints (origB G L e)).1 else (G.endpoints (origB G L e)).2 := by
  change (lookupVerts G L).get ⟨_,_⟩ = _; apply List.idxOf_get

theorem owner_inc (h : Independent G L) (v : Fin L.card) (e : B G L) : incident G (lookEquiv G L v).val (origB G L e) ↔ lookupIdx G L e = v := by
  rw [← (lookEquiv G L).injective.eq_iff,Subtype.ext_iff,owner_val]
  have hv := (lookEquiv G L v).property
  by_cases ha : (G.endpoints (origB G L e)).1 ∈ L
  · rw [if_pos ha]; exact or_iff_left (fun he => h _ ha (he ▸ hv))
  · rw [if_neg ha]; exact or_iff_right (fun he => ha (he ▸ hv))

def ownerFiber (h : Independent G L) (v : Fin L.card) : Fin (G.deg (lookEquiv G L v).val) ≃ {e : B G L // lookupIdx G L e=v} :=
  (portEq G _).trans {
    toFun a := by
      have hv := (lookEquiv G L v).property
      have hb : IsB G L a.val := by
        rcases a.property with he|he
        · exact Or.inl (he.symm ▸ hv)
        · exact Or.inr (he.symm ▸ hv)
      let i := (cutEquiv G L).symm ⟨a.val,hb⟩
      have hi : origB G L i = a.val := congrArg Subtype.val ((cutEquiv G L).apply_symm_apply ⟨a.val,hb⟩)
      exact ⟨i,(owner_inc G L h v i).mp (hi ▸ a.property)⟩
    invFun i := ⟨origB G L i.val,(owner_inc G L h v i.val).mpr i.property⟩
    left_inv a := by
      apply Subtype.ext
      exact congrArg (fun z : {e : Fin G.nE // IsB G L e} => z.val) ((cutEquiv G L).apply_symm_apply _)
    right_inv i := Subtype.ext ((cutEquiv G L).symm_apply_apply i.val) }

def fiberPort {n : ℕ} (leaf : B G L → Fin n) (v : Fin (L.card+n)) (p : B G L → Prop) (ok : ∀ e, incident (reattach G L n leaf) v e ↔ p e) :
  Fin ((reattach G L n leaf).deg v) ≃ {e : B G L // p e} := (portEq (reattach G L n leaf) v).trans (Equiv.subtypeEquivRight ok)

def leftP {n : ℕ} (leaf : B G L → Fin n) (v : Fin L.card) := fiberPort G L leaf (v.castAdd n) (fun e => lookupIdx G L e=v) (by
  intro e; change (Fin.castAdd n _ = Fin.castAdd n v ∨ Fin.natAdd L.card (leaf e) = Fin.castAdd n v) ↔ _
  simp [Fin.ext_iff]; omega)
def rightP {n : ℕ} (leaf : B G L → Fin n) (v : Fin n) := fiberPort G L leaf (Fin.natAdd L.card v) (fun e => leaf e=v) (by
  intro e; change (Fin.castAdd n (lookupIdx G L e) = Fin.natAdd L.card v ∨ Fin.natAdd L.card (leaf e) = Fin.natAdd L.card v) ↔ _
  simp [Fin.ext_iff]; have := (lookupIdx G L e).isLt; omega)

variable {m k S D : ℕ} (s : LookupSeparatorSpec G m k S D) {n : ℕ} (leaf : B G s.lookupVerts → Fin n)
local notation "K" => s.lookupVerts
local notation "H" => reattach G K n leaf
abbrev lp (v : Fin (K).card) := (ownerFiber G K (independent_of_spec G s) v).trans (leftP G K leaf v).symm

theorem degree_bound (U : ℕ) (cap : ∀ j,Fintype.card {e : B G K // leaf e=j} ≤ U) : (H).maxDeg ≤ max k U := by
  apply Finset.sup_le; intro v _
  refine Fin.addCases (motive := fun v => (H).deg v ≤ max k U) (fun i => ?_) (fun j => ?_) v
  · have h := (Fintype.card_congr (lp G s leaf i)).symm
    simp only [Fintype.card_fin] at h; rw [h,s.lookup_deg _ (lookEquiv G K i).property]; exact le_max_left ..
  · have h := Fintype.card_congr (rightP G K leaf j); rw [Fintype.card_fin] at h; exact (h.le.trans (cap j)).trans (le_max_right ..)

end DetDLP.D4CoreCut.Geom
set_option autoImplicit false
namespace DetDLP.M14ActualCore
open D4CoreCut Finset
/-- Provide the entry tensor with exactly the bits at its incident ports. -/
def supplied (G : BipartiteMultigraph) (v : Fin G.nV) (α : Fin (G.deg v) → Bool) (e : Fin G.nE) : Bool :=
  if h : e ∈ G.ports v then α ⟨(G.ports v).idxOf e,List.idxOf_lt_length_iff.mpr h⟩ else false
variable (G : BipartiteMultigraph) (L : Finset (Fin G.nV))
def boundary (e : Fin G.nE) : Prop := (G.endpoints e).1∈L ∨ (G.endpoints e).2∈L
instance (e : Fin G.nE) : Decidable (boundary G L e) := inferInstanceAs (Decidable (_ ∨ _))
abbrev B := {e : Fin G.nE // boundary G L e}
abbrev I := {e : Fin G.nE // ¬boundary G L e}
abbrev V := {v : Fin G.nV // v∉L}
private def vBack : D4CoreCut.V G L ≃ V G L :=
  ((List.nodup_finRange _).filter _ |>.getEquiv (coreVerts G L)).trans (Equiv.subtypeEquivRight (fun v => by simp [coreVerts]))
private def eBack : D4CoreCut.E G L ≃ I G L :=
  ((List.nodup_finRange _).filter _ |>.getEquiv (coreEdges G L)).trans (Equiv.subtypeEquivRight (fun e => by simp [coreEdges,boundary,not_or]))
abbrev core := coreGraph G L
private abbrev vertEquiv := (vBack G L).symm
private abbrev edgeEquiv := (eBack G L).symm
def incident (v : Fin G.nV) (e : Fin G.nE) : Prop := (G.endpoints e).1=v ∨ (G.endpoints e).2=v
theorem atPort (v : Fin G.nV) (i : Fin (G.deg v)) : incident G v ((G.ports v).get i) := by
  simpa [BipartiteMultigraph.ports,incident] using List.get_mem (G.ports v) i

theorem core_inc (v : V G L) (e : I G L) : incident (core G L) (vertEquiv G L v) (edgeEquiv G L e) ↔ incident G v.val e.val := by
  have hv : origV G L (vertEquiv G L v) = v.val := congrArg Subtype.val ((vBack G L).apply_symm_apply v)
  have he : origE G L (edgeEquiv G L e) = e.val := congrArg Subtype.val ((eBack G L).apply_symm_apply e)
  have inj : Function.Injective (origV G L) := ((List.nodup_finRange _).filter _).injective_get
  unfold incident; simp only [core,coreGraph]; constructor
  · intro hz; exact hz.imp (fun hh => by simpa [hv,he] using congrArg (origV G L) hh) (fun hh => by simpa [hv,he] using congrArg (origV G L) hh)
  · intro hz; exact hz.imp (fun hh => inj (by simpa [hv,he] using hh)) (fun hh => inj (by simpa [hv,he] using hh))
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
    supplied (core G L) v α (edgeEquiv G L e)

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
    rw [supplied,dif_pos mem,List.idxOf_get,Equiv.symm_apply_apply]

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
end DetDLP.M14ActualCore
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.D4CoreCut.CG
open Finset
variable {G : Graph} {m k S D : ℕ} (s : LookupSeparatorSpec G m k S D)
local notation "K" => s.lookupVerts
local notation "H" => coreGraph G K
local notation "h" => independent_of_spec G s

theorem countE : (H).nE ≤ S := by
  have hn : (coreEdges G K).Nodup := (List.nodup_finRange _).filter _
  change (coreEdges G K).length ≤ S
  rw [← List.toFinset_card_of_nodup hn]
  convert s.core_edges_le using 2; ext; simp [coreEdges]
theorem countV : (H).nV ≤ G.nV := (List.length_filter_le ..).trans_eq List.length_finRange
theorem maxDegree : (H).maxDeg ≤ D := by
  apply Finset.sup_le; intro v _
  have inj : Function.Injective (portIncl G K v) := by
    intro i j eq
    have eq' := congrArg (G.ports (origV G K v)).get eq
    simp only [portIncl,idx,List.idxOf_get] at eq'
    exact ((List.nodup_finRange _).filter _).injective_get (((List.nodup_finRange _).filter _).injective_get eq')
  have bound := Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fin] at bound
  exact bound.trans (s.core_deg_le _ (by simpa [coreVerts,origV] using of_decide_eq_true (List.mem_filter.mp ((coreVerts G K).get_mem v)).2))

def crosses (v : Fin G.nV) (e : Fin G.nE) := ( (G.endpoints e).1=v ∧ (G.endpoints e).2∈K) ∨ ((G.endpoints e).2=v ∧ (G.endpoints e).1∈K)
theorem host_cross (e : B G K) : crosses s (origV G K (host₀ G K h e)) (origB G K e) := by
  have hb := boundary_ok G K e
  by_cases ha : (G.endpoints (origB G K e)).1 ∈ K <;> simp [crosses,host₀,ha] <;> tauto
theorem host_sub (e : B G K) : origV G K (host₀ G K h e) ∈ s.termSubdivVerts := by
  have hb := boundary_ok G K e
  by_cases ha : (G.endpoints (origB G K e)).1 ∈ K
  · simpa [host₀,ha] using (s.lookup_edges_to_subdiv _).1 ha
  · simpa [host₀,ha] using (s.lookup_edges_to_subdiv _).2 (hb.resolve_left ha)
theorem host_inj : Function.Injective (host₀ G K h) := by
  intro a b eq
  have hv := host_sub s a
  obtain ⟨e,_,he⟩ := Finset.card_eq_one_iff_existsUnique.mp (s.subdiv_one_lookup_edge _ hv)
  have h₁ := host_cross s a
  have h₂ := host_cross s b
  rw [← eq] at h₂
  apply ((List.nodup_finRange _).filter _).injective_get (l:=boundaryEdges G K)
  exact (he _ (by simpa [crosses,origB] using h₁)).trans (he _ (by simpa [crosses,origB] using h₂)).symm

theorem tau (z : B G K) : (univ.filter fun y => host₀ G K h z = host₀ G K h y).card ≤ 1 := by
  apply Finset.card_le_one.mpr; intro a ha b hb
  exact host_inj s ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2)
end DetDLP.D4CoreCut.CG
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.D4CoreCut.Check
open Raw OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
variable {C c : ℕ} (x : D4Plan.Input C c)
local notation "G" => x.G
local notation "K" => L x
local notation "H" => coreGraph G K
local notation "h" => independent_of_spec G x.spec
local notation "bs" => boundaryEdges G K
local notation "vs" => coreVerts G K
local notation "es" => coreEdges G K

theorem byIndex {α β : Type} (l : List α) (f : α → β) : l.map f = List.ofFn (fun i => f (l.get i)) := by simpa using (List.map_ofFn (f:=l.get) (g:=f))
theorem byIndexFlat {α β : Type} (l : List α) (f : α → List β) : l.flatMap f = (List.finRange l.length).flatMap (fun i => f (l.get i)) := by simpa using List.flatMap_map l.get f (List.finRange l.length)
theorem byIndexFilter {α : Type} (l : List α) (p : α → Bool) : l.filter p = ((List.finRange l.length).filter (fun i => p (l.get i))).map l.get := by simpa only [List.map_get_finRange,Function.comp_def] using (List.filter_map (p:=p) (f:=l.get) (l:=List.finRange l.length))

theorem orig_ok : vertices (w x) false = List.ofFn (fun v : V G K => (origV G K v).val) := by rw [vertsF]; exact byIndex _ _
theorem hosts_ok : (selected (w x) true).map (fun e => (vertices (w x) false).idxOf (other (w x) e)) = List.ofFn (fun i => (host₀ G K h i).val) := by
  rw [selT,vertsF,List.map_map,byIndex]; congr 1; funext i
  dsimp only [Function.comp_apply]; change (List.map Fin.val vs).idxOf (other (w x) (origB G K i).val) = _
  by_cases ha : ((G).endpoints (origB G K i)).1∈K <;> simp [host₀,other,ha,vidx,idx]
theorem graph_ok : graphWord ((vertices (w x) false).map (fun v => (sides (w x)).getD v false))
    ((selected (w x) false).flatMap fun e => [(vertices (w x) false).idxOf (lhs (w x) e),(vertices (w x) false).idxOf (rhs (w x) e)]) (selected (w x) false).length = (H).encode := by
  rw [vertsF,selF,List.flatMap_map,List.map_map,List.length_map,byIndexFlat,byIndex]
  unfold graphWord BipartiteMultigraph.encode; rw [pack_ok]; simp only [List.length_ofFn,Function.comp_apply,sides_ok,getD_fn,lhs_ok,rhs_ok,idx_map]; rfl

theorem pins_fn {d t : ℕ} (host : Fin d → Fin t) (v : Fin t) :
  (if v.val ∈ List.ofFn (fun j => (host j).val) then (List.ofFn (fun j => (host j).val)).idxOf v.val + 1 else 0) =
    ((((List.finRange d).find? (fun i => host i == v)).map (fun i => i.val+1)).getD 0) := by
  let p := fun i : Fin d => host i == v
  let l := List.ofFn (fun j => (host j).val)
  have hi : l.idxOf v.val = (List.finRange d).findIdx p := by
    change (List.ofFn _).findIdx _ = _; rw [List.ofFn_eq_map,List.findIdx_map]; congr 1; funext i; simp [Function.comp_def,p,beq_eq_decide,Fin.ext_iff]
  change (if v.val ∈ l then l.idxOf v.val + 1 else 0) = (((List.find? p _).map _).getD 0)
  rw [List.find?_eq_getElem?_findIdx,← hi]
  by_cases hv : v.val ∈ l
  · have lt : l.idxOf v.val < d := by simpa [l] using List.idxOf_lt_length_iff.mpr hv
    rw [if_pos hv,List.getElem?_eq_getElem (by simpa using lt)]; simp
  · rw [if_neg hv,List.idxOf_of_notMem hv]; simp [l]

theorem pins_ok : (List.range (vertices (w x) false).length).map (fun v => if v ∈ List.ofFn (fun i => (host₀ G K h i).val) then (List.ofFn (fun i => (host₀ G K h i).val)).idxOf v + 1 else 0) = List.ofFn (fun v => ((pinEdge G K h v).map (fun i => i.val+1)).getD 0) := by
  rw [vertsF,List.length_map,← vals_range,List.map_map,← List.ofFn_eq_map]; congr 1; funext v; exact pins_fn _ _

theorem incident_iff (v : V G K) (i : E G K) : ((H).endpoints i).1=v ∨ ((H).endpoints i).2=v ↔ ((G).endpoints (origE G K i)).1=origV G K v ∨ ((G).endpoints (origE G K i)).2=origV G K v := by
  have inj : Function.Injective (origV G K) := ((List.nodup_finRange _).filter _).injective_get
  unfold coreGraph; constructor
  · exact Or.imp (fun he => by simpa using congrArg (origV G K) he) (fun he => by simpa using congrArg (origV G K) he)
  · exact Or.imp (fun he => inj (by simpa using he)) (fun he => inj (by simpa using he))

theorem ports_ok (v : Fin (G).nV) : ports (w x) (edges (w x)) v.val = ((G).ports v).map Fin.val := by
  unfold ports BipartiteMultigraph.ports; rw [edges_ok,List.filter_map]; congr 1; apply List.filter_congr; intro e _; simp [Function.comp_def,Fin.ext_iff,beq_eq_decide]
theorem coreports_ok (v : V G K) : ports (w x) (selected (w x) false) (origV G K v).val = ((H).ports v).map (fun e => (origE G K e).val) := by
  unfold ports; rw [selF,List.filter_map,byIndexFilter,List.map_map]; unfold BipartiteMultigraph.ports
  congr 1; apply List.filter_congr; intro e _; dsimp only [Function.comp_apply]; change ((lhs (w x) (origE G K e).val == _) || (rhs (w x) (origE G K e).val == _)) = _
  rw [lhs_ok,rhs_ok]; simp only [beq_eq_decide, ← Fin.ext_iff]; simp [incident_iff]
theorem portRow (v : V G K) : portTable (w x) (origV G K v).val = List.ofFn (fun j => (portIncl G K v j).val) := by
  unfold portTable; rw [coreports_ok,ports_ok];
  exact (List.map_map ..).trans ((byIndex _ _).trans (congrArg List.ofFn (funext (fun j => idx_map ((G).ports (origV G K v)) (origE G K (((H).ports v).get j))))))

theorem cut_ok : cutCoreRaw (w x) = (cutCore G K h).encode G K := by
  unfold cutCoreRaw Raw.cut; dsimp only; rw [graph_ok,hosts_ok,pins_ok,orig_ok,selT]
  unfold Cut.encode; rw [pack_ok,pack_ok]; change Encoding.encodeList id [_,_,_,_,_,_] = Encoding.encodeList id [_,_,_,_,_,_]
  congr 2; simp only [cutCore]; congr 1 <;> try rfl
  simp only [List.map_ofFn,Function.comp_def]; simp_rw [portRow]; rfl
end DetDLP.D4CoreCut.Check
open DetDLP DetDLP.D4CoreCut Finset
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
theorem solution : Groundwork.PolyT cutCoreRaw ∧ ∀ {C c : ℕ} (x : D4Plan.Input C c),
    let L := x.spec.lookupVerts
    let t := cutCore x.G L (independent_of_spec x.G x.spec)
    cutCoreRaw (D4Plan.input x) = t.encode x.G L ∧ t.H₀.nE ≤ x.S ∧ t.H₀.nV ≤ x.G.nV ∧
    t.H₀.maxDeg ≤ C * Nat.ceil ((x.b : ℝ)^((3:ℝ)/4)) ∧ t.boundary.length = 4*x.m*x.k ∧
    (∀ z,(univ.filter fun y => t.host z = t.host y).card ≤ 1) ∧
    ∀ (A : Type) [CommRing A] (T : (v : Fin x.G.nV) → (Fin (x.G.deg v) → Bool) → A),
    let bit := fun (η : Fin (4*x.m*x.k) → Bool) (e : Fin x.G.nE) => (List.ofFn η).getD (t.boundary.idxOf e) false
    let pin := fun (η : Fin (4*x.m*x.k) → Bool) (v : Fin t.H₀.nV) (a : Fin (t.H₀.deg v) → Bool) =>
      T (t.orig v) (fun j =>
        let e := (x.G.ports (t.orig v)).get j
        if e ∈ t.boundary then bit η e else
          let i := (coreEdges x.G L).idxOf e
          (List.ofFn a).getD ((t.H₀.ports v).map Fin.val |>.idxOf i) false)
    BTNContract x.G T = ∑ η : Fin (4*x.m*x.k) → Bool,
      (∏ v : ↥L,T v.val (fun j => bit η ((x.G.ports v.val).get j))) * BTNContract t.H₀ (pin η) := by
  refine ⟨Check.rawCutPoly,?_⟩
  intro C c x L t
  let e := Geom.cutEquiv x.G L
  let rank := finCongr (Geom.cut_card x.G x.spec)
  let rel := e.symm.trans rank
  refine ⟨Check.cut_ok x,CG.countE x.spec,CG.countV x.spec,CG.maxDegree x.spec,Geom.cut_card x.G x.spec,CG.tau x.spec,?_⟩
  intro A _ T bit pin
  refine (M14ActualCore.cut x.G L T).trans ?_
  let eqv := rel.arrowCongr (Equiv.refl Bool)
  apply Fintype.sum_equiv eqv; intro η
  have readB (b : M14ActualCore.B x.G L) : bit (eqv η) b.val = η b := by
    change (List.ofFn (eqv η)).getD ((boundaryEdges x.G L).idxOf b.val) false = _
    change (List.ofFn (eqv η)).getD (rel b).val false = _
    rw [Check.getD_fn]; exact congrArg η (rel.symm_apply_apply b)
  congr 1
  · apply Finset.prod_congr rfl; intro v _
    unfold M14ActualCore.lookupTensor; apply congrArg (T v.val); funext j; exact (readB _).symm
  · apply congrArg (BTNContract t.H₀); funext v a
    unfold M14ActualCore.coreTensor M14ActualCore.lifted
    apply congrArg (T (t.orig v)); funext j
    let edge := (x.G.ports (t.orig v)).get j
    have hm : edge ∈ t.boundary ↔ M14ActualCore.boundary x.G L edge := by change edge ∈ boundaryEdges x.G L ↔ _; simp [boundaryEdges,M14ActualCore.boundary]
    by_cases hb : M14ActualCore.boundary x.G L edge
    · change (if hb' : M14ActualCore.boundary x.G L edge then η ⟨edge,hb'⟩ else _) = (if edge ∈ t.boundary then bit _ edge else _)
      rw [dif_pos hb,if_pos (hm.mpr hb)]; exact (readB ⟨edge,hb⟩).symm
    · change (if hb' : M14ActualCore.boundary x.G L edge then η ⟨edge,hb'⟩ else _) = (if edge ∈ t.boundary then bit _ edge else _)
      rw [dif_neg hb,if_neg (mt hm.mp hb)]
      let i : Fin t.H₀.nE := ⟨(coreEdges x.G L).idxOf edge,List.idxOf_lt_length_iff.mpr (by simpa [coreEdges,M14ActualCore.boundary,not_or] using hb)⟩
      change M14ActualCore.supplied t.H₀ v a i = (List.ofFn a).getD ((t.H₀.ports v).map Fin.val |>.idxOf i.val) false
      rw [Check.idx_map]; unfold M14ActualCore.supplied
      split
      · rename_i h; exact (Check.getD_fn a ⟨_,List.idxOf_lt_length_iff.mpr h⟩ false).symm
      · rename_i hn; rw [List.idxOf_of_notMem hn]; simp [List.getD_eq_getElem?_getD,BipartiteMultigraph.deg,t,cutCore,M14ActualCore.core]
