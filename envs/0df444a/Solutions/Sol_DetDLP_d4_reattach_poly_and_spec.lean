-- Prove2me | solution 1 for DetDLP.d4_reattach_poly_and_spec
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T08:57:59.138574+00:00
-- url     : https://prove2.me/submissions/bd738fd5-3ff0-43a6-89ff-5d480cc8d3e5

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
open DetDLP DetDLP.D4CoreCut Finset
set_option autoImplicit false
theorem solution : Groundwork.PolyT reattachRaw ∧ ∀ {C c : ℕ} (x : D4Plan.Input C c) (n : ℕ),
    let L := x.spec.lookupVerts
    let B := D4CoreCut.B x.G L
    ∀ (f : B → Fin n), let H := reattach x.G L n f
    reattachRaw (reattachInput (D4Plan.input x) n (List.ofFn fun i => (f i).val)) = H.encode ∧
    H.nE = 4*x.m*x.k ∧ H.nV = 4*x.m+n ∧
    (∀ U : ℕ, (∀ j,Fintype.card {i : B // f i=j} ≤ U) → H.maxDeg ≤ max x.k U) ∧
    ∃ (old : Fin L.card ≃ ↥L) (rank : B ≃ Fin (4*x.m*x.k))
      (lp : (v : Fin L.card) → Fin (x.G.deg (old v).val) ≃ Fin (H.deg (v.castAdd n)))
      (rp : (j : Fin n) → Fin (H.deg (Fin.natAdd L.card j)) ≃ {e : B // f e=j}),
    (∀ i,(rank i).val=i.val) ∧
    (∀ v i, origB x.G L ((H.ports (v.castAdd n)).get (lp v i)) = (x.G.ports (old v).val).get i) ∧
    (∀ j i,(rp j i).val = (H.ports (Fin.natAdd L.card j)).get i) ∧
    ∀ (A : Type) [CommRing A] (T : (v : ↥L) → (Fin (x.G.deg v.val) → Bool) → A)
      (F : (j : Fin n) → ({e : B // f e=j} → Bool) → A),
    let combined : (v : Fin H.nV) → (Fin (H.deg v) → Bool) → A := Fin.addCases
      (fun v t => T (old v) (fun i => t (lp v i))) (fun j t => F j (fun e => t ((rp j).symm e)))
    BTNContract H combined = ∑ η : Fin (4*x.m*x.k) → Bool,
      (∏ v : Fin L.card, T (old v) (fun i => η (rank ((H.ports (v.castAdd n)).get (lp v i)))))*
      ∏ j : Fin n, F j (fun e => η (rank e.val)) := by
  refine ⟨Check.rawReattachPoly,?_⟩
  intro C c x n L B f H
  let rank := finCongr (Geom.cut_card x.G x.spec)
  let old := Geom.lookEquiv x.G L
  let lp := Geom.lp x.G x.spec f
  let rp := Geom.rightP x.G L f
  refine ⟨Check.reattach_ok x n f,Geom.cut_card x.G x.spec,congrArg (·+n) x.spec.card_lookup,
    Geom.degree_bound x.G x.spec f,old,rank,lp,rp,fun _ => rfl,?_,fun _ _ => rfl,?_⟩
  · intro v i
    let q := Geom.ownerFiber x.G L (independent_of_spec x.G x.spec) v i
    let e := Geom.leftP x.G L f v
    calc origB x.G L ((H.ports (Fin.castAdd n v)).get (lp v i)) = origB x.G L q.val :=
          congrArg (fun z => origB x.G L (Subtype.val z)) (e.apply_symm_apply q)
      _ = (x.G.ports (old v).val).get i := congrArg (fun z : {e // Geom.IsB x.G L e} => z.val) ((Geom.cutEquiv x.G L).apply_symm_apply _)
  · intro A _ T F combined
    unfold BTNContract
    let eqv := rank.arrowCongr (Equiv.refl Bool)
    apply Fintype.sum_equiv eqv; intro a
    refine (Fin.prod_univ_add (a:=L.card) (b:=n) (fun v => combined v (fun i => a ((H.ports v).get i)))).trans ?_
    congr 1
    · apply Finset.prod_congr rfl; intro i _; simp [combined,eqv]; rfl
    · apply Finset.prod_congr rfl; intro j _; simp only [combined,Fin.addCases_right]
      apply congrArg (F j); funext e
      change a (((rp j) ((rp j).symm e)).val) = eqv a (rank e.val)
      simp [eqv]
