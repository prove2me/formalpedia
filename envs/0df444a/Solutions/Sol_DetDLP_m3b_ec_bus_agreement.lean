-- Prove2me | solution 1 for DetDLP.m3b_ec_bus_agreement
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:28:20.495974+00:00
-- url     : https://prove2.me/submissions/4b241d2e-1f76-41fd-99c5-514218f13ff8

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs

set_option autoImplicit false
set_option maxHeartbeats 600000
open DetDLP DetDLP.M3B S8H0 RegisterMap NamedBlocks S8J
namespace ECBusMatch
attribute [-simp] Fin.natAdd_eq_addNat

private def edges {e g : ℕ} (f : Fin e → Fin g) (v : Fin g) := (List.finRange e).filter (fun j => decide (f j = v))
private def bits {a b : ℕ} (f : Fin a → Fin b) (v : Fin b) (x : Fin a → Bool) := (edges f v).map x
private def EBit {s : RegisterMap.Shape} (r : Ref s) : ECPolyDefs.Bit := (r.source.val,r.read false,r.read true)
private theorem readBit {s : RegisterMap.Shape} {b : ECPolyDefs.Bit} {r : Ref s} (h : b = EBit r) (v : Bool) : ECPolyDefs.rd b v = r.read v := by cases v <;> rw [h] <;> rfl
private structure Fits {q : ℕ} (a : ECPolyDefs.N) (b : B q) : Prop where
  g : ECPolyDefs.ng a=b.core.A.ng
  e : ECPolyDefs.ne a=b.core.A.ne
  own : ∀ i : Fin b.core.A.ne, ECPolyDefs.gate a i.val=(b.core.A.gate i).val
  name : ∀ i : Fin b.core.A.ne, ECPolyDefs.signal a i.val=(b.name i).val
  chk : ∀ (i : Fin b.core.A.ng) (x : Fin b.core.A.ne → Bool), ECPolyDefs.check a i.val (bits b.core.A.gate i x) = b.core.t i (fun j => x j.val)
private theorem splitFin (n m : ℕ) : List.finRange (n+m) = (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
  simp only [← List.ofFn_id,List.map_ofFn]; exact List.ofFn_add
private theorem apart {n m : ℕ} (i : Fin m) (j : Fin n) : Fin.natAdd n i ≠ Fin.castAdd m j := by
  intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd,Fin.val_natAdd] at this; omega
private theorem filterNo {α : Type} (l : List α) : l.filter (fun _ => false) = [] := by simp
private theorem bitsL {n m u v : ℕ} (f : Fin n → Fin u) (g : Fin m → Fin v) (j : Fin u) (x : Fin (n+m) → Bool) :
    bits (splitMap f g) (Fin.castAdd v j) x = bits f j (x ∘ Fin.castAdd m) := by
  simp only [bits,edges,splitFin n m,List.filter_append,List.filter_map,Function.comp_def,splitMap,Fin.addCases_left,Fin.addCases_right,Fin.castAdd_inj,apart,decide_false,filterNo,List.map_nil,List.append_nil,List.map_map]
private theorem bitsR {n m u v : ℕ} (f : Fin n → Fin u) (g : Fin m → Fin v) (j : Fin v) (x : Fin (n+m) → Bool) :
    bits (splitMap f g) (Fin.natAdd u j) x = bits g j (x ∘ Fin.natAdd n) := by
  simp only [bits,edges,splitFin n m,List.filter_append,List.filter_map,Function.comp_def,splitMap,Fin.addCases_left,Fin.addCases_right,Fin.natAdd_inj,Ne.symm (apart _ _),decide_false,filterNo,List.map_nil,List.nil_append,List.map_map]
private theorem joinM {q : ℕ} {a b : ECPolyDefs.N} {A B : NamedBlocks.B q} (h : Fits a A) (k : Fits b B) : Fits (ECPolyDefs.cat a b) (joinB A B) := by
  refine ⟨congrArg₂ (·+·) h.g k.g,congrArg₂ (·+·) h.e k.e,?_,?_,?_⟩
  · intro i; induction i using Fin.addCases with
    | left i => simp [ECPolyDefs.cat,ECPolyDefs.gate,joinB,join,splitMap,h.e,i.isLt]; exact h.own i
    | right i => simp [ECPolyDefs.cat,ECPolyDefs.gate,joinB,join,splitMap,h.e,h.g]; exact k.own i
  · intro i; induction i using Fin.addCases with
    | left i => simp [ECPolyDefs.cat,ECPolyDefs.signal,joinB,h.e,i.isLt]; exact h.name i
    | right i => simp [ECPolyDefs.cat,ECPolyDefs.signal,joinB,h.e]; exact k.name i
  · intro i; induction i using Fin.addCases with
    | left i =>
      intro x; change Fin (A.core.A.ne + B.core.A.ne) → Bool at x; change (if i.val < ECPolyDefs.ng a then ECPolyDefs.check a i.val else _) (bits (splitMap A.core.A.gate B.core.A.gate) (Fin.castAdd _ i) x) = joinTest A.core.t B.core.t (Fin.castAdd _ i) _
      rw [h.g,if_pos i.isLt,bitsL]; exact (h.chk i _).trans (by simp [joinTest])
    | right i =>
      intro x; change Fin (A.core.A.ne + B.core.A.ne) → Bool at x; change (if A.core.A.ng+i.val < ECPolyDefs.ng a then _ else ECPolyDefs.check b (A.core.A.ng+i.val-ECPolyDefs.ng a)) (bits (splitMap A.core.A.gate B.core.A.gate) (Fin.natAdd _ i) x) = joinTest A.core.t B.core.t (Fin.natAdd _ i) _
      rw [h.g,if_neg (by omega),Nat.add_sub_cancel_left,bitsR]; exact (k.chk i _).trans (by simp [joinTest])

private theorem rowBits {n m : ℕ} (i : Fin n) (x : Fin (n*m) → Bool) :
    bits (fun j : Fin (n*m) => (finProdFinEquiv.symm j).1) i x = List.ofFn (fun j : Fin m => x (finProdFinEquiv (i,j))) := by
  let E := fun j : Fin m => finProdFinEquiv (i,j)
  have sort : (List.finRange (n*m)).Pairwise (· < ·) := by simp only [← List.ofFn_id,List.pairwise_ofFn,id_eq]; exact fun _ _ h => h
  have hs : (edges (fun j : Fin (n*m) => (finProdFinEquiv.symm j).1) i).Pairwise (· < ·) := sort.filter _
  have ht : (List.ofFn E).Pairwise (· < ·) := by
    apply List.pairwise_ofFn.mpr; intro a b h; change a.val+m*i.val < b.val+m*i.val; exact Nat.add_lt_add_right h _
  have heq := hs.eq_of_mem_iff ht (fun v => by
    simp only [edges,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,List.mem_ofFn]
    constructor
    · intro h; exact ⟨(finProdFinEquiv.symm v).2,by dsimp [E]; rw [←h]; exact finProdFinEquiv.apply_symm_apply v⟩
    · rintro ⟨j,rfl⟩; simp [E])
  unfold bits; rw [heq,List.map_ofFn]; rfl
private theorem rowM {s : RegisterMap.Shape} {n m : ℕ} (w : ℕ → ℕ → ECPolyDefs.Bit) (r : Fin n → Fin m → Ref s)
    (t : ℕ → (ℕ → Bool) → Bool) (u : Fin n → (Fin m → Bool) → Bool)
    (hw : ∀ (i : Fin n) (j : Fin m), w i.val j.val = EBit (r i j))
    (ht : ∀ (i : Fin n) (v : ℕ → Bool), t i v = u i (fun j => v j.val)) : Fits (ECPolyDefs.rows n m w t) (rows n m r u) := by
  refine ⟨rfl,rfl,fun _ => rfl,?_,?_⟩
  · intro i; exact congrArg Prod.fst (hw (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
  · intro i x
    change Fin n at i; change Fin (n*m) → Bool at x
    change t i.val (fun j => ECPolyDefs.rd (w i.val j) ((bits (fun k : Fin (n*m) => (finProdFinEquiv.symm k).1) i x).getD j false)) = _
    rw [rowBits,ht]; apply congrArg (u i); funext j
    rw [List.getD_eq_getElem _ _ (by simp [j.isLt]),List.getElem_ofFn,readBit (hw i j)]
    change _ = (r (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2).read _
    simp
private theorem eqM {s : RegisterMap.Shape} {n : ℕ} {a b : ECPolyDefs.Word} {A B : Fin n → Ref s}
    (ha : ∀ i : Fin n, a i = EBit (A i)) (hb : ∀ i : Fin n, b i = EBit (B i)) : Fits (ECPolyDefs.eqs n a b) (NamedBlocks.eqs n A B) := by
  apply rowM
  · intro i j; fin_cases j; exact ha i; exact hb i
  · intro i v; change (v 0 == v 1) = decide (v 0=v 1); cases v 0 <;> cases v 1 <;> rfl

private theorem colM {s : RegisterMap.Shape} {n : ℕ} (cin : Bool) {a b z c : ECPolyDefs.Word} {A B Z C : Fin n → Ref s}
    (ha : ∀ i : Fin n, a i = EBit (A i)) (hb : ∀ i : Fin n, b i = EBit (B i)) (hz : ∀ i : Fin n, z i = EBit (Z i)) (hc : ∀ i : Fin n, c i = EBit (C i)) :
    Fits (ECPolyDefs.col n cin a b z c) (NamedBlocks.add cin A B Z C) := by
  let ref := fun i j => match j with | 0 => a i | 1 => b i | 2 => z i | 3 => c i | _ => c (if i=0 then n-1 else i-1)
  let phy := fun (i : Fin n) (j : Fin 5) => colRef A B Z C (S8C.AddLayout.bit (S8C.AddLayout.pos i j))
  have reg {i : Fin n} (j : Fin 4) : colRef A B Z C (S8C.AddLayout.reg i j) =
      match j.val with | 0 => A i | 1 => B i | 2 => Z i | _ => C i := by
    have h1 : (4*i.val+j.val)%4=j.val := by omega
    have h2 : (4*i.val+j.val)/4=i.val := by omega
    simp only [colRef,S8C.AddLayout.reg,h1]; have eq : (⟨(4*i.val+j.val)/4,by omega⟩ : Fin n)=i := Fin.ext h2
    rw [eq]; fin_cases j <;> rfl
  have route (i : Fin n) (j : Fin 5) : ref i.val j.val = EBit (phy i j) := by
    dsimp only [phy]; rw [S8C.AddLayout.bit_pos]; fin_cases j
    · rw [dif_pos (by decide),reg]; exact ha i
    · rw [dif_pos (by decide),reg]; exact hb i
    · rw [dif_pos (by decide),reg]; exact hz i
    · rw [dif_pos (by decide),reg]; exact hc i
    · rw [dif_neg (by decide),reg]; exact hc (S8C.AddLayout.prev i)
  have pos (i : Fin n) (j : Fin 5) : finProdFinEquiv (i,j) = S8C.AddLayout.pos i j := by apply Fin.ext; change j.val+5*i.val=5*i.val+j.val; omega
  have any (k : Fin (n*5)) : ref (k.val/5) (k.val%5) = EBit (colRef A B Z C (S8C.AddLayout.bit k)) := by
    let i := (finProdFinEquiv.symm k).1; let j := (finProdFinEquiv.symm k).2
    have eq : S8C.AddLayout.pos i j = k := (pos i j).symm.trans (finProdFinEquiv.apply_symm_apply k)
    rw [← show i.val = k.val/5 from rfl,← show j.val = k.val%5 from rfl]
    simpa only [phy,eq] using route i j
  refine ⟨rfl,rfl,fun _ => rfl,fun k => congrArg Prod.fst (any k),?_⟩
  intro i x; change Fin n at i; change Fin (n*5) → Bool at x
  let v := fun (j : ℕ) => ECPolyDefs.rd (ref i j) ((bits (fun k : Fin (n*5) => (finProdFinEquiv.symm k).1) i x).getD j false)
  let u := fun j : Fin 5 => (phy i j).read (x (S8C.AddLayout.pos i j))
  have equal (j : Fin 5) : v j.val = u j := by
    dsimp only [v,u]; rw [rowBits,List.getD_eq_getElem _ _ (by simp [j.isLt]),List.getElem_ofFn,readBit (route i j),pos]
  change decide ((v 0).toNat + (v 1).toNat + (if i.val=0 then cin else v 4).toNat = (v 2).toNat+2*(v 3).toNat ∧ (i.val+1=n → v 3=false)) =
    decide ((u 0).toNat + (u 1).toNat + (if i.val=0 then cin else u 4).toNat = (u 2).toNat+2*(u 3).toNat ∧ (i.val+1=n → u 3=false))
  rw [show v 0 = u 0 from equal 0,show v 1=u 1 from equal 1,show v 2=u 2 from equal 2,show v 3=u 3 from equal 3,show v 4=u 4 from equal 4]

open ECPhysicalNet ECChainBlocks GateSemantics
private theorem pairVal {n l : ℕ} (i : Fin n) (j : Fin l) : (finProdFinEquiv (i,j)).val = i.val*l+j.val := by change j.val+l*i.val=_; ring
private theorem widths (p m k : ℕ) :
    (ShapeOf p m k).size = 4*m*ECPolyDefs.slotSize (d p) (e p) (busWidth p k)+2*ECPolyDefs.chainSize (d p) (e p) m+ECPolyDefs.pt (d p) := by
  simp only [ShapeOf,SlotCell,ECArithBlock.Sh,GateRoutes.S,Chain,Cells,PointCell,ECAddRows.addShape,ECMapRows.mapShape,
    ECMapRows.slot,GateRoutes.auxShape,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,bank,Shape.size,ECPolyDefs.slotSize,
    ECPolyDefs.bankSize,ECPolyDefs.triple,ECPolyDefs.pt,ECPolyDefs.chainSize,ECPolyDefs.mapSize,ECPolyDefs.addSize,
    ECPolyDefs.gsize,ECPolyDefs.run,ECPolyDefs.aux]; ring
private theorem offset {p m k : ℕ} (i : Fin (4*m)) (l : Fin 3) (j : Fin (busWidth p k)) :
    (busAddr i l j).index.val = ECPolyDefs.busOff (d p) (e p) (busWidth p k) i l + j := by
  change ((finProdFinEquiv (i, Fin.natAdd (ECArithBlock.Sh p).size (Fin.natAdd (d p) (Fin.natAdd (d p+1) (finProdFinEquiv (l,j))))))).val = _
  rw [pairVal,Fin.val_natAdd,Fin.val_natAdd,Fin.val_natAdd,pairVal]
  simp only [ECArithBlock.Sh,GateRoutes.S,bank,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,Shape.size,
    ECPolyDefs.busOff,ECPolyDefs.slotSize,ECPolyDefs.bankSize,ECPolyDefs.triple,ECPolyDefs.pt,ECPolyDefs.run,ECPolyDefs.aux]; ring

private theorem busMatch {p m k : ℕ} (T : ℕ) (i : Fin (4*m)) :
    let d := GateSemantics.d p; let e := GateSemantics.e p; let w := busWidth p k; let K := (ShapeOf p m k).size
    let I := inputs (p:=p) (m:=m) (k:=k)
    Fits (ECPolyDefs.busN K d e w T i.val) (ECAddrGadget.block T (I.parity i) (I.hash i) (I.selected i) (fun j => .reg (I.addr i j)) (I.carry i)) := by
  let d := GateSemantics.d p; let e := GateSemantics.e p; let w := busWidth p k; let K := (ShapeOf p m k).size
  let t := i.val*ECPolyDefs.slotSize d e w
  let I := inputs (p:=p) (m:=m) (k:=k)
  have reg (a : Addr (ShapeOf p m k)) : EBit (.reg a) = ECPolyDefs.reg a.index.val := rfl
  have bus (l : Fin 3) (j : Fin w) : ECPolyDefs.word K (ECPolyDefs.busOff d e w i l) w j.val = EBit (.reg (busAddr i l j)) := by
    rw [reg,offset]; exact if_pos j.isLt
  have cellId (a : Addr (SlotCell p k)) : (cell (p:=p) (m:=m) (k:=k) i a).index.val = t+a.index.val := by
    change (finProdFinEquiv (i,a.index)).val = _; rw [pairVal]; unfold t
    congr 1; congr 1
    simp only [SlotCell,ECArithBlock.Sh,GateRoutes.S,RegisterMap.bank,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,Shape.size,
      ECPolyDefs.slotSize,ECPolyDefs.bankSize,ECPolyDefs.pt,ECPolyDefs.triple,ECPolyDefs.run,ECPolyDefs.aux]; ring
  have parity : ECPolyDefs.reg (t+1+ECPolyDefs.triple d) = EBit (I.parity i) := by
    change _ = EBit (.reg (cell i _)); rw [reg,cellId]; congr 1
    change t+1+ECPolyDefs.triple d = t+(1+((RegisterMap.triple d).size+0))
    simp only [ECPolyDefs.triple,RegisterMap.triple,Shape.size]; ring
  have hash (j : Fin w) : ECPolyDefs.word K (t+ECPolyDefs.pt d+6*ECPolyDefs.run d e) d j.val = EBit (I.hash i j) := by
    change _ = EBit (RangeRows.pad (slotPath i).hash j)
    unfold ECPolyDefs.word RangeRows.pad; by_cases hj : j.val < d
    · rw [if_pos hj,dif_pos hj]; change _ = EBit (.reg (cell i _)); rw [reg,cellId]; congr 1
      change t+ECPolyDefs.pt d+6*ECPolyDefs.run d e+j.val = t+((PointCell d).size+(j.val+(RegisterMap.run d e).size*6))
      simp only [PointCell,ECPolyDefs.pt,ECPolyDefs.triple,ECPolyDefs.run,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,Shape.size]; ring
    · rw [if_neg hj,dif_neg hj]; rfl
  unfold ECPolyDefs.busN ECAddrGadget.block; dsimp only
  refine joinM (rowM _ _ _ _ ?_ ?_) (colM false hash (bus 0) (bus 1) (bus 2))
  · intro j u; fin_cases u; exact parity; exact bus 0 j
  · intro j v; change (v 1 == (v 0 && T.testBit j.val)) = decide (v 1 = (v 0 && T.testBit j.val))
    cases v 1 <;> cases (v 0 && T.testBit j.val) <;> rfl
end ECBusMatch
open ECPhysicalNet GateSemantics

theorem solution {p m k : ℕ} (T : ℕ) (i : Fin (4*m)) :
    let a := ECPolyDefs.busN (ShapeOf p m k).size (d p) (e p) (busWidth p k) T i.val
    let I := inputs (p:=p) (m:=m) (k:=k)
    let b := ECAddrGadget.block T (I.parity i) (I.hash i) (I.selected i) (fun j => .reg (I.addr i j)) (I.carry i)
    ECPolyDefs.ng a=b.core.A.ng ∧ ECPolyDefs.ne a=b.core.A.ne ∧
    (∀ j : Fin b.core.A.ne, ECPolyDefs.gate a j.val=(b.core.A.gate j).val ∧ ECPolyDefs.signal a j.val=(b.name j).val) ∧
    (∀ (g : Fin b.core.A.ng) (x : Fin b.core.A.ne → Bool), ECPolyDefs.check a g.val (((List.finRange b.core.A.ne).filter (fun j => decide (b.core.A.gate j = g))).map x) = b.core.t g (fun j => x j.val)) := by
  have h := ECBusMatch.busMatch (p:=p) (k:=k) T i
  exact ⟨h.g,h.e,fun j => ⟨h.own j,h.name j⟩,h.chk⟩
