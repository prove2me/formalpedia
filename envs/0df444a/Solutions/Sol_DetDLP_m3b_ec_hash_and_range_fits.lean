-- Prove2me | solution 1 for DetDLP.m3b_ec_hash_and_range_fits
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T09:46:00.21849+00:00
-- url     : https://prove2.me/submissions/c9ca9baf-d9df-4b78-9f01-ec61848b7609

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_M3B_ECFits
import Theorems.Thm_DetDLP_m3b_ec_multiplier_agreement

set_option autoImplicit false
set_option maxHeartbeats 600000
open DetDLP DetDLP.M3B DetDLP.M3B.ECFits S8H0 RegisterMap NamedBlocks S8J HashRows

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace DetDLP.M3B.ECFitsCombinators
attribute [-simp] Fin.natAdd_eq_addNat

def edges {e g : ℕ} (f : Fin e → Fin g) (v : Fin g) := (List.finRange e).filter (fun j => decide (f j = v))
def bits {a b : ℕ} (f : Fin a → Fin b) (v : Fin b) (x : Fin a → Bool) := (edges f v).map x

theorem readBit {s : RegisterMap.Shape} {b : ECPolyDefs.Bit} {r : Ref s} (h : b = EBit r) (v : Bool) :
    ECPolyDefs.rd b v = r.read v := by cases v <;> rw [h] <;> rfl

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

theorem joinM {q : ℕ} {a b : ECPolyDefs.N} {A B : NamedBlocks.B q} (h : Fits a A) (k : Fits b B) :
    Fits (ECPolyDefs.cat a b) (joinB A B) := by
  refine ⟨congrArg₂ (·+·) h.g k.g,congrArg₂ (·+·) h.e k.e,?_,?_,?_⟩
  · intro i; induction i using Fin.addCases with
    | left i => simp [ECPolyDefs.cat,ECPolyDefs.gate,joinB,join,splitMap,h.e,i.isLt]; exact h.own i
    | right i => simp [ECPolyDefs.cat,ECPolyDefs.gate,joinB,join,splitMap,h.e,h.g]; exact k.own i
  · intro i; induction i using Fin.addCases with
    | left i => simp [ECPolyDefs.cat,ECPolyDefs.signal,joinB,h.e,i.isLt]; exact h.name i
    | right i => simp [ECPolyDefs.cat,ECPolyDefs.signal,joinB,h.e]; exact k.name i
  · intro i; induction i using Fin.addCases with
    | left i =>
      intro x; change Fin (A.core.A.ne + B.core.A.ne) → Bool at x
      change (if i.val < ECPolyDefs.ng a then ECPolyDefs.check a i.val else _) (bits (splitMap A.core.A.gate B.core.A.gate) (Fin.castAdd _ i) x) = joinTest A.core.t B.core.t (Fin.castAdd _ i) _
      rw [h.g,if_pos i.isLt,bitsL]; exact (h.chk i _).trans (by simp [joinTest])
    | right i =>
      intro x; change Fin (A.core.A.ne + B.core.A.ne) → Bool at x
      change (if A.core.A.ng+i.val < ECPolyDefs.ng a then _ else ECPolyDefs.check b (A.core.A.ng+i.val-ECPolyDefs.ng a)) (bits (splitMap A.core.A.gate B.core.A.gate) (Fin.natAdd _ i) x) = joinTest A.core.t B.core.t (Fin.natAdd _ i) _
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

theorem rowM {s : RegisterMap.Shape} {n m : ℕ} (w : ℕ → ℕ → ECPolyDefs.Bit) (r : Fin n → Fin m → Ref s)
    (t : ℕ → (ℕ → Bool) → Bool) (u : Fin n → (Fin m → Bool) → Bool)
    (hw : ∀ (i : Fin n) (j : Fin m), w i.val j.val = EBit (r i j))
    (ht : ∀ (i : Fin n) (v : ℕ → Bool), t i v = u i (fun j => v j.val)) :
    Fits (ECPolyDefs.rows n m w t) (NamedBlocks.rows n m r u) := by
  refine ⟨rfl,rfl,fun _ => rfl,?_,?_⟩
  · intro i; exact congrArg Prod.fst (hw (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
  · intro i x
    change Fin n at i; change Fin (n*m) → Bool at x
    change t i.val (fun j => ECPolyDefs.rd (w i.val j) ((bits (fun k : Fin (n*m) => (finProdFinEquiv.symm k).1) i x).getD j false)) = _
    rw [rowBits,ht]; apply congrArg (u i); funext j
    rw [List.getD_eq_getElem _ _ (by simp [j.isLt]),List.getElem_ofFn,readBit (hw i j)]
    change _ = (r (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2).read _
    simp

theorem eqM {s : RegisterMap.Shape} {n : ℕ} {a b : ECPolyDefs.Word} {A B : Fin n → Ref s}
    (ha : ∀ i : Fin n, a i = EBit (A i)) (hb : ∀ i : Fin n, b i = EBit (B i)) :
    Fits (ECPolyDefs.eqs n a b) (NamedBlocks.eqs n A B) := by
  apply rowM
  · intro i j; fin_cases j; exact ha i; exact hb i
  · intro i v; change (v 0 == v 1) = decide (v 0=v 1); cases v 0 <;> cases v 1 <;> rfl

theorem colM {s : RegisterMap.Shape} {n : ℕ} (cin : Bool) {a b z c : ECPolyDefs.Word} {A B Z C : Fin n → Ref s}
    (ha : ∀ i : Fin n, a i = EBit (A i)) (hb : ∀ i : Fin n, b i = EBit (B i))
    (hz : ∀ i : Fin n, z i = EBit (Z i)) (hc : ∀ i : Fin n, c i = EBit (C i)) :
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

theorem prodM {s : RegisterMap.Shape} {d K off : ℕ} (hd : 1 ≤ d) {a b z : ECPolyDefs.Word}
    {A B Z : HashRows.Word s} {R : Fin (w3_fpMulLayout d hd).nb → Ref s}
    (hr : ∀ j, ECPolyDefs.reg (off+j.val) = EBit (R j))
    (ha : ∀ j, a j = EBit (A j)) (hb : ∀ j, b j = EBit (B j)) (hz : ∀ j, z j = EBit (Z j)) :
    Fits (ECPolyDefs.prod K d off a b z) (HashRows.product hd A B Z R) := by
  obtain ⟨hg, he, hgn, hchk⟩ := m3b_ec_multiplier_agreement (K:=K) hd a b z A B Z R hr ha hb hz
  exact ⟨hg, he, fun j => (hgn j).1, fun j => (hgn j).2, hchk⟩

open DetDLP.M3B.ECPolyDefs (N ng ne gate signal check cat copies)
private structure Agree (a b : N) : Prop where
  g : ng a=ng b
  e : ne a=ne b
  own : ∀ j, j<ne b → gate a j=gate b j
  name : ∀ j, j<ne b → signal a j=signal b j
  chk : ∀ j, j<ng b → check a j=check b j
private theorem convertM {k} {a b : N} {c : NamedBlocks.B k} (h : Agree a b) (u : Fits b c) : Fits a c :=
  ⟨h.g.trans u.g,h.e.trans u.e,fun i => (h.own i (u.e.symm ▸ i.isLt)).trans (u.own i),
    fun i => (h.name i (u.e.symm ▸ i.isLt)).trans (u.name i),fun i x => (congrFun (h.chk i (u.g.symm ▸ i.isLt)) _).trans (u.chk i x)⟩
private theorem cpSucc (n G E : ℕ) (f : ℕ → N) (hg : ∀ j, ng (f j)=G) (he : ∀ j, ne (f j)=E) :
    Agree (copies (n+1) f) (cat (f 0) (copies n (fun j => f (j+1)))) := by
  have gateC (f : ℕ → N) (n j : ℕ) : gate (copies n f) j = j/ne (f 0)*ng (f 0)+gate (f (j/ne (f 0))) (j%ne (f 0)) := rfl
  have sigC (f : ℕ → N) (n j : ℕ) : signal (copies n f) j = signal (f (j/ne (f 0))) (j%ne (f 0)) := rfl
  have chkC (f : ℕ → N) (n j : ℕ) : check (copies n f) j = check (f (j/ng (f 0))) (j%ng (f 0)) := rfl
  have gCat (a b : N) : ng (cat a b)=ng a+ng b := rfl
  have eCat (a b : N) : ne (cat a b)=ne a+ne b := rfl
  have gCop (n : ℕ) (f : ℕ → N) : ng (copies n f)=n*ng (f 0) := rfl
  have eCop (n : ℕ) (f : ℕ → N) : ne (copies n f)=n*ne (f 0) := rfl
  have gateCat (a b : N) (j : ℕ) : gate (cat a b) j = if j<ne a then gate a j else ng a + gate b (j-ne a) := rfl
  have sigCat (a b : N) (j : ℕ) : signal (cat a b) j = if j<ne a then signal a j else signal b (j-ne a) := rfl
  have chkCat (a b : N) (j : ℕ) : check (cat a b) j = if j<ng a then check a j else check b (j-ng a) := rfl
  constructor
  · simp only [gCat,gCop,hg]; ring
  · simp only [eCat,eCop,he]; ring
  · intro j hj; simp only [eCat,eCop,he] at hj; simp only [gateCat,gateC,he,hg]
    by_cases h : j<E
    · simp [h,Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]
    · have pos : 0<E := by by_contra! hn; simp [show E=0 by omega] at hj
      obtain ⟨z,rfl⟩ : ∃ z, j=E+z := ⟨j-E,by omega⟩
      simp only [h,reduceIte,Nat.add_sub_cancel_left,Nat.add_div_left _ pos,Nat.add_mod_left,Nat.succ_mul]; omega
  · intro j hj; simp only [eCat,eCop,he] at hj; simp only [sigCat,sigC,he]
    by_cases h : j<E
    · simp [h,Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]
    · have pos : 0<E := by by_contra! hn; simp [show E=0 by omega] at hj
      obtain ⟨z,rfl⟩ : ∃ z, j=E+z := ⟨j-E,by omega⟩; simp [h,pos]
  · intro j hj; simp only [gCat,gCop,hg] at hj; simp only [chkCat,chkC,hg]
    by_cases h : j<G
    · simp [h,Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]
    · have pos : 0<G := by by_contra! hn; simp [show G=0 by omega] at hj
      obtain ⟨z,rfl⟩ : ∃ z, j=G+z := ⟨j-G,by omega⟩; simp [h,pos]

theorem manyM {k : ℕ} (n g e : ℕ) (f : ℕ → N) (F : Fin n → NamedBlocks.B k)
    (h : ∀ i : Fin n, Fits (f i.val) (F i)) (hg : ∀ j, ng (f j)=g) (he : ∀ j, ne (f j)=e) :
    Fits (copies n f) (ECChainBlocks.manyB n F) := by
  induction n generalizing f with
  | zero => exact ⟨Nat.zero_mul _,Nat.zero_mul _,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | succ n ih =>
    apply convertM (cpSucc n g e f hg he)
    exact joinM (h 0) (ih (fun j => f (j+1)) (fun i => F i.succ) (fun i => h i.succ) (fun i => hg (i+1)) (fun i => he (i+1)))

theorem many1M {k : ℕ} (n g e : ℕ) (f : ℕ → N) (F : Fin (n+1) → NamedBlocks.B k)
    (h : ∀ i : Fin (n+1), Fits (f i.val) (F i)) (hg : ∀ j, ng (f j)=g) (he : ∀ j, ne (f j)=e) :
    Fits (copies (n+1) f) (RangeRows.many n F) := by
  induction n generalizing f with
  | zero =>
    apply convertM (b:=f 0) _ (h 0)
    refine ⟨Nat.one_mul _,Nat.one_mul _,?_,?_,?_⟩
    · intro j hj; change j/ne (f 0)*ng (f 0)+gate (f (j/ne (f 0))) (j%ne (f 0)) = _; simp [Nat.div_eq_of_lt hj,Nat.mod_eq_of_lt hj]
    · intro j hj; change signal (f (j/ne (f 0))) (j%ne (f 0)) = _; simp [Nat.div_eq_of_lt hj,Nat.mod_eq_of_lt hj]
    · intro j hj; change check (f (j/ng (f 0))) (j%ng (f 0)) = _; simp [Nat.div_eq_of_lt hj,Nat.mod_eq_of_lt hj]
  | succ n ih =>
    apply convertM (cpSucc (n+1) g e f hg he)
    exact joinM (h 0) (ih (fun j => f (j+1)) (fun i => F i.succ) (fun i => h i.succ) (fun i => hg (i+1)) (fun i => he (i+1)))

open ECPhysicalNet ECArithBlock GateSemantics GateRoutes
private theorem pairVal {n l : ℕ} (i : Fin n) (j : Fin l) : (finProdFinEquiv (i,j)).val = i.val*l+j.val := by change j.val+l*i.val=_; ring
private theorem cellSize (p k : ℕ) : (SlotCell p k).size = ECPolyDefs.slotSize (d p) (e p) (busWidth p k) := by
  simp only [Sh,GateRoutes.S,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,bank,Shape.size,ECPolyDefs.slotSize,ECPolyDefs.bankSize,ECPolyDefs.triple,ECPolyDefs.pt,ECPolyDefs.run,ECPolyDefs.aux]; ring
private theorem bankLast {p m k : ℕ} (i : Fin (4*m)) : bankName (p:=p) (k:=k) i (Fin.last _) = Fin.last _ := Fin.lastCases_last
private theorem bankReg {p m k : ℕ} [Fact p.Prime] (i : Fin (4*m)) (a : Addr (Sh p)) :
    (bankName (k:=k) i a.index.castSucc).val = i.val*ECPolyDefs.slotSize (d p) (e p) (busWidth p k)+a.index.val := by
  rw [bankName_index]; change (finProdFinEquiv (i,a.index.castAdd _)).val = _
  rw [pairVal,←cellSize]; rfl
private theorem zeroM {n q : ℕ} (f : Fin (n+1) → Fin q) :
    Fits (ECPolyDefs.rows 1 1 (fun _ _ => ECPolyDefs.reg (f (Fin.last n)).val) (fun _ v => !v 0)) (rewire (PointGraph.zeroLast n) f) := by
  refine ⟨rfl,rfl,?_,fun _ => rfl,?_⟩
  · intro j; change j.val/1=j.val; exact Nat.div_one _
  · intro i x; change Fin 1 at i; change Fin 1 → Bool at x
    obtain rfl := Fin.eq_zero i
    change (!ECPolyDefs.rd _ ((List.map x ((List.finRange 1).filter (fun j => decide (j=0)))).getD 0 false)) = !x 0
    rw [show List.finRange 1 = [0] by decide]; cases h : x 0 <;> simp [ECPolyDefs.rd,ECPolyDefs.reg,h]
private theorem rwJoin {n q : ℕ} (u v : B n) (f : Fin n → Fin q) : rewire (joinB u v) f = joinB (rewire u f) (rewire v f) := by
  unfold rewire joinB; congr 1; funext j
  change f (Fin.addCases u.name v.name j) = Fin.addCases (f ∘ u.name) (f ∘ v.name) j
  induction j using Fin.addCases with
  | left j => erw [Fin.addCases_left,Fin.addCases_left]; rfl
  | right j => erw [Fin.addCases_right,Fin.addCases_right]; rfl
private theorem rwMany {n q : ℕ} (l : ℕ) (v : Fin (l+1) → B n) (f : Fin n → Fin q) : rewire (RangeRows.many l v) f = RangeRows.many l (fun j => rewire (v j) f) := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [RangeRows.many,rwJoin,ih]
private def route {s u : Shape} (P : Path s u) : Ref s → Ref u
  | .pin b => .pin b | .reg a => .reg (P a) | .masked b a => .masked b (P a)
private theorem routeRead {s u : Shape} (P : Path s u) (r : Ref s) (x : Bool) : (route P r).read x = r.read x := by cases r <;> rfl
private theorem routeBank {p m k : ℕ} [Fact p.Prime] (i : Fin (4*m)) (r : Ref (Sh p)) :
    (route (slot (k:=k) i) r).source = bankName i r.source := by
  cases r with
  | pin b => exact (bankLast i).symm
  | reg a => exact (bankName_index i a).symm
  | masked b a => exact (bankName_index i a).symm
private theorem rwMapped {p m k : ℕ} [Fact p.Prime] (i : Fin (4*m)) (L : w3_FactorLayout) (t : w3_factorTest L) (r : Fin L.nb → Ref (Sh p)) :
    rewire (mapped L t r) (bankName (k:=k) i) = mapped L t (fun j => route (slot i) (r j)) := by
  let t₁ : w3_factorTest L := fun g x => t g fun j => (r (L.bit j.val)).read (x j)
  let t₂ : w3_factorTest L := fun g x => t g fun j => (route (slot (k:=k) i) (r (L.bit j.val))).read (x j)
  have h : t₁ = t₂ := by funext g x; apply congrArg (t g); funext j; exact (routeRead ..).symm
  change (⟨⟨L,t₁⟩,fun j => bankName i (r (L.bit j)).source⟩ : B _) = ⟨⟨L,t₂⟩,_⟩
  rw [h]; congr 1; funext j; exact (routeBank ..).symm
section Routing
variable {p m k : ℕ} [Fact p.Prime] (i : Fin (4*m))
local notation "ρ" => route (slot (p:=p) (k:=k) i)
local notation "β" => bankName (p:=p) (k:=k) i
private theorem rwRows {n l : ℕ} (r : Fin n → Fin l → Ref (Sh p)) (u : Fin n → (Fin l → Bool) → Bool) : rewire (NamedBlocks.rows n l r u) β = NamedBlocks.rows n l (fun g j => ρ (r g j)) u := rwMapped ..
private theorem rwEq {n : ℕ} (a b : Fin n → Ref (Sh p)) : rewire (NamedBlocks.eqs n a b) β = NamedBlocks.eqs n (fun j => ρ (a j)) (fun j => ρ (b j)) := by
  unfold NamedBlocks.eqs; rw [rwRows]; congr 1; funext g j; fin_cases j <;> rfl
private theorem rwCol {n : ℕ} (cin : Bool) (a b z c : Fin n → Ref (Sh p)) : rewire (NamedBlocks.add cin a b z c) β = NamedBlocks.add cin (fun j => ρ (a j)) (fun j => ρ (b j)) (fun j => ρ (z j)) (fun j => ρ (c j)) := by
  unfold NamedBlocks.add; erw [rwMapped]; congr 1; funext j; unfold colRef; split <;> rfl
private theorem rwProd {D : ℕ} (hD : 1 ≤ D) (a b z : HashRows.Word (Sh p)) (r : Fin (w3_fpMulLayout D hD).nb → Ref (Sh p)) : rewire (HashRows.product hD a b z r) β = HashRows.product hD (fun j => ρ (a j)) (fun j => ρ (b j)) (fun j => ρ (z j)) (fun j => ρ (r j)) := by
  unfold HashRows.product; rw [rwJoin,rwMapped,rwEq]; congr 2; funext j; unfold busRef; split_ifs <;> rfl
local notation "K" => Shape.size (ShapeOf p m k)
local notation "D" => d p
local notation "W" => busWidth p k
local notation "t₀" => i.val*ECPolyDefs.slotSize D (e p) W
private theorem slotReg (a : Addr (Sh p)) {off : ℕ} (h : off = t₀+a.index.val) : ECPolyDefs.reg off = EBit (ρ (.reg a)) := by
  have H := bankReg (k:=k) i a; rw [bankName_index] at H; rw [h,←H]; rfl
private theorem slotWord {n : ℕ} (f : Fin n → Addr (Sh p)) {off : ℕ} (h : ∀ j, off+j.val=t₀+(f j).index.val) (j : ℕ) :
    ECPolyDefs.word K off n j = EBit (ρ (padded (fun j => .reg (f j)) j)) := by
  unfold ECPolyDefs.word padded; split_ifs with hj; exact slotReg i _ (h ⟨j,hj⟩); rfl
private theorem slotPad {n l : ℕ} (f : Fin n → Addr (Sh p)) {off : ℕ} (h : ∀ j, off+j.val=t₀+(f j).index.val) (j : Fin l) :
    ECPolyDefs.word K off n j.val = EBit (ρ (RangeRows.pad (fun j => .reg (f j)) j)) := slotWord i f h j.val
private theorem addrChecker {off : ℕ} (f : Path (RegisterMap.triple D) (Sh p)) (h : ∀ a, off+a.index.val=t₀+(f a).index.val) :
    Fits (ECPolyDefs.bnd K p D off) (rewire (RangeRows.checker p f) β) := by
  unfold RangeRows.checker; rw [rwCol]; apply colM
  · intro j; apply slotPad; intro l; exact h (.fst (.word l))
  · intro j; apply slotPad; intro l; have H := h (.snd (.fst (.word l))); change off+(D+l.val)=_ at H; exact (Nat.add_assoc ..).trans H
  · intro j; rfl
  · intro j; apply slotReg; have H := h (.snd (.snd (.word j))); change off+(D+(D+j.val))=_ at H; convert H using 1; omega
private theorem pairAddr {u v : Shape} (a : Addr u) : ((Addr.fst (v:=v) a).index).val = a.index.val := rfl
private theorem pairAddrR {u v : Shape} (a : Addr v) : ((Addr.snd (u:=u) a).index).val = u.size+a.index.val := rfl
private theorem vecAddr {s : Shape} {n : ℕ} (g : Fin n) (a : Addr s) : (Addr.vec g a).index.val = g.val*s.size+a.index.val := pairVal ..
private theorem gG (q p d off : ℕ) : ng (ECPolyDefs.gbound q p d off) = (d+1)+(d+1) := rfl
private theorem gE (q p d off : ℕ) : ne (ECPolyDefs.gbound q p d off) = (d+1)*5+(d+1)*5 := rfl
private theorem rangeFit : Fits (cat (ECPolyDefs.pbound K p D t₀) (copies 7 (fun g => ECPolyDefs.gbound K p D (t₀+ECPolyDefs.pt D+g*ECPolyDefs.run D (e p))))) (rewire (RangeRows.block D (e p) p) β) := by
  unfold RangeRows.block; rw [rwJoin,rwJoin,rwMany]; apply joinM
  · apply joinM <;> apply addrChecker <;> intro a <;> (simp only [RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.m1,GateRoutes.m2,GateRoutes.aux,GateRoutes.cm,GateRoutes.runPath,CurveRows.outbit,CurveRows.ybit,CurveRows.flag,Addr.index,Fin.val_castAdd,Fin.val_natAdd,pairVal,GateRoutes.auxShape,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.pt,ECPolyDefs.triple,ECPolyDefs.run,ECPolyDefs.aux]; try dsimp only [Fin.castAdd,Fin.castLE,Fin.natAdd,finProdFinEquiv,Equiv.coe_fn_mk,Shape.size,RegisterMap.run,RegisterMap.triple,RegisterMap.mul]; first | rfl | ring)
  · let net := fun g : ℕ => ECPolyDefs.gbound K p D (t₀+ECPolyDefs.pt D+g*ECPolyDefs.run D (e p))
    let F := fun g : Fin 7 => rewire (joinB (RangeRows.checker p (RangeRows.oa g)) (RangeRows.checker p (RangeRows.ra g))) β
    refine many1M 6 _ _ net F ?_ (fun g => gG ..) (fun g => gE ..)
    intro g; dsimp only [net,F]; rw [rwJoin]
    apply joinM
    · apply addrChecker; intro a
      change _ = t₀ + ((1+((RegisterMap.triple D).size+(RegisterMap.triple D).size))+(a.index.val+(RegisterMap.run D (e p)).size*g.val))
      (simp only [RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.m1,GateRoutes.m2,GateRoutes.aux,GateRoutes.cm,GateRoutes.runPath,CurveRows.outbit,CurveRows.ybit,CurveRows.flag,Addr.index,Fin.val_castAdd,Fin.val_natAdd,pairVal,GateRoutes.auxShape,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.pt,ECPolyDefs.triple,ECPolyDefs.run,ECPolyDefs.aux]; try dsimp only [Fin.castAdd,Fin.castLE,Fin.natAdd,finProdFinEquiv,Equiv.coe_fn_mk,Shape.size,RegisterMap.run,RegisterMap.triple,RegisterMap.mul]; first | rfl | ring); ring
    · apply addrChecker; intro a
      change _ = t₀ + ((1+((RegisterMap.triple D).size+(RegisterMap.triple D).size))+(((RegisterMap.triple D).size+a.index.val)+(RegisterMap.run D (e p)).size*g.val))
      (simp only [RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.m1,GateRoutes.m2,GateRoutes.aux,GateRoutes.cm,GateRoutes.runPath,CurveRows.outbit,CurveRows.ybit,CurveRows.flag,Addr.index,Fin.val_castAdd,Fin.val_natAdd,pairVal,GateRoutes.auxShape,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.pt,ECPolyDefs.triple,ECPolyDefs.run,ECPolyDefs.aux]; try dsimp only [Fin.castAdd,Fin.castLE,Fin.natAdd,finProdFinEquiv,Equiv.coe_fn_mk,Shape.size,RegisterMap.run,RegisterMap.triple,RegisterMap.mul]; first | rfl | ring); ring
local notation "runOff" => (fun g : ℕ => t₀+ECPolyDefs.pt D+g*ECPolyDefs.run D (e p))
local notation "auxOff" => (fun g : ℕ => runOff 7+g*ECPolyDefs.aux D)
omit [Fact p.Prime] in
private theorem runOffset (g : Fin 7) (a : Addr (RegisterMap.run D (e p))) : t₀+(GateRoutes.runPath g a).index.val = runOff g + a.index.val := by
  change t₀+(1+((RegisterMap.triple D).size+(RegisterMap.triple D).size)+(a.index.val+(RegisterMap.run D (e p)).size*g.val))=_
  simp only [RegisterMap.triple,RegisterMap.run,RegisterMap.mul,Shape.size,ECPolyDefs.run,ECPolyDefs.triple,ECPolyDefs.pt]; ring
omit [Fact p.Prime] in
private theorem auxOffset (g : Fin 7) (a : Addr (GateRoutes.auxShape D)) : t₀+(GateRoutes.aux (e:=e p) g a).index.val = auxOff g + a.index.val := by
  change t₀+(1+((RegisterMap.triple D).size+(RegisterMap.triple D).size)+(7*(RegisterMap.run D (e p)).size+(a.index.val+(GateRoutes.auxShape D).size*g.val)))=_
  simp only [RegisterMap.triple,RegisterMap.run,RegisterMap.mul,GateRoutes.auxShape,Shape.size,ECPolyDefs.run,ECPolyDefs.triple,ECPolyDefs.pt,ECPolyDefs.aux]; ring
private theorem maskReg (a : Addr (Sh p)) (v : Bool) {off : ℕ} (h : off = t₀+a.index.val) : ECPolyDefs.mask off v = EBit (ρ (.masked v a)) := by
  have H := bankReg (k:=k) i a; rw [bankName_index] at H; rw [h,←H]; cases v <;> rfl
private theorem hashFit (g : Fin 7) (c : GateRoutes.Coeff) (a x b : ECPolyDefs.Word) (A X Bv : HashRows.Word (Sh p))
    (ha : ∀ j, a j = EBit (ρ (A j))) (hx : ∀ j, x j = EBit (ρ (X j))) (hb : ∀ j, b j = EBit (ρ (Bv j))) :
    Fits (ECPolyDefs.hash K p D (e p) (runOff g) (auxOff g) a x b)
      (rewire (HashRows.block p { GateRoutes.wires (hd p) p c g with a := A, x := X, b := Bv }) β) := by
  let r := runOff g; let ax := auxOff g
  let rem := r+ECPolyDefs.triple D; let q := rem+ECPolyDefs.triple D; let u := q+D; let v := u+2*D+e p
  let w := GateRoutes.wires (hd p) p c g
  have reg1 (j) : ECPolyDefs.reg (u+2*D+j.val) = EBit (ρ (w.mul1 j)) := by
    apply slotReg; dsimp only [w,GateRoutes.wires,GateRoutes.m1,r,u,q,rem]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have reg2 (j) : ECPolyDefs.reg (v+2*D+j.val) = EBit (ρ (w.mul2 j)) := by
    apply slotReg; dsimp only [w,GateRoutes.wires,GateRoutes.m2,r,v,u,q,rem]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have p1 (j) : ECPolyDefs.word K u (2*D) j = EBit (ρ (w.prod1 j)) := by
    dsimp only [w,GateRoutes.wires,GateRoutes.quot,GateRoutes.rword,GateRoutes.word]; apply slotWord; intro l; dsimp only [u,q,rem,r,GateRoutes.m1]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have p2 (j) : ECPolyDefs.word K v (2*D) j = EBit (ρ (w.prod2 j)) := by
    dsimp only [w,GateRoutes.wires,GateRoutes.quot,GateRoutes.rword,GateRoutes.word]; apply slotWord; intro l; dsimp only [v,u,q,rem,r,GateRoutes.m2]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have qw (j) : ECPolyDefs.word K q D j = EBit (ρ (w.quot j)) := by
    dsimp only [w,GateRoutes.wires,GateRoutes.quot,GateRoutes.rword,GateRoutes.word]; apply slotWord; intro l; dsimp only [q,rem,r]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have remw (j) : ECPolyDefs.word K rem D j = EBit (ρ (w.rem j)) := by
    dsimp only [w,GateRoutes.wires,GateRoutes.quot,GateRoutes.rword,GateRoutes.word]; apply slotWord; intro l; dsimp only [rem,r]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have zw (j) : ECPolyDefs.word K r D j = EBit (ρ (w.z j)) := by
    dsimp only [w,GateRoutes.wires,GateRoutes.quot,GateRoutes.rword,GateRoutes.word]; apply slotWord; intro l; dsimp only [r]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have sw (j) : ECPolyDefs.word K (ax+2*D) (D+1) j = EBit (ρ (w.sum j)) := by
    dsimp only [w,GateRoutes.wires,GateRoutes.quot,GateRoutes.rword,GateRoutes.word]; apply slotWord; intro l; dsimp only [ax]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have cw (j) : ECPolyDefs.mask (v+2*D+e p) (p.testBit j) = EBit (ρ (w.cp j)) := by
    apply maskReg; dsimp only [GateRoutes.cm,w,GateRoutes.wires,v,u,q,rem,r]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have c1 (j : Fin (2*D)) : ECPolyDefs.reg (ax+j.val) = EBit (ρ (w.carry1 j)) := by
    apply slotReg; dsimp only [w,GateRoutes.wires,ax]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have c2 (j : Fin (D+1)) : ECPolyDefs.reg (ax+3*D+1+j.val) = EBit (ρ (w.carry2 j)) := by
    apply slotReg; dsimp only [w,GateRoutes.wires,ax]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  have c3 (j : Fin (D+1)) : ECPolyDefs.reg (ax+4*D+2+j.val) = EBit (ρ (w.carry3 j)) := by
    apply slotReg; dsimp only [w,GateRoutes.wires,ax]; ((first | erw [runOffset] | erw [auxOffset]) <;> dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,ECPolyDefs.triple,GateRoutes.auxShape,Fin.val_zero] <;> ring <;> rfl)
  simp only [HashRows.block,rwJoin,rwProd,HashRows.sumRows,rwCol]
  exact joinM (joinM (prodM (hd p) reg1 ha hx p1) (prodM (hd p) reg2 qw (fun _ => rfl) p2)) (joinM (colM false (fun j => p2 j) (fun j => remw j) (fun j => p1 j) c1) (joinM (colM false (fun j => remw j) (fun j => hb j) (fun j => sw j) c2) (colM false (fun j => zw j) (fun j => cw j) (fun j => sw j) c3)))
end Routing
end DetDLP.M3B.ECFitsCombinators
open DetDLP DetDLP.M3B DetDLP.M3B.ECFits S8H0 RegisterMap NamedBlocks ECPhysicalNet ECArithBlock GateSemantics
open DetDLP.M3B.ECFitsCombinators

theorem solution (p m k : ℕ) [Fact p.Prime] (i : Fin (4*m)) :
    let K := (ShapeOf p m k).size; let D := d p; let t := i.val*ECPolyDefs.slotSize D (e p) (busWidth p k)
    let r := fun g : ℕ => t+ECPolyDefs.pt D+g*ECPolyDefs.run D (e p)
    let ax := fun g : ℕ => r 7+g*ECPolyDefs.aux D
    let f := bankName (p:=p) (k:=k) i
    let bit := fun z : Ref (Sh p) => ((f z.source).val,z.read false,z.read true)
    Fits (ECPolyDefs.cat (ECPolyDefs.pbound K p D t) (ECPolyDefs.copies 7 (fun g => ECPolyDefs.gbound K p D (r g)))) (rewire (RangeRows.block D (e p) p) f) ∧
    ∀ (g : Fin 7) (c : GateRoutes.Coeff) (a x b : ECPolyDefs.Word) (A X B : HashRows.Word (Sh p)),
      (∀ j, a j = bit (A j)) → (∀ j, x j = bit (X j)) → (∀ j, b j = bit (B j)) →
      Fits (ECPolyDefs.hash K p D (e p) (r g) (ax g) a x b) (rewire (HashRows.block p { GateRoutes.wires (hd p) p c g with a := A, x := X, b := B }) f) := by
  refine ⟨rangeFit i,?_⟩
  intro g c a x b A X B ha hx hb
  apply hashFit i g c a x b A X B <;> intro j <;> simp only [EBit,routeBank,routeRead] <;> first | exact ha j | exact hx j | exact hb j


