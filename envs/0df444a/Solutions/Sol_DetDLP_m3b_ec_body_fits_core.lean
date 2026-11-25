-- Prove2me | solution 1 for DetDLP.m3b_ec_body_fits_core
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T10:14:25.02383+00:00
-- url     : https://prove2.me/submissions/924eab3a-0a8f-4163-907f-d2574f4e633c

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_M3B_ECFits
import Definitions.Def_DetDLP_W3C_BlockLookup
import Definitions.Def_DetDLP_W3_Separator
import Theorems.Thm_DetDLP_m3b_ec_multiplier_agreement
import Theorems.Thm_DetDLP_m3b_ec_bus_agreement
import Theorems.Thm_DetDLP_m3b_ec_slot_fits

section
set_option autoImplicit false
set_option maxHeartbeats 600000
open DetDLP DetDLP.M3B DetDLP.M3B.ECFits S8H0 RegisterMap NamedBlocks S8J HashRows

namespace DetDLP.M3B.SlotFitCombinators
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


end DetDLP.M3B.SlotFitCombinators
end

section
set_option autoImplicit false
namespace DetDLP.M3B.SlotOperands

open S8H0 RegisterMap NamedBlocks GateSemantics ECPhysicalNet ECArithBlock

variable {p m k : ℕ} [Fact p.Prime]

def seedRow (s : ECSeed p m) (i : Fin m) : List ℕ :=
  [(s i false).1.val + 1, (s i false).2.val, (s i true).1.val + 1, (s i true).2.val]

def seedData (s : ECSeed p m) : List ℕ := (List.finRange m).flatMap (seedRow s)

end DetDLP.M3B.SlotOperands
end

section
set_option autoImplicit false
namespace DetDLP.M3B.SlotRows

open S8H0 RegisterMap NamedBlocks ECPolyDefs GateSemantics ECPhysicalNet ECArithBlock
open ECFits SlotFitCombinators SlotOperands
variable {p m k : ℕ} [Fact p.Prime]

theorem cat_assoc (a b c : ECPolyDefs.N) : cat (cat a b) c = cat a (cat b c) := by
  rcases a with ⟨ag,ae,af,asig,ac⟩
  rcases b with ⟨bg,be,bf,bsig,bc⟩
  rcases c with ⟨cg,ce,cf,csig,cc⟩
  dsimp only [cat,ng,ne,gate,signal,check]
  refine Prod.ext (Nat.add_assoc ..) (Prod.ext (Nat.add_assoc ..) (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · funext j
    by_cases h : j < ae
    · simp [h,show j < ae+be by omega]
    · by_cases h' : j < ae+be
      · simp [h,h',show j-ae < be by omega]
      · simp [h,h',show ¬ j-ae < be by omega,Nat.sub_sub,Nat.add_assoc]
  · funext j
    by_cases h : j < ae
    · simp [h,show j < ae+be by omega]
    · by_cases h' : j < ae+be
      · simp [h,h',show j-ae < be by omega]
      · simp [h,h',show ¬ j-ae < be by omega,Nat.sub_sub]
  · funext j
    by_cases h : j < ag
    · simp [h,show j < ag+bg by omega]
    · by_cases h' : j < ag+bg
      · simp [h,h',show j-ag < bg by omega]
      · simp [h,h',show ¬ j-ag < bg by omega,Nat.sub_sub]

end DetDLP.M3B.SlotRows
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainOffsets

open S8H0 RegisterMap GateRoutes GateSemantics ECMapRows ECChainBlocks ECPhysicalNet

def chainStart (p m k side : ℕ) :=
  4*m*ECPolyDefs.slotSize (d p) (e p) (busWidth p k)+side*ECPolyDefs.chainSize (d p) (e p) m

def mapStart (p m k side i : ℕ) :=
  chainStart p m k side+i*ECPolyDefs.mapSize (d p) (e p)

def addStart (p m k side i : ℕ) :=
  mapStart p m k side (2*m+1)+i*ECPolyDefs.addSize (d p) (e p)

def accumulator (p m k side i : ℕ) :=
  if i=0 then mapStart p m k side 0 else addStart p m k side (i-1)

theorem mapSize (d e : ℕ) : (mapShape d e).size = ECPolyDefs.mapSize d e := by
  simp only [mapShape,ECMapRows.slot,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,
    GateRoutes.auxShape,Shape.size,ECPolyDefs.mapSize,ECPolyDefs.gsize,ECPolyDefs.pt,
    ECPolyDefs.triple,ECPolyDefs.run,ECPolyDefs.aux]
  ring

theorem addSize (d e : ℕ) : (ECAddRows.addShape d e).size = ECPolyDefs.addSize d e := by
  simp only [ECAddRows.addShape,ECMapRows.slot,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,
    GateRoutes.auxShape,Shape.size,ECPolyDefs.addSize,ECPolyDefs.gsize,ECPolyDefs.pt,
    ECPolyDefs.triple,ECPolyDefs.run,ECPolyDefs.aux]
  ring

theorem chainSize (p m : ℕ) : (Chain p (2*m)).size = ECPolyDefs.chainSize (d p) (e p) m := by
  change (2*m+1)*(mapShape (d p) (e p)).size +
    (2*m)*(ECAddRows.addShape (d p) (e p)).size = _
  rw [mapSize,addSize]
  rfl

private theorem cellSize (p k : ℕ) :
    (SlotCell p k).size = ECPolyDefs.slotSize (d p) (e p) (busWidth p k) := by
  simp only [ECArithBlock.Sh,GateRoutes.S,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,
    bank,Shape.size,ECPolyDefs.slotSize,ECPolyDefs.bankSize,ECPolyDefs.triple,
    ECPolyDefs.pt,ECPolyDefs.run,ECPolyDefs.aux]
  ring

private theorem sideVal (s : Bool) : (sideIdx s).val = s.toNat := by cases s <;> rfl

theorem mapIndex {p m k : ℕ} (s : Bool) (i : Fin (2*m+1)) (a : Addr (mapShape (d p) (e p))) :
    (mapPath (chainPath (k := k) s) i a).index.val = mapStart p m k s.toNat i.val+a.index.val := by
  change (4*m)*(SlotCell p k).size+
    ((a.index.val+(mapShape (d p) (e p)).size*i.val)+(Chain p (2*m)).size*(sideIdx s).val) = _
  generalize a.index.val = n
  rw [cellSize,mapSize,chainSize,sideVal]
  unfold mapStart chainStart
  ring

theorem addIndex {p m k : ℕ} (s : Bool) (i : Fin (2*m)) (a : Addr (ECAddRows.addShape (d p) (e p))) :
    (addPath (chainPath (k := k) s) i a).index.val = addStart p m k s.toNat i.val+a.index.val := by
  change (4*m)*(SlotCell p k).size+
    (((2*m+1)*(mapShape (d p) (e p)).size+
      (a.index.val+(ECAddRows.addShape (d p) (e p)).size*i.val))+(Chain p (2*m)).size*(sideIdx s).val) = _
  generalize a.index.val = n
  rw [cellSize,mapSize,addSize,chainSize,sideVal]
  unfold addStart mapStart chainStart
  ring

theorem accumulatorIndex {p m k : ℕ} (s : Bool) (i : Fin (2*m+1)) (a : Addr (PointCell (d p))) :
    (acc (chainPath (k := k) s) i a).index.val = accumulator p m k s.toNat i.val+a.index.val := by
  induction i using Fin.cases with
  | zero =>
    change (mapPath (chainPath (k := k) s) 0 (.fst a)).index.val =
      mapStart p m k s.toNat 0+a.index.val
    exact mapIndex s 0 (.fst a)
  | succ i =>
    rw [acc, Fin.cases_succ]
    change (addPath (chainPath (k := k) s) i (.fst a)).index.val =
      (if i.val+1 = 0 then _ else addStart p m k s.toNat (i.val+1-1))+a.index.val
    rw [if_neg (by omega),Nat.add_sub_cancel]
    exact addIndex s i (.fst a)

theorem terminalIndex {p m k : ℕ} (a : Addr (PointCell (d p))) :
    (terminal (m := m) (k := k) a).index.val = chainStart p m k 2+a.index.val := by
  change (4*m)*(SlotCell p k).size+(2*(Chain p (2*m)).size+a.index.val) = _
  rw [cellSize,chainSize]
  unfold chainStart
  omega

end DetDLP.M3B.ChainOffsets
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainSubblocks

open S8H0 GateSemantics ECPhysicalNet ECChainBlocks ChainOffsets ECFits

def factor (p m k j : ℕ) : ECPolyDefs.XYZ :=
  let K := (ShapeOf p m k).size
  let o := j * ECPolyDefs.slotSize (d p) (e p) (busWidth p k)
  (ECPolyDefs.pin K false,(ECPolyDefs.ptw K (d p) o).2)

def numericInput (p m k : ℕ) (c : List ℕ) (side j : ℕ) : ECPolyDefs.XYZ :=
  let K := (ShapeOf p m k).size
  if j = 0 then
    if side = 1 then (ECPolyDefs.pin K true,ECPolyDefs.pub K 0,ECPolyDefs.pub K 0)
    else (ECPolyDefs.pin K (decide (c.getD 0 0 = 1)),ECPolyDefs.pub K (c.getD 1 0),
      ECPolyDefs.pub K (c.getD 2 0))
  else factor p m k (2*(j-1)+side)

def MapFits {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (m k : ℕ) (P : E.toAffine.Point) : Prop :=
  ∀ (side : Bool) (j : Fin (2*m+1)),
    let K := (ShapeOf p m k).size
    Fits (ECPolyDefs.mapN K p (d p) (e p) (mapStart p m k side.toNat j.val)
      (numericInput p m k (pointCoords P) side.toNat j.val))
      (mapAt E (chainPath (m := m) (k := k) side) (chainIn (k := k) E P side) j)

def AddFits {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (m k : ℕ) : Prop :=
  ∀ (side : Bool) (j : Fin (2*m)),
    let K := (ShapeOf p m k).size
    Fits (ECPolyDefs.addN K p (d p) (e p) (addStart p m k side.toNat j.val)
      ((1296*E.a₄.val)%p) (ECPolyDefs.ptw K (d p) (accumulator p m k side.toNat j.val))
      (ECPolyDefs.ptw K (d p) (mapStart p m k side.toNat (j.val+1))))
      (addAt E (chainPath (m := m) (k := k) side) j)

end DetDLP.M3B.ChainSubblocks
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainRouting

open S8H0 RegisterMap NamedBlocks GateRoutes ECMapRows ECPhysicalNet ECChainBlocks
open ECFits SlotFitCombinators

def Packed {s u : Shape} (path : Path u s) (off : ℕ) : Prop :=
  ∀ j, (path j).index.val = off+j.index.val

def WordFits {s : Shape} (a : ECPolyDefs.Word) (r : HashRows.Word s) : Prop :=
  ∀ j, a j = EBit (r j)

theorem Packed.first {s u v : Shape} {f : Path (.pair u v) s} {o : ℕ} (h : Packed f o) :
    Packed (fstP f) o := fun j => h (.fst j)

theorem Packed.second {s u v : Shape} {f : Path (.pair u v) s} {o : ℕ} (h : Packed f o) :
    Packed (sndP f) (o+u.size) := by
  intro j
  exact (h (.snd j)).trans (Nat.add_assoc ..).symm

theorem Packed.entry {s u : Shape} {n o : ℕ} {f : Path (.vec n u) s} (h : Packed f o) (i : Fin n) :
    Packed (fun j => f (.vec i j)) (o+i.val*u.size) := by
  intro j
  have H := h (.vec i j)
  change _ = o+(j.index.val+u.size*i.val) at H
  rw [H]
  ring

theorem Packed.reg {s u : Shape} {off : ℕ} {f : Path u s} (h : Packed f off)
    (a : Addr u) {n : ℕ} (hn : n=off+a.index.val) :
    ECPolyDefs.reg n = EBit (.reg (f a)) := congrArg ECPolyDefs.reg (hn.trans (h a).symm)

theorem Packed.word {s : Shape} {n off : ℕ} {f : Path (.word n) s} (h : Packed f off) :
    WordFits (ECPolyDefs.word s.size off n) (GateRoutes.word f) := by
  intro j
  unfold ECPolyDefs.word GateRoutes.word HashRows.padded
  by_cases hj : j < n
  · rw [if_pos hj,dif_pos hj]
    exact h.reg (.word ⟨j,hj⟩) rfl
  · rw [if_neg hj,dif_neg hj]
    rfl

theorem Packed.wordAt {s : Shape} {n a b : ℕ} {f : Path (.word n) s} (h : Packed f a) (hab : a=b) :
    WordFits (ECPolyDefs.word s.size b n) (GateRoutes.word f) := hab ▸ h.word

theorem Packed.mask {s u : Shape} {base : ℕ} {f : Path u s} (h : Packed f base)
    (a : Addr u) (b : Bool) {n : ℕ} (hn : n=base+a.index.val) :
    ECPolyDefs.mask n b = EBit (.masked b (f a)) := by
  rw [hn,← h a]
  cases b <;> rfl

theorem pub {s : Shape} (t : ℕ) : WordFits (s := s) (ECPolyDefs.pub s.size t) (HashRows.pub t) := fun _ => rfl

theorem bound {s : Shape} {d t : ℕ} (p : ℕ) (f : Path (RegisterMap.triple d) s) (h : Packed f t) :
    Fits (ECPolyDefs.bnd s.size p d t) (RangeRows.checker p f) := by
  apply colM
  · exact fun j => h.first.word j.val
  · exact fun j => h.second.first.word j.val
  · exact fun _ => rfl
  · intro j
    apply h.reg (.snd (.snd (.word j)))
    change t+2*d+j.val = t+(d+(d+j.val))
    omega

theorem pointBounds {s : Shape} {d t : ℕ} (p : ℕ) (f : Path (PointCell d) s) (h : Packed f t) :
    Fits (ECPolyDefs.pbound s.size p d t)
      (joinB (RangeRows.checker p (fstP (sndP f))) (RangeRows.checker p (sndP (sndP f)))) := by
  apply joinM (bound p _ h.second.first)
  apply bound p
  have H := h.second.second
  have sz : (RegisterMap.triple d).size = ECPolyDefs.triple d := by
    simp only [RegisterMap.triple,Shape.size,ECPolyDefs.triple]
    omega
  rw [← sz]
  exact H

theorem gateBounds {s : Shape} {d e t : ℕ} (p : ℕ) (f : Path (ECMapRows.slot d e) s) (h : Packed f t) :
    Fits (ECPolyDefs.gbound s.size p d t)
      (joinB (RangeRows.checker p (result f)) (RangeRows.checker p (remain f))) := by
  apply joinM (bound p _ h.first.first)
  apply bound p
  have H := h.first.second.first.first
  have sz : (RegisterMap.triple d).size = ECPolyDefs.triple d := by
    simp only [RegisterMap.triple,Shape.size,ECPolyDefs.triple]
    omega
  rw [← sz]
  exact H

theorem pointWords {s : Shape} {d t : ℕ} (f : Path (PointCell d) s) (h : Packed f t) :
    (ECPolyDefs.ptw s.size d t).1 = EBit (pointWires f).1 ∧
    WordFits (ECPolyDefs.ptw s.size d t).2.1 (pointWires f).2.1 ∧
    WordFits (ECPolyDefs.ptw s.size d t).2.2 (pointWires f).2.2 := by
  have y := h.second.second.first.word
  have sz : (RegisterMap.triple d).size = ECPolyDefs.triple d := by
    simp only [RegisterMap.triple,Shape.size,ECPolyDefs.triple]
    omega
  refine ⟨h.reg (.fst .bit) (Nat.add_zero _).symm,h.second.first.first.word,?_⟩
  change WordFits (ECPolyDefs.word s.size (t+1+ECPolyDefs.triple d) d) _
  rw [← sz]
  exact y

end DetDLP.M3B.ChainRouting
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainGate

open S8H0 RegisterMap NamedBlocks ECMapRows GateRoutes ECFits SlotFitCombinators ChainRouting

def counts (d : ℕ) : ℕ × ℕ :=
  let mul := S8H.PointAddresses.mul d
  let g := mul.ng+4*d
  let e := mul.ne+4*d*2
  (g+g+(2*d+((d+1)+(d+1))),e+e+(2*d*5+((d+1)*5+(d+1)*5)))

theorem sizes (K p d e t : ℕ) (a : ECPolyDefs.Word × ECPolyDefs.Word × ECPolyDefs.Word) :
    ECPolyDefs.ng (ECPolyDefs.ghash K p d e t a) = (counts d).1 ∧
    ECPolyDefs.ne (ECPolyDefs.ghash K p d e t a) = (counts d).2 := ⟨rfl,rfl⟩

private theorem multiply {s : Shape} {d K t : ℕ} (hd : 1 ≤ d) {a b z : ECPolyDefs.Word}
    {A B Z : HashRows.Word s} {R : Fin (w3_fpMulLayout d hd).nb → Ref s}
    (hr : ∀ j, ECPolyDefs.reg (t+j.val) = EBit (R j))
    (ha : WordFits a A) (hb : WordFits b B) (hz : WordFits z Z) :
    Fits (ECPolyDefs.prod K d t a b z) (HashRows.product hd A B Z R) := by
  obtain ⟨hg,he,hj,hk⟩ := m3b_ec_multiplier_agreement (K := K) hd a b z A B Z R hr ha hb hz
  exact ⟨hg,he,fun j => (hj j).1,fun j => (hj j).2,hk⟩

/-- A contiguous run followed by its auxiliary words gives exactly the numeric hash block. -/
theorem gateFits {s : Shape} {p d e t : ℕ} {hd : 1 ≤ d}
    (width : (w4_M5GraphBounds.graph d hd).nE ≤ e)
    (f : Path (ECMapRows.slot d e) s) (h : Packed f t)
    {a x b : ECPolyDefs.Word} {A X B : HashRows.Word s}
    (ha : WordFits a A) (hx : WordFits x X) (hb : WordFits b B) :
    Fits (ECPolyDefs.ghash s.size p d e t (a,x,b)) (ECMapRows.slotBlock hd p A X B f) := by
  let rem := t+ECPolyDefs.triple d
  let q := rem+ECPolyDefs.triple d
  let u := q+d
  let v := u+2*d+e
  let ax := t+ECPolyDefs.run d e
  let w := gw hd p A X B f
  have r1 (j : Fin (w3_fpMulLayout d hd).nb) : ECPolyDefs.reg (u+2*d+j.val) = EBit (w.mul1 j) := by
    dsimp only [w,gw]
    rw [RangeRows.pad,dif_pos (j.isLt.trans_le width)]
    apply h.reg
    dsimp only [u,q,rem]
    dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]
    omega
  have r2 (j : Fin (w3_fpMulLayout d hd).nb) : ECPolyDefs.reg (v+2*d+j.val) = EBit (w.mul2 j) := by
    dsimp only [w,gw]
    rw [RangeRows.pad,dif_pos (j.isLt.trans_le width)]
    apply h.reg
    dsimp only [v,u,q,rem]
    dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]
    omega
  have p1 : WordFits (ECPolyDefs.word s.size u (2*d)) w.prod1 :=
    h.first.second.first.second.second.first.first.wordAt (by dsimp only [u,q,rem]; dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]; omega)
  have p2 : WordFits (ECPolyDefs.word s.size v (2*d)) w.prod2 :=
    h.first.second.first.second.second.second.first.wordAt (by dsimp only [v,u,q,rem]; dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]; omega)
  have qo : WordFits (ECPolyDefs.word s.size q d) w.quot :=
    h.first.second.first.second.first.wordAt (by dsimp only [q,rem]; dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]; omega)
  have re : WordFits (ECPolyDefs.word s.size rem d) w.rem :=
    h.first.second.first.first.first.wordAt (by dsimp only [rem]; dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]; omega)
  have z : WordFits (ECPolyDefs.word s.size t d) w.z := h.first.first.first.word
  have su : WordFits (ECPolyDefs.word s.size (ax+2*d) (d+1)) w.sum :=
    h.second.second.first.wordAt (by dsimp only [ax]; dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]; omega)
  have cp (j : ℕ) : ECPolyDefs.mask (v+2*d+e) (p.testBit j) = EBit (w.cp j) := by
    apply h.mask
    dsimp only [v,u,q,rem]
    dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]
    omega
  have c1 (j : Fin (2*d)) : ECPolyDefs.reg (ax+j.val) = EBit (w.carry1 j) := by
    apply h.reg
    dsimp only [ax]
    dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]
    omega
  have c2 (j : Fin (d+1)) : ECPolyDefs.reg (ax+3*d+1+j.val) = EBit (w.carry2 j) := by
    apply h.reg
    dsimp only [ax]
    dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]
    omega
  have c3 (j : Fin (d+1)) : ECPolyDefs.reg (ax+4*d+2+j.val) = EBit (w.carry3 j) := by
    apply h.reg
    dsimp only [ax]
    dsimp only [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.run,RegisterMap.mul,RegisterMap.triple,GateRoutes.auxShape,ECPolyDefs.run,ECPolyDefs.triple,Fin.val_zero]
    omega
  rw [ECMapRows.slotBlock,if_pos width]
  exact joinM (joinM (multiply hd r1 ha hx p1) (multiply hd r2 qo (fun _ => rfl) p2))
    (joinM (colM false (fun j => p2 j) (fun j => re j) (fun j => p1 j) c1)
      (joinM (colM false (fun j => re j) (fun j => hb j) (fun j => su j) c2)
        (colM false (fun j => z j) (fun j => cp j) (fun j => su j) c3)))

end DetDLP.M3B.ChainGate
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainMapInputs

open S8H0 RegisterMap NamedBlocks GateRoutes GateSemantics ECMapRows ECChainBlocks ECPhysicalNet
open ChainRouting ChainSubblocks ECFits

def PointFits {s : Shape} (a : ECPolyDefs.XYZ) (q : Wires s) : Prop :=
  a.1 = EBit q.1 ∧ WordFits a.2.1 q.2.1 ∧ WordFits a.2.2 q.2.2

theorem factorInput {p m k : ℕ} (side : Bool) (i : Fin (2*m)) :
    PointFits (factor p m k (2*i.val+side.toNat)) (factorWires (p := p) (k := k) side i) := by
  let D := d p
  let idx := ix side i
  let f : Path (PointCell D) (ShapeOf p m k) := fun u => ECPhysicalNet.slot idx (.fst u)
  let t := (2*i.val+side.toNat)*ECPolyDefs.slotSize D (e p) (busWidth p k)
  have h : Packed f t := by
    intro a
    change a.index.val+(SlotCell p k).size*(2*i.val+side.toNat) = t+a.index.val
    have sz : (SlotCell p k).size = ECPolyDefs.slotSize D (e p) (busWidth p k) := by
      simp only [D,ECArithBlock.Sh,GateRoutes.S,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,
        bank,Shape.size,ECPolyDefs.slotSize,ECPolyDefs.bankSize,ECPolyDefs.triple,
        ECPolyDefs.pt,ECPolyDefs.run,ECPolyDefs.aux]
      ring
    generalize a.index.val = n
    rw [sz]
    unfold t
    ring
  exact ⟨rfl,(pointWords f h).2.1,(pointWords f h).2.2⟩

theorem mapInput {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (P : E.toAffine.Point)
    (side : Bool) (j : Fin (2*m+1)) :
    PointFits (numericInput p m k (pointCoords P) side.toNat j.val) (chainIn (k := k) E P side j) := by
  induction j using Fin.cases with
  | zero =>
    have hz : WordFits (s := ShapeOf p m k) (ECPolyDefs.pub (ShapeOf p m k).size 0)
        (HashRows.pub (0 : ZMod p).val) := by
      rw [ZMod.val_zero]
      exact ChainRouting.pub 0
    cases side <;> cases P <;> first
      | exact ⟨rfl,hz,hz⟩
      | exact ⟨rfl,fun _ => rfl,fun _ => rfl⟩
  | succ i =>
    simp only [numericInput,Fin.val_succ,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel,chainIn,Fin.cases_succ]
    exact factorInput side i

end DetDLP.M3B.ChainMapInputs
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainPointRows

open S8H0 RegisterMap NamedBlocks GateRoutes ECMapRows ECChainBlocks ECFits SlotFitCombinators

private theorem splitRows (n m : ℕ) (a b : ECPolyDefs.Word) :
    ECPolyDefs.eqs (n+m) a b = ECPolyDefs.cat (ECPolyDefs.eqs n a b)
      (ECPolyDefs.eqs m (fun j => a (n+j)) (fun j => b (n+j))) := by
  refine Prod.ext rfl (Prod.ext (Nat.add_mul ..) (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · funext j
    change j/2 = if j < n*2 then j/2 else n+(j-n*2)/2
    split <;> omega
  · funext j
    let sig := fun (h i : ℕ) => (if h=0 then a i else b i).1
    change sig (j%2) (j/2) = if j < n*2 then sig (j%2) (j/2)
      else sig ((j-n*2)%2) (n+(j-n*2)/2)
    by_cases hj : j < n*2
    · rw [if_pos hj]
    · rw [if_neg hj,show n+(j-n*2)/2=j/2 by omega,show (j-n*2)%2=j%2 by omega]
  · funext j
    let test := fun (i : ℕ) (l : List Bool) => ECPolyDefs.rd (a i) (l.getD 0 false) ==
      ECPolyDefs.rd (b i) (l.getD 1 false)
    change test j = if j < n then test j else test (n+(j-n))
    by_cases hj : j < n
    · rw [if_pos hj]
    · rw [if_neg hj,show n+(j-n)=j by omega]

def Compares {s u : Shape} (f g : Path u s) (block : B (s.size+1)) : Prop :=
  ∀ (a b : ECPolyDefs.Word),
    (∀ j : Addr u, a j.index.val = EBit (.reg (f j))) →
    (∀ j : Addr u, b j.index.val = EBit (.reg (g j))) →
    Fits (ECPolyDefs.eqs u.size a b) block

private theorem pairRows {s u v : Shape} {f g : Path (.pair u v) s} {x y : B (s.size+1)}
    (hx : Compares (fstP f) (fstP g) x) (hy : Compares (sndP f) (sndP g) y) :
    Compares f g (joinB x y) := by
  intro a b ha hb
  change Fits (ECPolyDefs.eqs (u.size+v.size) a b) _
  rw [splitRows]
  exact joinM (hx a b (fun j => ha (.fst j)) (fun j => hb (.fst j)))
    (hy _ _ (fun j => ha (.snd j)) (fun j => hb (.snd j)))

private theorem bitRows {s : Shape} (f g : Path .bit s) :
    Compares f g (NamedBlocks.eqs 1 (fun _ => .reg (f .bit)) (fun _ => .reg (g .bit))) := by
  intro a b ha hb
  apply eqM
  · intro j; obtain rfl := Fin.eq_zero j; exact ha .bit
  · intro j; obtain rfl := Fin.eq_zero j; exact hb .bit

private theorem wordRows {s : Shape} {n : ℕ} (f g : Path (.word n) s) :
    Compares f g (wordEqB f g) := by
  intro a b ha hb
  exact eqM (fun j => ha (.word j)) (fun j => hb (.word j))

private theorem tripleRows {s : Shape} {d : ℕ} (f g : Path (triple d) s) :
    Compares f g (tripleEq f g) :=
  pairRows (wordRows _ _) (pairRows (wordRows _ _) (wordRows _ _))

theorem pointRows {s : Shape} {d : ℕ} (f g : Path (PointCell d) s) :
    Compares f g (pointEq f g) :=
  pairRows (bitRows _ _) (pairRows (tripleRows _ _) (tripleRows _ _))

theorem pointSize (d : ℕ) : (PointCell d).size = ECPolyDefs.pt d := by
  simp only [RegisterMap.triple,Shape.size,ECPolyDefs.pt,ECPolyDefs.triple]
  omega

/-- Compare every bit of two packed points, including both complementary values and both carry words. -/
theorem fitsAt {s : Shape} {d : ℕ} (f g : Path (PointCell d) s) (left right : ℕ)
    (hl : ∀ j, (f j).index.val = left+j.index.val)
    (hr : ∀ j, (g j).index.val = right+j.index.val) :
    Fits (ECPolyDefs.eqs (ECPolyDefs.pt d)
      (ECPolyDefs.word s.size left (ECPolyDefs.pt d)) (ECPolyDefs.word s.size right (ECPolyDefs.pt d)))
      (pointEq f g) := by
  have packed (off : ℕ) (path : Path (PointCell d) s)
      (h : ∀ j, (path j).index.val = off+j.index.val) (j : Addr (PointCell d)) :
      ECPolyDefs.word s.size off (ECPolyDefs.pt d) j.index.val = EBit (.reg (path j)) := by
    unfold ECPolyDefs.word
    rw [if_pos (j.index.isLt.trans_eq (pointSize d))]
    exact congrArg ECPolyDefs.reg (h j).symm
  simpa only [pointSize] using pointRows f g _ _ (packed left f hl) (packed right g hr)

end DetDLP.M3B.ChainPointRows
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainTerminalFits

open S8H0 GateSemantics ECPhysicalNet ECChainBlocks ChainOffsets ECFits

/-- The last accumulator and the shared terminal point agree at every checked row,
    for either side, including the zero-length addition chain. -/
theorem fits (p m k : ℕ) (s : Bool) :
    let K := (ShapeOf p m k).size
    let D := d p
    Fits (ECPolyDefs.eqs (ECPolyDefs.pt D)
      (ECPolyDefs.word K (accumulator p m k s.toNat (2*m)) (ECPolyDefs.pt D))
      (ECPolyDefs.word K (chainStart p m k 2) (ECPolyDefs.pt D)))
      (pointEq (acc (chainPath (k := k) s) (Fin.last (2*m))) (terminal (p := p) (k := k))) :=
  ChainPointRows.fitsAt _ _ _ _ (accumulatorIndex s (Fin.last (2*m))) terminalIndex

end DetDLP.M3B.ChainTerminalFits
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainAssembly

open S8H0 GateSemantics ECPhysicalNet ECChainBlocks ECFits ChainSubblocks ChainOffsets SlotFitCombinators
open ECPolyDefs

private def emptyPoint : XYZ := (reg 0,pub 0 0,pub 0 0)
private def mapTemplate (d : ℕ) := mapN 0 0 d 0 0 emptyPoint
private def addTemplate (d : ℕ) := addN 0 0 d 0 0 0 emptyPoint emptyPoint

private theorem mapCounts (K p d e t : ℕ) (q : XYZ) :
    ng (mapN K p d e t q) = ng (mapTemplate d) ∧ ne (mapN K p d e t q) = ne (mapTemplate d) := by
  dsimp only [mapTemplate,mapN,cat,copies,pbound,gbound,bnd,ghash,ECPolyDefs.hash,prod,eqs,col,rows,ng,ne]
  exact ⟨rfl,rfl⟩

private theorem addCounts (K p d e t c : ℕ) (q r : XYZ) :
    ng (addN K p d e t c q r) = ng (addTemplate d) ∧ ne (addN K p d e t c q r) = ne (addTemplate d) := by
  dsimp only [addTemplate,addN,cat,copies,pbound,gbound,bnd,ghash,ECPolyDefs.hash,prod,eqs,col,rows,ng,ne]
  exact ⟨rfl,rfl⟩

def compiledChain (p m k side : ℕ) (coords : List ℕ) (c4 : ℕ) :=
  let K := (ShapeOf p m k).size
  let d := GateSemantics.d p
  let e := GateSemantics.e p
  let maps := fun j => mapN K p d e (mapStart p m k side j) (numericInput p m k coords side j)
  let adds := fun j => addN K p d e (addStart p m k side j) c4
    (ptw K d (accumulator p m k side j)) (ptw K d (mapStart p m k side (j+1)))
  cat (copies (2*m+1) maps) (cat (copies (2*m) adds)
    (eqs (pt d) (word K (accumulator p m k side (2*m)) (pt d)) (word K (chainStart p m k 2) (pt d))))

/-- One map fit and one addition fit per position suffice for either entire arithmetic chain. -/
theorem ofSubblocks {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (P : E.toAffine.Point)
    (hm : MapFits E m k P) (ha : AddFits E m k) (side : Bool) :
    Fits (compiledChain p m k side.toNat (pointCoords P) ((1296*E.a₄.val)%p))
      (sideBlock (m := m) (k := k) E P side) := by
  let D := d p
  let K := (ShapeOf p m k).size
  let maps := fun j => mapN K p D (e p) (mapStart p m k side.toNat j)
    (numericInput p m k (pointCoords P) side.toNat j)
  let adds := fun j => addN K p D (e p) (addStart p m k side.toNat j) ((1296*E.a₄.val)%p)
    (ptw K D (accumulator p m k side.toNat j)) (ptw K D (mapStart p m k side.toNat (j+1)))
  have hmg (j : ℕ) : ng (maps j) = ng (mapTemplate D) ∧ ne (maps j) = ne (mapTemplate D) := mapCounts ..
  have hag (j : ℕ) : ng (adds j) = ng (addTemplate D) ∧ ne (adds j) = ne (addTemplate D) := addCounts ..
  have mapsFit := manyM (2*m+1) _ _ maps (mapAt E (chainPath (k := k) side) (chainIn (k := k) E P side))
    (hm side) (fun j => (hmg j).1) (fun j => (hmg j).2)
  have addsFit := manyM (2*m) _ _ adds (addAt E (chainPath (k := k) side))
    (ha side) (fun j => (hag j).1) (fun j => (hag j).2)
  exact joinM mapsFit (joinM addsFit (ChainTerminalFits.fits p m k side))

end DetDLP.M3B.ChainAssembly
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainMapBlock

open S8H0 RegisterMap NamedBlocks GateRoutes ECMapRows ECChainBlocks ECFits SlotFitCombinators
open ChainRouting ChainMapInputs

def gatePath {s : Shape} {d e : ℕ} (f : Path (mapShape d e) s) (g : Fin 4) :
    Path (ECMapRows.slot d e) s := fun a => f (.snd (.vec g a))

theorem gateIndex {s : Shape} {d e t : ℕ} {f : Path (mapShape d e) s} (h : Packed f t) (g : Fin 4) :
    Packed (gatePath f g) (t+ECPolyDefs.pt d+g.val*ECPolyDefs.gsize d e) := by
  have sz : (ECMapRows.slot d e).size = ECPolyDefs.gsize d e := by
    simp only [RegisterMap.run,RegisterMap.mul,RegisterMap.triple,Shape.size,GateRoutes.auxShape,
      ECPolyDefs.gsize,ECPolyDefs.run,ECPolyDefs.aux,ECPolyDefs.triple]
    omega
  rw [← ChainPointRows.pointSize,← sz]
  exact h.second.entry g

private theorem maskFits {s : Shape} {d : ℕ} {z o : ECPolyDefs.Word} {Z O : HashRows.Word s}
    {b : ECPolyDefs.Bit} {r : Ref s} (hb : b = EBit r) (ho : WordFits o O) (hz : WordFits z Z) :
    Fits (ECPolyDefs.rows d 3 (fun j i => match i with | 0 => b | 1 => o j | _ => z j)
      (fun _ v => v 1 == (!v 0 && v 2)))
      (NamedBlocks.rows d 3 (fun j => ![r,O j,Z j]) (fun _ v => v 1 == (!v 0 && v 2))) := by
  apply rowM
  · intro i j
    fin_cases j
    · exact hb
    · exact ho i
    · exact hz i
  · intro i v
    rfl

/-- Arithmetic and routing agreement for a short-Weierstrass conversion block. -/
theorem fits {s : Shape} {d e t p : ℕ} (hd : 1 ≤ d) (width : (w4_M5GraphBounds.graph d hd).nE ≤ e)
    (f : Path (mapShape d e) s) (h : Packed f t) (q : ECPolyDefs.XYZ) (Q : ECChainBlocks.Wires s)
    (hq : PointFits q Q) :
    Fits (ECPolyDefs.mapN s.size p d e t q) (ECMapRows.mapBlock hd p 0 0 0 Q.1 Q.2.1 Q.2.2 f) := by
  let off := fun g => t+ECPolyDefs.pt d+g*ECPolyDefs.gsize d e
  let z := fun g => ECPolyDefs.word s.size (off g) d
  let Z := fun g => rwrd (result (gatePath f g))
  let args : ℕ → ECPolyDefs.Word × ECPolyDefs.Word × ECPolyDefs.Word := fun g => match g with
    | 0 => (ECPolyDefs.pub s.size (36%p),q.2.1,ECPolyDefs.pub s.size 0)
    | 1 => (ECPolyDefs.pub s.size 0,q.2.1,ECPolyDefs.pub s.size 0)
    | 2 => (ECPolyDefs.pub s.size (2%p),q.2.2,z 1)
    | _ => (ECPolyDefs.pub s.size (108%p),z 2,ECPolyDefs.pub s.size 0)
  let argsP : Fin 4 → HashRows.Word s × HashRows.Word s × HashRows.Word s :=
    ![(HashRows.pub (36%p),Q.2.1,HashRows.pub (3*0%p)),(HashRows.pub 0,Q.2.1,HashRows.pub 0),
      (HashRows.pub (2%p),Q.2.2,Z 1),(HashRows.pub (108%p),Z 2,HashRows.pub 0)]
  have outs (g : Fin 4) : WordFits (z g.val) (Z g) := (gateIndex h g).first.first.first.word
  have inputs (g : Fin 4) : WordFits (args g.val).1 (argsP g).1 ∧
      WordFits (args g.val).2.1 (argsP g).2.1 ∧ WordFits (args g.val).2.2 (argsP g).2.2 := by
    fin_cases g
    · refine ⟨ChainRouting.pub _,hq.2.1,?_⟩
      change WordFits (ECPolyDefs.pub s.size 0) (HashRows.pub (3*0%p))
      rw [Nat.mul_zero,Nat.zero_mod]
      exact ChainRouting.pub _
    · exact ⟨ChainRouting.pub _,hq.2.1,ChainRouting.pub _⟩
    · exact ⟨ChainRouting.pub _,hq.2.2,outs 1⟩
    · exact ⟨ChainRouting.pub _,outs 2,ChainRouting.pub _⟩
  let ranges := fun g => ECPolyDefs.gbound s.size p d (off g)
  let rangeP := fun g : Fin 4 => joinB (RangeRows.checker p (result (gatePath f g)))
    (RangeRows.checker p (remain (gatePath f g)))
  have rg : Fits (ECPolyDefs.copies 4 ranges) (RangeRows.many 3 rangeP) := by
    refine many1M 3 ((d+1)+(d+1)) ((d+1)*5+(d+1)*5) ranges rangeP
      (fun g => gateBounds p _ (gateIndex h g)) (fun _ => rfl) (fun _ => rfl)
  let gates := fun g => ECPolyDefs.ghash s.size p d e (off g) (args g)
  let gateP := fun g : Fin 4 => ECMapRows.slotBlock hd p (argsP g).1 (argsP g).2.1 (argsP g).2.2 (gatePath f g)
  have gatesFit : Fits (ECPolyDefs.copies 4 gates) (RangeRows.many 3 gateP) := by
    refine many1M 3 (ChainGate.counts d).1 (ChainGate.counts d).2 gates gateP ?_
      (fun g => (ChainGate.sizes s.size p d e (off g) (args g)).1)
      (fun g => (ChainGate.sizes s.size p d e (off g) (args g)).2)
    intro g
    exact ChainGate.gateFits width _ (gateIndex h g) (inputs g).1 (inputs g).2.1 (inputs g).2.2
  have op := pointWords (fstP f) h.first
  exact joinM (joinM (pointBounds p (fstP f) h.first) rg)
    (joinM gatesFit (joinM (eqM (fun _ => op.1) (fun _ => hq.1))
      (joinM (maskFits hq.1 op.2.1 (outs 0)) (maskFits hq.1 op.2.2 (outs 3)))))

end DetDLP.M3B.ChainMapBlock
end

section
set_option autoImplicit false
open DetDLP DetDLP.M3B S8H0 GateSemantics ECPhysicalNet ECChainBlocks ECFits

private theorem DetDLP.bodyChainMapFits (p m k : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (ha₁ : E.a₁=0) (ha₂ : E.a₂=0) (ha₃ : E.a₃=0) (P : E.toAffine.Point) :
    ChainSubblocks.MapFits E m k P := by
  intro side j
  let q := ChainSubblocks.numericInput p m k (pointCoords P) side.toNat j.val
  let Q := chainIn (m := m) (k := k) E P side j
  let f := mapPath (chainPath (p := p) (m := m) (k := k) side) j
  let t := ChainOffsets.mapStart p m k side.toNat j.val
  change Fits (ECPolyDefs.mapN (ShapeOf p m k).size p (d p) (e p) t q)
    (ECMapRows.mapBlock (hd p) p E.b₂.val E.a₁.val E.a₃.val Q.1 Q.2.1 Q.2.2 f)
  have hb : E.b₂ = 0 := by simp [WeierstrassCurve.b₂,ha₁,ha₂]
  rw [hb,ha₁,ha₃,ZMod.val_zero]
  apply ChainMapBlock.fits (hd p) (Nat.le_refl _) f (ChainOffsets.mapIndex side j) q Q
  exact ChainMapInputs.mapInput E P side j
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainAddPaths

open S8H0 RegisterMap GateRoutes ECMapRows ECChainBlocks ECPhysicalNet ChainRouting

abbrev Ctrl (d : ℕ) := Shape.pair .bit (RegisterMap.triple d)
abbrev control {s : Shape} {d e : ℕ} (f : Path (ECAddRows.addShape d e) s) (j : Fin 2) :
    Path (Ctrl d) s := fun a => f (.snd (.fst (.vec j a)))
abbrev slope {s : Shape} {d e : ℕ} (f : Path (ECAddRows.addShape d e) s) :
    Path (.word d) s := fun a => f (.snd (.snd (.fst a)))
abbrev gate {s : Shape} {d e : ℕ} (f : Path (ECAddRows.addShape d e) s) (j : Fin 15) :
    Path (ECMapRows.slot d e) s := fun a => f (.snd (.snd (.snd (.vec j a))))

def ctrlOff (t d j : ℕ) := t+ECPolyDefs.pt d+j*(1+ECPolyDefs.triple d)
def gateOff (t d e j : ℕ) := ctrlOff t d 2+d+j*ECPolyDefs.gsize d e

private theorem ctrlSize (d : ℕ) : (Ctrl d).size = 1+ECPolyDefs.triple d := by
  simp only [Shape.size,RegisterMap.triple,ECPolyDefs.triple]
  omega

private theorem slotSize (d e : ℕ) : (ECMapRows.slot d e).size = ECPolyDefs.gsize d e := by
  simp only [Shape.size,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,GateRoutes.auxShape,
    ECPolyDefs.gsize,ECPolyDefs.triple,ECPolyDefs.run,ECPolyDefs.aux]
  omega

theorem ctrlIndex {s : Shape} {d e t : ℕ} {f : Path (ECAddRows.addShape d e) s}
    (h : Packed f t) (i : Fin 2) : Packed (control f i) (ctrlOff t d i.val) := by
  unfold ctrlOff
  rw [← ChainPointRows.pointSize,← ctrlSize]
  exact h.second.first.entry i

theorem slopeIndex {s : Shape} {d e t : ℕ} {f : Path (ECAddRows.addShape d e) s}
    (h : Packed f t) : Packed (slope f) (ctrlOff t d 2) := by
  unfold ctrlOff
  rw [← ChainPointRows.pointSize,← ctrlSize]
  exact h.second.second.first

theorem gateIndex {s : Shape} {d e t : ℕ} {f : Path (ECAddRows.addShape d e) s}
    (h : Packed f t) (i : Fin 15) : Packed (gate f i) (gateOff t d e i.val) := by
  unfold gateOff ctrlOff
  rw [← ChainPointRows.pointSize,← ctrlSize,← slotSize]
  exact h.second.second.second.entry i

theorem coefficients {p : ℕ} [Fact p.Prime] (hp : 3 < p) (E : WeierstrassCurve (ZMod p))
    (h₁ : E.a₁=0) (h₂ : E.a₂=0) (h₃ : E.a₃=0) :
    (-1 : ZMod p).val = p-1 ∧ (1 : ZMod p).val = 1 ∧ (3 : ZMod p).val = 3 ∧
      (-27*E.c₄).val = (1296*E.a₄.val)%p := by
  have hn : (-1 : ZMod p).val = p-1 := by
    cases p with
    | zero => omega
    | succ q => exact ZMod.val_neg_one q
  have hc : -27*E.c₄ = (↑(1296*E.a₄.val) : ZMod p) := by
    simp only [WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄,h₁,h₂,h₃,
      Nat.cast_mul,ZMod.natCast_zmod_val]
    push_cast
    ring
  refine ⟨hn,?_,?_,hc ▸ ZMod.val_natCast ..⟩
  · rw [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (by omega)]
  · exact ZMod.val_natCast_of_lt hp

end DetDLP.M3B.ChainAddPaths
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainAddRows

open S8H0 RegisterMap NamedBlocks GateRoutes ECMapRows ECFits SlotFitCombinators ChainRouting

def args {α : Type} (minus one three c zero x y z w bx by' l : α) (g : Fin 15 → α) :
    ℕ → α × α × α
  | 0 => (minus,x,z)
  | 1 => (g 0,bx,zero)
  | 2 => (one,y,w)
  | 3 => (g 2,by',zero)
  | 4 => (minus,y,w)
  | 5 => (g 4,bx,zero)
  | 6 => (x,x,zero)
  | 7 => (three,g 6,c)
  | 8 => (g 7,by',zero)
  | 9 => (l,l,zero)
  | 10 => (minus,x,g 9)
  | 11 => (minus,z,g 10)
  | 12 => (minus,g 11,x)
  | 13 => (l,g 12,zero)
  | _ => (minus,y,g 13)

def invN (d : ℕ) (b : ECPolyDefs.Bit) (u a v one : ECPolyDefs.Word) :=
  ECPolyDefs.rows d 5 (fun k h => match h with | 0 => b | 1 => u k | 2 => a k | 3 => v k | _ => one k)
    (fun _ z => if z 0 then !z 1 && !z 2 else z 3 == z 4)

theorem invFits {s : Shape} {d : ℕ} {b : ECPolyDefs.Bit} {B : Ref s} (hb : b = EBit B)
    {u a v one : ECPolyDefs.Word} {U A V O : HashRows.Word s}
    (hu : WordFits u U) (ha : WordFits a A) (hv : WordFits v V) (ho : WordFits one O) :
    Fits (invN d b u a v one) (NamedBlocks.rows d 5 (fun i => ![B,U i,A i,V i,O i])
      (fun _ z => if z 0 then !z 1 && !z 2 else z 3 == z 4)) := by
  apply rowM
  · intro i j
    fin_cases j
    · exact hb
    · exact hu i
    · exact ha i
    · exact hv i
    · exact ho i
  · intro i z; rfl

def choose (pitch i j b c y z u v : Bool) :=
  if pitch then if !i && !j && !b then y else if !i && !j && b && !c then z else u
  else if i then y else if j then z else if b && c then u else v

def branchN (n : ℕ) (pitch : Bool) (i j b c : ECPolyDefs.Bit) (o y z u v : ECPolyDefs.Word) :=
  ECPolyDefs.rows n 9 (fun k h => match h with
    | 0 => i | 1 => j | 2 => b | 3 => c | 4 => o k | 5 => y k | 6 => z k | 7 => u k | _ => v k)
    (fun _ a => a 4 == choose pitch (a 0) (a 1) (a 2) (a 3) (a 5) (a 6) (a 7) (a 8))

theorem branchFits {s : Shape} {n : ℕ} (pitch : Bool)
    {i j b c : ECPolyDefs.Bit} {I J B C : Ref s}
    (hi : i = EBit I) (hj : j = EBit J) (hb : b = EBit B) (hc : c = EBit C)
    {o y z u v : ECPolyDefs.Word} {O Y Z U V : HashRows.Word s}
    (ho : WordFits o O) (hy : WordFits y Y) (hz : WordFits z Z) (hu : WordFits u U) (hv : WordFits v V) :
    Fits (branchN n pitch i j b c o y z u v)
      (NamedBlocks.rows n 9 (fun k => ![I,J,B,C,O k,Y k,Z k,U k,V k])
        (fun _ a => a 4 == choose pitch (a 0) (a 1) (a 2) (a 3) (a 5) (a 6) (a 7) (a 8))) := by
  apply rowM
  · intro k l
    fin_cases l
    · exact hi
    · exact hj
    · exact hb
    · exact hc
    · exact ho k
    · exact hy k
    · exact hz k
    · exact hu k
    · exact hv k
  · intro k a; rfl

end DetDLP.M3B.ChainAddRows
end

section
set_option autoImplicit false
namespace DetDLP.M3B.ChainAddBlock

open S8H0 RegisterMap NamedBlocks GateRoutes ECMapRows ECFits SlotFitCombinators
open ChainRouting ChainMapInputs ChainAddPaths ChainAddRows

set_option maxHeartbeats 500000 in
theorem fits {s : Shape} {d e t p : ℕ} (hd : 1 ≤ d) (width : (w4_M5GraphBounds.graph d hd).nE ≤ e)
    (f : Path (ECAddRows.addShape d e) s) (h : Packed f t) (c : ℕ)
    (P Q : ECPolyDefs.XYZ) (A B : ECChainBlocks.Wires s) (hP : PointFits P A) (hQ : PointFits Q B) :
    Fits (ECPolyDefs.addN s.size p d e t c P Q)
      (ECAddRows.addBlock hd p (p-1) 1 3 c A.1 B.1 A.2.1 A.2.2 B.2.1 B.2.2 f) := by
  let cp := ctrlOff t d
  let go := gateOff t d e
  let a := fun j => ECPolyDefs.word s.size (cp j+1) d
  let b := fun j => ECPolyDefs.reg (cp j)
  let l := ECPolyDefs.word s.size (cp 2) d
  let g := fun j => ECPolyDefs.word s.size (go j) d
  let av := fun j => rwrd (sndP (control f j))
  let bv := fun j => Ref.reg (fstP (control f j) .bit)
  let lv := GateRoutes.word (slope f)
  let gv := fun j => rwrd (result (ChainAddPaths.gate f j))
  have ao (j : Fin 2) : WordFits (a j.val) (av j) := (ctrlIndex h j).second.first.word
  have bo (j : Fin 2) : b j.val = EBit (bv j) := (ctrlIndex h j).reg (.fst .bit) (Nat.add_zero _).symm
  have lo : WordFits l lv := (slopeIndex h).word
  have gout (j : Fin 15) : WordFits (g j.val) (gv j) := (gateIndex h j).first.first.first.word
  let pub := ECPolyDefs.pub s.size
  let narg := ChainAddRows.args (pub (p-1)) (pub 1) (pub 3) (pub c) (pub 0)
    P.2.1 P.2.2 Q.2.1 Q.2.2 (a 0) (a 1) l (fun i => g i.val)
  let parg := ChainAddRows.args (HashRows.pub (p-1)) (HashRows.pub 1) (HashRows.pub 3)
    (HashRows.pub c) (HashRows.pub 0) A.2.1 A.2.2 B.2.1 B.2.2 (av 0) (av 1) lv gv
  have inputs (j : Fin 15) : WordFits (narg j.val).1 (parg j.val).1 ∧
      WordFits (narg j.val).2.1 (parg j.val).2.1 ∧ WordFits (narg j.val).2.2 (parg j.val).2.2 := by
    fin_cases j
    · exact ⟨ChainRouting.pub _,hP.2.1,hQ.2.1⟩
    · exact ⟨gout 0,ao 0,ChainRouting.pub _⟩
    · exact ⟨ChainRouting.pub _,hP.2.2,hQ.2.2⟩
    · exact ⟨gout 2,ao 1,ChainRouting.pub _⟩
    · exact ⟨ChainRouting.pub _,hP.2.2,hQ.2.2⟩
    · exact ⟨gout 4,ao 0,ChainRouting.pub _⟩
    · exact ⟨hP.2.1,hP.2.1,ChainRouting.pub _⟩
    · exact ⟨ChainRouting.pub _,gout 6,ChainRouting.pub _⟩
    · exact ⟨gout 7,ao 1,ChainRouting.pub _⟩
    · exact ⟨lo,lo,ChainRouting.pub _⟩
    · exact ⟨ChainRouting.pub _,hP.2.1,gout 9⟩
    · exact ⟨ChainRouting.pub _,hQ.2.1,gout 10⟩
    · exact ⟨ChainRouting.pub _,gout 11,hP.2.1⟩
    · exact ⟨lo,gout 12,ChainRouting.pub _⟩
    · exact ⟨ChainRouting.pub _,hP.2.2,gout 13⟩
  let rctrl := fun j => ECPolyDefs.bnd s.size p d (cp j+1)
  let pctrl := fun j : Fin 2 => RangeRows.checker p (sndP (control f j))
  have controls : Fits (ECPolyDefs.copies 2 rctrl) (RangeRows.many 1 pctrl) :=
    many1M 1 (d+1) ((d+1)*5) rctrl pctrl
      (fun j => bound p _ (ctrlIndex h j).second) (fun _ => rfl) (fun _ => rfl)
  let rgate := fun j => ECPolyDefs.gbound s.size p d (go j)
  let pgate := fun j : Fin 15 => joinB (RangeRows.checker p (result (ChainAddPaths.gate f j)))
    (RangeRows.checker p (remain (ChainAddPaths.gate f j)))
  have ranges : Fits (ECPolyDefs.copies 15 rgate) (RangeRows.many 14 pgate) :=
    many1M 14 ((d+1)+(d+1)) ((d+1)*5+(d+1)*5) rgate pgate
      (fun j => gateBounds p _ (gateIndex h j)) (fun _ => rfl) (fun _ => rfl)
  let gates := fun j => ECPolyDefs.ghash s.size p d e (go j) (narg j)
  let blocks := fun j : Fin 15 => ECMapRows.slotBlock hd p (parg j.val).1 (parg j.val).2.1 (parg j.val).2.2
    (ChainAddPaths.gate f j)
  have hashes : Fits (ECPolyDefs.copies 15 gates) (RangeRows.many 14 blocks) := by
    refine many1M 14 (ChainGate.counts d).1 (ChainGate.counts d).2 gates blocks ?_
      (fun j => (ChainGate.sizes s.size p d e (go j) (narg j)).1)
      (fun j => (ChainGate.sizes s.size p d e (go j) (narg j)).2)
    intro j
    exact ChainGate.gateFits width _ (gateIndex h j) (inputs j).1 (inputs j).2.1 (inputs j).2.2
  have op := pointWords (fstP f) h.first
  have inv0 := invFits (d := d) (bo 0) (gout 0) (ao 0) (gout 1) (ChainRouting.pub 1)
  have inv1 := invFits (d := d) (bo 1) (gout 2) (ao 1) (gout 3) (ChainRouting.pub 1)
  have bs := branchFits (n := d) true hP.1 hQ.1 (bo 0) (bo 1) lo (gout 5) (gout 8)
    (ChainRouting.pub 0) (ChainRouting.pub 0)
  have bf := branchFits (n := 1) false hP.1 hQ.1 (bo 0) (bo 1)
    (fun _ => op.1) (fun _ => hQ.1) (ChainRouting.pub 0) (ChainRouting.pub 1) (ChainRouting.pub 0)
  have bx := branchFits (n := d) false hP.1 hQ.1 (bo 0) (bo 1) op.2.1 hQ.2.1 hP.2.1 (ChainRouting.pub 0) (gout 11)
  have by' := branchFits (n := d) false hP.1 hQ.1 (bo 0) (bo 1) op.2.2 hQ.2.2 hP.2.2 (ChainRouting.pub 0) (gout 14)
  exact joinM (joinM (pointBounds p _ h.first) (joinM controls ranges))
    (joinM hashes (joinM inv0 (joinM inv1 (joinM bs (joinM bf (joinM bx by'))))))

end DetDLP.M3B.ChainAddBlock
end

section
set_option autoImplicit false
open DetDLP DetDLP.M3B S8H0 GateSemantics ECPhysicalNet ECChainBlocks ECFits

private theorem blockCoefficients {s : RegisterMap.Shape} {d e p : ℕ} (hd : 1 ≤ d)
    {a A b B c C t T : ℕ} (ha : a=A) (hb : b=B) (hc : c=C) (ht : t=T)
    (P Q : Wires s) (f : GateRoutes.Path (ECAddRows.addShape d e) s) :
    ECAddRows.addBlock hd p a b c t P.1 Q.1 P.2.1 P.2.2 Q.2.1 Q.2.2 f =
    ECAddRows.addBlock hd p A B C T P.1 Q.1 P.2.1 P.2.2 Q.2.1 Q.2.2 f := by
  subst A; subst B; subst C; subst T; rfl

private theorem transfer {q : ℕ} {a : ECPolyDefs.N} {L R : NamedBlocks.B q}
    (blocks : L=R) (h : Fits a R) : Fits a L := blocks.symm ▸ h

private theorem DetDLP.bodyChainAddFits (p m k : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (ha₁ : E.a₁=0) (ha₂ : E.a₂=0) (ha₃ : E.a₃=0) (hp : 3 < p) :
    ChainSubblocks.AddFits E m k := by
  intro side j
  let K := (ShapeOf p m k).size
  let f := chainPath (p := p) (m := m) (k := k) side
  let L := ECPolyDefs.ptw K (d p) (ChainOffsets.accumulator p m k side.toNat j.val)
  let R := ECPolyDefs.ptw K (d p) (ChainOffsets.mapStart p m k side.toNat (j.val+1))
  let A := pointWires (acc f j.castSucc)
  let B := pointWires (ECMapRows.fstP (mapPath f j.succ))
  let t := ChainOffsets.addStart p m k side.toNat j.val
  let c4 := (1296*E.a₄.val)%p
  have hL : ChainMapInputs.PointFits L A := ChainRouting.pointWords _ (ChainOffsets.accumulatorIndex side j.castSucc)
  have hf : ChainRouting.Packed (mapPath f j.succ) (ChainOffsets.mapStart p m k side.toNat (j.val+1)) :=
    ChainOffsets.mapIndex side j.succ
  have hR : ChainMapInputs.PointFits R B := ChainRouting.pointWords _ hf.first
  have normalized := ChainAddBlock.fits (s := ShapeOf p m k) (d := d p) (e := e p) (t := t) (p := p)
    (hd p) (Nat.le_refl _) (addPath f j) (ChainOffsets.addIndex side j) c4 L R A B hL hR
  obtain ⟨hn,ho,ht,hc⟩ := ChainAddPaths.coefficients hp E ha₁ ha₂ ha₃
  exact transfer (blockCoefficients (p := p) (hd p) hn ho ht hc A B (addPath f j)) normalized
end

section
set_option autoImplicit false
namespace DetDLP.M3B.PrefixIndex

open S8H0 RegisterMap NamedBlocks ECPrefix

private theorem getChunk {α β : Type} {w : ℕ} (f : α → List β) (len : ∀ j, (f j).length = w)
    (l : List α) (i r : ℕ) (hi : i < l.length) (hr : r < w) (z : β) :
    (l.flatMap f).getD (w*i+r) z = (f l[i]).getD r z := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp [List.getElem?_append,len,hr]
    | succ i =>
      simpa [List.getD_eq_getElem?_getD,List.getElem?_append,len,Nat.mul_succ,
        show ¬ w*i+w+r < w by omega,show w*i+w+r-w=w*i+r by omega]
        using ih i (by simpa using hi)

private theorem finChunk {α : Type} {w n : ℕ} (f : Fin n → List α) (len : ∀ j, (f j).length=w)
    (i : Fin n) (r : ℕ) (hr : r<w) (z : α) :
    ((List.finRange n).flatMap f).getD (w*i.val+r) z = (f i).getD r z := by
  simpa using getChunk f len (List.finRange n) i.val r (by simp) hr z

def coord {s : Shape} {b : ℕ} (x y : Fin b → Ref s) (h : Fin 3) (l : Fin b) : Ref s :=
  if h.val=0 then .pin false else if h.val=1 then x l else y l

private theorem oneLen {s : Shape} {b : ℕ} (x y : Fin b → Ref s) :
    (ECPrefix.one x y).length=3*b := by simp [ECPrefix.one]; omega

private theorem oneAt {s : Shape} {b : ℕ} (x y : Fin b → Ref s) (g : Fin 3) (l : Fin b) :
    (ECPrefix.one x y).getD (g.val*b+l.val) (.pin false) = coord x y g l := by
  have h := l.isLt
  fin_cases g
  · simp [ECPrefix.one,List.getElem?_append,coord,h]
  · simp [ECPrefix.one,List.getElem?_append,coord,h]
  · simp [ECPrefix.one,coord,show 2*b+l.val=b+(b+l.val) by omega,h]

private theorem sideLen {s : Shape} {m b : ℕ} (x y : Route s m b) (v : Bool) :
    (ECPrefix.side x y v).length = 2*m*(3*b) := by
  simp [ECPrefix.side,List.length_flatMap,oneLen,List.finRange_succ]
  ring

private theorem sideAt {s : Shape} {m b : ℕ} (x y : Route s m b) (v : Bool)
    (i : Fin m) (j : Fin 2) (g : Fin 3) (l : Fin b) :
    (ECPrefix.side x y v).getD ((2*i.val+j.val)*(3*b)+(g.val*b+l.val)) (.pin false)
      = coord (x v i j) (y v i j) g l := by
  have hg : g.val*b+l.val < 3*b := by
    have H : (g.val+1)*b ≤ 3*b := Nat.mul_le_mul_right b (by omega)
    rw [Nat.add_mul,one_mul] at H
    omega
  have hj : 3*b*j.val+(g.val*b+l.val) < 2*(3*b) := by
    have H : (j.val+1)*(3*b) ≤ 2*(3*b) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul,one_mul,Nat.mul_comm j.val] at H
    omega
  let mid := fun i : Fin m => (List.finRange 2).flatMap fun j => ECPrefix.one (x v i j) (y v i j)
  have midLen (i : Fin m) : (mid i).length = 2*(3*b) := by
    simp [mid,List.finRange_succ,oneLen]
    omega
  change ((List.finRange m).flatMap mid).getD _ _ = _
  rw [show (2*i.val+j.val)*(3*b)+(g.val*b+l.val) =
    (2*(3*b))*i.val+(3*b*j.val+(g.val*b+l.val)) by ring,finChunk mid midLen i _ hj]
  unfold mid
  rw [finChunk _ (fun _ => oneLen ..) j _ hg]
  exact oneAt .. 

theorem refAt {s : Shape} {m b : ℕ} (x y : Route s m b) (v : Bool)
    (i : Fin m) (j : Fin 2) (g : Fin 3) (l : Fin b) :
    (ECPrefix.refs x y).getD (v.toNat*(2*m*(3*b))+
      ((2*i.val+j.val)*(3*b)+(g.val*b+l.val))) (.pin false) = coord (x v i j) (y v i j) g l := by
  let r := (2*i.val+j.val)*(3*b)+(g.val*b+l.val)
  have hg : g.val*b+l.val < 3*b := by
    have H : (g.val+1)*b ≤ 3*b := Nat.mul_le_mul_right b (by omega)
    rw [Nat.add_mul,one_mul] at H
    omega
  have hr : r<2*m*(3*b) := by
    have H : (2*i.val+j.val+1)*(3*b)≤(2*m)*(3*b) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul,one_mul] at H
    dsimp only [r]
    omega
  cases v
  · simpa [ECPrefix.refs,Bool.toNat,List.getD_eq_getElem?_getD,List.getElem?_append,sideLen,hr,r]
      using sideAt x y false i j g l
  · simpa [ECPrefix.refs,Bool.toNat,List.getD_eq_getElem?_getD,List.getElem?_append,sideLen,r]
      using sideAt x y true i j g l

end DetDLP.M3B.PrefixIndex
end

section
set_option autoImplicit false
namespace DetDLP.M3B.PrefixArithmetic

structure Address (m b n : ℕ) where
  side : Bool
  block : Fin m
  point : Fin 2
  coord : Fin 3
  bit : Fin b
  sideVal : side.toNat = n/(2*m*(3*b))
  pointVal : 2*block.val+point.val = (n/(3*b))%(2*m)
  coordVal : coord.val = (n/b)%3
  bitVal : bit.val = n%b
  index : n = side.toNat*(2*m*(3*b))+((2*block.val+point.val)*(3*b)+(coord.val*b+bit.val))

def decode {m b n : ℕ} (inRange : n < 4*m*(3*b)) : Address m b n := by
  have mb : 0 < m := by by_contra! h; simp [show m=0 by omega] at inRange
  have bb : 0 < b := by by_contra! h; simp [show b=0 by omega] at inRange
  let w := 3*b
  let stride := 2*m
  let v := n/(stride*w)
  let lane := (n/w)%stride
  have hs : 0<stride := by dsimp [stride]; omega
  have hw : 0<w := by dsimp [w]; omega
  have hv : v<2 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hs hw)).mpr
    simpa only [stride,w,show 4*m=2*(2*m) by omega,Nat.mul_assoc] using inRange
  let side := decide (v=1)
  have es : side.toNat = v := by
    by_cases h : v=1
    · simp [side,h]
    · have h0 := Nat.lt_one_iff.mp ((lt_or_eq_of_le (Nat.le_of_lt_succ hv)).resolve_right h)
      change (decide (v=1)).toNat = v
      rw [h0]
      rfl
  have laneLt : lane<2*m := Nat.mod_lt _ hs
  let i : Fin m := ⟨lane/2,by omega⟩
  let j : Fin 2 := ⟨lane%2,by omega⟩
  let g : Fin 3 := ⟨n/b%3,by omega⟩
  let l : Fin b := ⟨n%b,Nat.mod_lt _ bb⟩
  have ei : 2*i.val+j.val=lane := Nat.div_add_mod lane 2
  refine ⟨side,i,j,g,l,es,ei,rfl,rfl,?_⟩
  rw [es,ei]
  have r₁ : 3*(n/w)+g.val = n/b := by
    have H := Nat.div_add_mod (n/b) 3
    rwa [Nat.div_div_eq_div_mul,Nat.mul_comm b 3] at H
  have r₂ : stride*v+lane = n/w := by
    have H := Nat.div_add_mod (n/w) stride
    rwa [Nat.div_div_eq_div_mul,Nat.mul_comm w stride] at H
  calc
    n = b*(n/b)+l.val := (Nat.div_add_mod n b).symm
    _ = b*(3*(n/w)+g.val)+l.val := by rw [r₁]
    _ = b*(3*(stride*v+lane)+g.val)+l.val := by rw [r₂]
    _ = v*(2*m*(3*b))+(lane*(3*b)+(g.val*b+l.val)) := by dsimp only [stride]; ring

end DetDLP.M3B.PrefixArithmetic
end

section
set_option autoImplicit false
namespace DetDLP.M3B.BodyPrefix

open S8H0 RegisterMap NamedBlocks GateSemantics ECPhysicalNet ECFits SlotFitCombinators
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def signal (p m k n : ℕ) : ECPolyDefs.Bit :=
  let b := bitLen p
  let s := n/(2*m*(3*b))
  let i := (n/(3*b))%(2*m)
  let h := (n/b)%3
  let q := ChainSubblocks.factor p m k (2*i+s)
  if h=0 then ECPolyDefs.pin (ShapeOf p m k).size false else
    if h=1 then q.2.1 (n%b) else q.2.2 (n%b)

def prefixN (p m k : ℕ) (pre : List Bool) :=
  if pre.length ≤ 4*m*(3*bitLen p) then
    ECPolyDefs.rows pre.length 1 (fun j _ => signal p m k j) (fun j v => v 0 == pre.getD j false)
  else ECPolyDefs.rows 1 1 (fun _ _ => ECPolyDefs.pin (ShapeOf p m k).size false) (fun _ _ => false)

theorem signalRef {p m k n : ℕ} (hn : n<4*m*(3*bitLen p)) :
    signal p m k n = EBit ((refs (p := p) (m := m) (k := k)).getD n (.pin false)) := by
  let a := PrefixArithmetic.decode hn
  let pi := pointIdx a.block a.point
  let x := fun (s : Bool) (i : Fin m) (j : Fin 2) (l : Fin (bitLen p)) =>
    (factorWires (p := p) (k := k) s (pointIdx i j)).2.1 l.val
  let y := fun (s : Bool) (i : Fin m) (j : Fin 2) (l : Fin (bitLen p)) =>
    (factorWires (p := p) (k := k) s (pointIdx i j)).2.2 l.val
  have addr : (refs (p := p) (m := m) (k := k)).getD n (.pin false) =
      PrefixIndex.coord (x a.side a.block a.point) (y a.side a.block a.point) a.coord a.bit := by
    change (ECPrefix.refs x y).getD n _ = _
    conv_lhs => rw [a.index]
    exact PrefixIndex.refAt .. 
  rw [addr]
  have H := ChainMapInputs.factorInput (p := p) (k := k) a.side pi
  dsimp only [signal]
  rw [← a.sideVal,← a.pointVal,← a.coordVal,← a.bitVal]
  unfold PrefixIndex.coord
  by_cases hz : a.coord.val=0
  · rw [if_pos hz,if_pos hz]
    rfl
  · rw [if_neg hz,if_neg hz]
    by_cases ho : a.coord.val=1
    · rw [if_pos ho,if_pos ho]
      exact H.2.1 a.bit.val
    · rw [if_neg ho,if_neg ho]
      exact H.2.2 a.bit.val

theorem fits (p m k : ℕ) [Fact p.Prime] (pre : List Bool) :
    Fits (prefixN p m k pre) (ECArithNet.prefixBlock (refs (p := p) (m := m) (k := k)) pre) := by
  unfold prefixN ECArithNet.prefixBlock
  by_cases h : pre.length ≤ 4*m*(3*bitLen p)
  · have hr : pre.length ≤ (refs (p := p) (m := m) (k := k)).length := by rwa [refs_length]
    rw [if_pos h,dif_pos hr]
    apply rowM
    · intro i j
      have hi := i.isLt.trans_le hr
      have H := signalRef (p := p) (m := m) (k := k) (i.isLt.trans_le h)
      rw [List.getD_eq_getElem _ _ hi] at H
      exact H
    · intro i v
      rw [List.getD_eq_getElem _ _ i.isLt]
      change (v 0 == pre[i.val]) = decide (v 0=pre[i.val])
      cases v 0 <;> cases pre[i.val] <;> rfl
  · have hr : ¬ pre.length ≤ (refs (p := p) (m := m) (k := k)).length := by rwa [refs_length]
    rw [if_neg h,dif_neg hr]
    exact rowM _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

end DetDLP.M3B.BodyPrefix
end

section
set_option autoImplicit false
namespace DetDLP.M3B.BodyBus

open S8H0 RegisterMap NamedBlocks ECPhysicalNet ECArithNet GateSemantics ECFits SlotFitCombinators

def busBlock {r : Shape} {n w : ℕ} (I : Inputs r n w) (T : ℕ) (i : Fin n) :=
  ECAddrGadget.block T (I.parity i) (I.hash i) (I.selected i) (fun j => .reg (I.addr i j)) (I.carry i)

theorem bankMany {r : Shape} {n w : ℕ} (I : Inputs r n w) (T : ℕ) :
    ECArithNet.bank I T = ECChainBlocks.manyB n (busBlock I T) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let t : Inputs r n w := ⟨fun i => I.parity i.succ,fun i => I.hash i.succ,fun i => I.selected i.succ,
      fun i => I.addr i.succ,fun i => I.carry i.succ⟩
    exact congrArg (joinB (busBlock I T 0)) (ih t)

theorem allBuses (p m k T : ℕ) :
    let w := busWidth p k
    let K := (ShapeOf p m k).size
    Fits (ECPolyDefs.copies (4*m) (ECPolyDefs.busN K (d p) (e p) w T)) (ECArithNet.bank (inputs (p := p) (m := m) (k := k)) T) := by
  let w := busWidth p k
  let fn := ECPolyDefs.busN (ShapeOf p m k).size (d p) (e p) w T
  have one (i : Fin (4*m)) : Fits (fn i.val) (busBlock (inputs (p := p) (m := m) (k := k)) T i) := by
    obtain ⟨hg,he,hj,hk⟩ := m3b_ec_bus_agreement (p := p) (k := k) T i
    exact ⟨hg,he,fun j => (hj j).1,fun j => (hj j).2,hk⟩
  change Fits (ECPolyDefs.copies (4*m) fn) (ECArithNet.bank _ T)
  rw [bankMany]
  exact manyM (4*m) (w+w) (w*2+w*5) fn _ one (fun _ => rfl) (fun _ => rfl)

def anchorN (n : ℕ) := ECPolyDefs.rows n 1 (fun i _ => ECPolyDefs.reg i) (fun _ _ => true)

private def anchors (n : ℕ) : B n := ⟨⟨AnchoredLayout.anchors n,fun _ _ => true⟩,id⟩

private theorem anchorFits (n : ℕ) : Fits (anchorN n) (anchors n) :=
  ⟨rfl,Nat.mul_one _,fun i => Nat.div_one i.val,fun i => Nat.div_one i.val,fun _ _ => rfl⟩

theorem anchored {q : ℕ} {a : ECPolyDefs.N} {b : B q} (h : Fits a b) :
    FitsCore (ECPolyDefs.cat (anchorN q) a) b := joinM (anchorFits q) h

end DetDLP.M3B.BodyBus
end

section
set_option autoImplicit false
namespace DetDLP.M3B.BodyDecode

open OAI.Algorithms.SubexponentialSAT ECPolyDefs

private theorem parsed (l : List W) : frames (Encoding.encodeList id l) = l :=
  W3C.BlockLookup.decodeFrames_correct l

theorem compile (cs seed point : List ℕ) (M T : ℕ) (factors values pre : W) :
    compiled (Encoding.encodeList id [encodeNatListBin cs,encodeNatListBin point,
      encodeNatListBin [M,T],encodeNatListBin seed,factors,values,pre]) =
    net cs seed point pre (seed.length/4) (Nat.clog 2 (2*T)) T := by
  simp only [compiled,dimensions,parsed,List.getD_cons_zero,List.getD_cons_succ,w5_M6Sort.decode_encode]

end DetDLP.M3B.BodyDecode
end

section
set_option autoImplicit false
namespace DetDLP.M3B.BodyAssembly

open S8H0 RegisterMap GateSemantics ECPhysicalNet ECFits SlotFitCombinators ChainOffsets
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def curve {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :=
  [p,E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val]

def slots (p m k T : ℕ) (cs sd : List ℕ) :=
  let D := d p
  let V := e p
  let w := busWidth p k
  ECPolyDefs.copies (4*m) fun i => ECPolyDefs.slotN (ShapeOf p m k).size p D V w
    (i*ECPolyDefs.slotSize D V w) T cs sd (i/4)

def buses (p m k T : ℕ) := ECPolyDefs.copies (4*m)
  (ECPolyDefs.busN (ShapeOf p m k).size (d p) (e p) (busWidth p k) T)

private theorem totalSize (p m k : ℕ) : (ShapeOf p m k).size = chainStart p m k 2+ECPolyDefs.pt (d p) := by
  change 4*m*(SlotCell p k).size+(2*(ECChainBlocks.Chain p (2*m)).size+
    (ECChainBlocks.PointCell (d p)).size) = _
  have sz : (SlotCell p k).size = ECPolyDefs.slotSize (d p) (e p) (busWidth p k) := by
    simp only [ECArithBlock.Sh,GateRoutes.S,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,
      bank,Shape.size,ECPolyDefs.slotSize,ECPolyDefs.bankSize,ECPolyDefs.triple,
      ECPolyDefs.pt,ECPolyDefs.run,ECPolyDefs.aux]
    ring
  rw [sz,ChainOffsets.chainSize,ChainPointRows.pointSize]
  unfold chainStart
  omega

set_option maxHeartbeats 500000 in
private theorem decompose {p m k T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (sd point : List ℕ) (pre : List Bool) :
    ECPolyDefs.net (curve E) sd point pre m k T =
    ECPolyDefs.cat (BodyBus.anchorN ((ShapeOf p m k).size+1))
      (ECPolyDefs.cat (slots p m k T (curve E) sd)
      (ECPolyDefs.cat (ChainAssembly.compiledChain p m k 0 point ((1296*E.a₄.val)%p))
      (ECPolyDefs.cat (ChainAssembly.compiledChain p m k 1 point ((1296*E.a₄.val)%p))
      (ECPolyDefs.cat (buses p m k T) (BodyPrefix.prefixN p m k pre))))) := by
  have er : S8H.PointAddresses.wires (bitLen p+1) = e p := S8H.PointAddresses.wires_eq (hd p)
  have sz : 4*m*ECPolyDefs.slotSize (bitLen p+1) (e p) (max (bitLen p+1) k) +
      2*ECPolyDefs.chainSize (bitLen p+1) (e p) m+ECPolyDefs.pt (bitLen p+1) = (ShapeOf p m k).size :=
    (totalSize p m k).symm
  have modField : (curve E).getD 0 0 = p := by simp only [curve,List.getD_cons_zero]
  have c4 : (curve E).getD 4 0 = E.a₄.val := by simp only [curve,List.getD_cons_zero,List.getD_cons_succ]
  simp only [ECPolyDefs.net,modField,c4,er,sz]
  rfl

set_option maxHeartbeats 700000 in
theorem fits {p m k T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (h₁ : E.a₁=0) (h₂ : E.a₂=0) (h₃ : E.a₃=0) (hp : 3<p)
    (s : ECSeed p m) (P : E.toAffine.Point) (pre : List Bool) :
    FitsCore (ECPolyDefs.net (curve E) (SlotOperands.seedData s) (pointCoords P) pre m k T)
      (ECPhysicalNet.body (k := k) E s T P pre) := by
  let chain := fun side => ChainAssembly.compiledChain p m k side (pointCoords P) ((1296*E.a₄.val)%p)
  let z := slots p m k T (curve E) (SlotOperands.seedData s)
  let b := buses p m k T
  let pr := BodyPrefix.prefixN p m k pre
  have hs : Fits z (ECChainBlocks.manyB (4*m) (slotAt (k := k) E s T)) :=
    m3b_ec_slot_fits p m k T E s
  have hm : ChainSubblocks.MapFits E m k P := bodyChainMapFits p m k E h₁ h₂ h₃ P
  have ha : ChainSubblocks.AddFits E m k := bodyChainAddFits p m k E h₁ h₂ h₃ hp
  have hh : Fits (ECPolyDefs.cat (ECPolyDefs.cat z (ECPolyDefs.cat (chain 0) (chain 1)))
       (ECPolyDefs.cat b pr)) (ECPhysicalNet.body (k := k) E s T P pre) :=
    joinM (joinM hs (joinM (ChainAssembly.ofSubblocks E P hm ha false)
      (ChainAssembly.ofSubblocks E P hm ha true)))
      (joinM (BodyBus.allBuses p m k T) (BodyPrefix.fits p m k pre))
  rw [decompose]
  apply BodyBus.anchored
  simpa only [SlotRows.cat_assoc] using hh

end DetDLP.M3B.BodyAssembly
end

section
set_option autoImplicit false
open DetDLP DetDLP.M3B OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution
    (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0) (hp : 67 < p) :
    letI := ecPointFintype E
    let M := Fintype.card E.toAffine.Point
    let b := bitLen p
    let m := blockCount b
    let T := hashThreshold p (M - 1) m M
    let k := Nat.clog 2 (2 * T)
    64 ≤ M → 4096 * m ≤ M - 1 →
    ∀ (seed : ECSeed p m) (F : Fin m → List E.toAffine.Point) (P : E.toAffine.Point)
      (y : w3_Label M (IndexedFactorBase.mk F).totalCoords) (pre : List Bool),
      let input := Encoding.encodeList id
        [encodeCurveInput p E, encodeNatListBin (pointCoords P), encodeNatListBin [M, T],
         encodeNatListBin ((List.finRange m).flatMap fun i =>
           [(seed i false).1.val + 1, (seed i false).2.val, (seed i true).1.val + 1, (seed i true).2.val]),
         encodeECFactorBlocks F, encodeNatListBin (List.ofFn fun j => (y j).val), pre]
      ECFits.FitsCore (ECPolyDefs.compiled input) (ECPhysicalNet.body (k := k) E seed T P pre) := by
  intro M b m T k _ _ seed F P y pre input
  let sd := SlotOperands.seedData seed
  have sl : sd.length = 4*m := by
    simp [sd,SlotOperands.seedData,SlotOperands.seedRow,List.length_flatMap,Nat.mul_comm]
  change ECFits.FitsCore (ECPolyDefs.compiled (Encoding.encodeList id
    [encodeNatListBin (BodyAssembly.curve E),encodeNatListBin (pointCoords P),encodeNatListBin [M,T],
      encodeNatListBin sd,encodeECFactorBlocks F,encodeNatListBin (List.ofFn fun j => (y j).val),pre])) _
  rw [BodyDecode.compile,sl,Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  exact BodyAssembly.fits E ha₁ ha₂ ha₃ (by omega) seed P pre
end
