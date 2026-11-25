-- Prove2me | solution 1 for DetDLP.m3b_ec_slot_fits
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T09:42:11.201507+00:00
-- url     : https://prove2.me/submissions/e1500e5e-eb1e-495e-a1b5-f97878355290

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_M3B_ECFits
import Theorems.Thm_DetDLP_m3b_ec_hash_and_range_fits

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

open ECPhysicalNet ECArithBlock GateSemantics GateRoutes
private theorem bankLast {p m k : ℕ} (i : Fin (4*m)) : bankName (p:=p) (k:=k) i (Fin.last _) = Fin.last _ := Fin.lastCases_last
theorem zeroM {n q : ℕ} (f : Fin (n+1) → Fin q) :
    Fits (ECPolyDefs.rows 1 1 (fun _ _ => ECPolyDefs.reg (f (Fin.last n)).val) (fun _ v => !v 0)) (rewire (PointGraph.zeroLast n) f) := by
  refine ⟨rfl,rfl,?_,fun _ => rfl,?_⟩
  · intro j; change j.val/1=j.val; exact Nat.div_one _
  · intro i x; change Fin 1 at i; change Fin 1 → Bool at x
    obtain rfl := Fin.eq_zero i
    change (!ECPolyDefs.rd _ ((List.map x ((List.finRange 1).filter (fun j => decide (j=0)))).getD 0 false)) = !x 0
    rw [show List.finRange 1 = [0] by decide]; cases h : x 0 <;> simp [ECPolyDefs.rd,ECPolyDefs.reg,h]
theorem rwJoin {n q : ℕ} (u v : B n) (f : Fin n → Fin q) : rewire (joinB u v) f = joinB (rewire u f) (rewire v f) := by
  unfold rewire joinB; congr 1; funext j
  change f (Fin.addCases u.name v.name j) = Fin.addCases (f ∘ u.name) (f ∘ v.name) j
  induction j using Fin.addCases with
  | left j => erw [Fin.addCases_left,Fin.addCases_left]; rfl
  | right j => erw [Fin.addCases_right,Fin.addCases_right]; rfl
theorem rwMany {n q : ℕ} (l : ℕ) (v : Fin (l+1) → B n) (f : Fin n → Fin q) : rewire (RangeRows.many l v) f = RangeRows.many l (fun j => rewire (v j) f) := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [RangeRows.many,rwJoin,ih]
def route {s u : Shape} (P : Path s u) : Ref s → Ref u
  | .pin b => .pin b | .reg a => .reg (P a) | .masked b a => .masked b (P a)
theorem routeRead {s u : Shape} (P : Path s u) (r : Ref s) (x : Bool) : (route P r).read x = r.read x := by cases r <;> rfl
theorem routeBank {p m k : ℕ} [Fact p.Prime] (i : Fin (4*m)) (r : Ref (Sh p)) :
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
theorem rwRows {n l : ℕ} (r : Fin n → Fin l → Ref (Sh p)) (u : Fin n → (Fin l → Bool) → Bool) : rewire (NamedBlocks.rows n l r u) β = NamedBlocks.rows n l (fun g j => ρ (r g j)) u := rwMapped ..
theorem rwEq {n : ℕ} (a b : Fin n → Ref (Sh p)) : rewire (NamedBlocks.eqs n a b) β = NamedBlocks.eqs n (fun j => ρ (a j)) (fun j => ρ (b j)) := by
  unfold NamedBlocks.eqs; rw [rwRows]; congr 1; funext g j; fin_cases j <;> rfl
end Routing
end DetDLP.M3B.SlotFitCombinators
end

section
set_option autoImplicit false
namespace DetDLP.M3B.SlotOperands

open S8H0 RegisterMap NamedBlocks GateSemantics ECPhysicalNet ECArithBlock

variable {p m k : ℕ} [Fact p.Prime]

def cellOffset (i : Fin (4 * m)) (k : ℕ) : ℕ :=
  i.val * ECPolyDefs.slotSize (d p) (e p) (busWidth p k)

def encoded (i : Fin (4 * m)) (k : ℕ) (r : Ref (Sh p)) : ECPolyDefs.Bit :=
  ((bankName (k := k) i r.source).val, r.read false, r.read true)

private theorem cellSize (p k : ℕ) :
    (SlotCell p k).size = ECPolyDefs.slotSize (d p) (e p) (busWidth p k) := by
  simp only [Sh, GateRoutes.S, RegisterMap.triple, RegisterMap.run, RegisterMap.mul,
    bank, Shape.size, ECPolyDefs.slotSize, ECPolyDefs.bankSize, ECPolyDefs.triple,
    ECPolyDefs.pt, ECPolyDefs.run, ECPolyDefs.aux]
  ring

private theorem bankReg (i : Fin (4 * m)) (a : Addr (Sh p)) :
    (bankName (k := k) i a.index.castSucc).val = cellOffset (p := p) i k + a.index.val := by
  rw [bankName_index]
  change (finProdFinEquiv (i, a.index.castAdd _)).val = _
  change a.index.val + (SlotCell p k).size * i.val = _
  rw [cellSize]
  unfold cellOffset
  ring

omit [Fact p.Prime] in
theorem encoded_pin (i : Fin (4 * m)) (b : Bool) :
    encoded (p := p) i k (.pin b) = ECPolyDefs.pin (ShapeOf p m k).size b := by
  change ((bankName (p := p) (k := k) i (Fin.last _)).val, b, b) = _
  rw [show bankName (p := p) (k := k) i (Fin.last _) = Fin.last _ from Fin.lastCases_last]
  rfl

theorem encoded_reg (i : Fin (4 * m)) (a : Addr (Sh p)) :
    encoded i k (.reg a) = ECPolyDefs.reg (cellOffset (p := p) i k + a.index.val) := by
  change ((bankName (k := k) i a.index.castSucc).val, false, true) = _
  rw [bankReg]
  rfl

omit [Fact p.Prime] in
private theorem flagIndex :
    (CurveRows.flag (d := d p) (e := e p)).index.val = 0 := rfl

omit [Fact p.Prime] in
private theorem yBitIndex (j : Fin (d p)) :
    (CurveRows.ybit (e := e p) j).index.val = 1 + ECPolyDefs.triple (d p) + j.val := by
  simp only [CurveRows.ybit, Addr.index, Fin.val_castAdd, Fin.val_natAdd,
    RegisterMap.triple, Shape.size, ECPolyDefs.triple]
  omega

/-- Both seed coefficients use the low y bit and its complementary register in the same slot. -/
theorem selectWord_eq (i : Fin (4 * m)) (a b j : ℕ) :
    let t := cellOffset (p := p) i k
    ECPolyDefs.select (ShapeOf p m k).size a b (t + 1 + ECPolyDefs.triple (d p)) t j =
      encoded (p := p) i k (selectWord a b j) := by
  dsimp only
  unfold ECPolyDefs.select selectWord
  cases ha : a.testBit j <;> cases hb : b.testBit j
  · exact (encoded_pin i false).symm
  · change _ = encoded i k (.reg (CurveRows.ybit ⟨0, hd p⟩))
    rw [encoded_reg, yBitIndex]
    simp [Nat.add_assoc]
  · change _ = encoded i k (.reg CurveRows.flag)
    rw [encoded_reg, flagIndex, Nat.add_zero]
    rfl
  · exact (encoded_pin i true).symm

def seedRow (s : ECSeed p m) (i : Fin m) : List ℕ :=
  [(s i false).1.val + 1, (s i false).2.val, (s i true).1.val + 1, (s i true).2.val]

def seedData (s : ECSeed p m) : List ℕ := (List.finRange m).flatMap (seedRow s)

private theorem seedGet {α : Type} (f : α → List ℕ) (h : ∀ a, (f a).length = 4)
    (l : List α) (i : ℕ) (hi : i < l.length) (j : ℕ) (hj : j < 4) :
    (l.flatMap f).getD (4*i+j) 0 = (f l[i]).getD j 0 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp [List.getElem?_append, h, hj]
    | succ i =>
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append, h, Nat.mul_succ,
        show ¬ (4*i+4+j < 4) by omega, show 4*i+4+j-4 = 4*i+j by omega]
        using ih i (by simpa using hi)

omit [Fact p.Prime] in
theorem seedData_get (s : ECSeed p m) (i : Fin m) (j : ℕ) (hj : j < 4) :
    (seedData s).getD (4*i.val+j) 0 = (seedRow s i).getD j 0 := by
  have H := seedGet (seedRow s) (fun _ => rfl) (List.finRange m) i.val
    (by simp) j hj
  simpa [seedData] using H

/-- The two serialized words passed to the seventh hash reproduce its selected field coefficients. -/
theorem seedOperands (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m) (i : Fin (4 * m)) :
    let b : Fin m := ⟨i.val / 4, by omega⟩
    let t := cellOffset (p := p) i k
    let pick := fun l => ECPolyDefs.select (ShapeOf p m k).size
      ((seedData s).getD (4*b.val+l) 0) ((seedData s).getD (4*b.val+2+l) 0)
      (t + 1 + ECPolyDefs.triple (d p)) t
    (∀ j, pick 0 j = encoded i k ((seedWires E s b).a j)) ∧
    (∀ j, pick 1 j = encoded i k ((seedWires E s b).b j)) := by
  intro b t pick
  constructor <;> intro j
  · change ECPolyDefs.select _ ((seedData s).getD (4*b.val+0) 0) ((seedData s).getD (4*b.val+2+0) 0) _ _ j = _
    rw [show 4*b.val+2+0=4*b.val+2 by omega, seedData_get s b 0 (by decide),
      seedData_get s b 2 (by decide)]
    exact selectWord_eq i (A s b false) (A s b true) j
  · change ECPolyDefs.select _ ((seedData s).getD (4*b.val+1) 0) ((seedData s).getD (4*b.val+2+1) 0) _ _ j = _
    rw [show 4*b.val+2+1=4*b.val+3 by omega, seedData_get s b 1 (by decide),
      seedData_get s b 3 (by decide)]
    exact selectWord_eq i (Bv s b false) (Bv s b true) j

end DetDLP.M3B.SlotOperands
end

section
set_option autoImplicit false
namespace DetDLP.M3B.SlotOperands

open S8H0 RegisterMap NamedBlocks GateSemantics ECPhysicalNet ECArithBlock

variable {p m k : ℕ} [Fact p.Prime]

private theorem physicalWord (i : Fin (4*m)) {n off : ℕ} (f : Fin n → Addr (Sh p))
    (offset : ∀ j, off + j.val = cellOffset (p := p) i k + (f j).index.val) (j : ℕ) :
    ECPolyDefs.word (ShapeOf p m k).size off n j =
      encoded i k (HashRows.padded (fun l => .reg (f l)) j) := by
  unfold ECPolyDefs.word HashRows.padded
  by_cases hj : j < n
  · rw [if_pos hj, dif_pos hj, encoded_reg]
    exact congrArg ECPolyDefs.reg (offset ⟨j,hj⟩)
  · rw [if_neg hj, dif_neg hj]
    exact (encoded_pin i false).symm

private theorem xWord (i : Fin (4*m)) (j : ℕ) :
    ECPolyDefs.word (ShapeOf p m k).size (cellOffset (p := p) i k + 1) (d p) j =
      encoded (p := p) i k (GateRoutes.rword RangeRows.xa j) := by
  refine physicalWord (p := p) (k := k) i (fun l : Fin (d p) => RangeRows.xa (.fst (.word l))) ?_ j
  intro l
  change _ = cellOffset (p := p) i k + (1 + l.val)
  omega

private theorem yWord (i : Fin (4*m)) (j : ℕ) :
    ECPolyDefs.word (ShapeOf p m k).size
      (cellOffset (p := p) i k + 1 + ECPolyDefs.triple (d p)) (d p) j =
      encoded (p := p) i k (GateRoutes.rword RangeRows.ya j) := by
  refine physicalWord (p := p) (k := k) i (fun l : Fin (d p) => RangeRows.ya (.fst (.word l))) ?_ j
  intro l
  simp only [RangeRows.ya, Addr.index, Fin.val_castAdd, Fin.val_natAdd, RegisterMap.triple,
    Shape.size, ECPolyDefs.triple]
  omega

private theorem outputWord (i : Fin (4*m)) (g : Fin 7) (j : ℕ) :
    ECPolyDefs.word (ShapeOf p m k).size
      (cellOffset (p := p) i k + ECPolyDefs.pt (d p) + g.val * ECPolyDefs.run (d p) (e p))
      (d p) j =
      encoded (p := p) i k (GateRoutes.rword (RangeRows.oa g) j) := by
  refine physicalWord (p := p) (k := k) i (fun l : Fin (d p) => RangeRows.oa g (.fst (.word l))) ?_ j
  intro l
  change _ = cellOffset (p := p) i k +
    (1 + ((RegisterMap.triple (d p)).size + (RegisterMap.triple (d p)).size)
       + (l.val + (RegisterMap.run (d p) (e p)).size * g.val))
  simp only [RegisterMap.triple, RegisterMap.run, RegisterMap.mul, Shape.size,
    ECPolyDefs.pt, ECPolyDefs.triple, ECPolyDefs.run]
  ring

omit [Fact p.Prime] in
private theorem publicWord (i : Fin (4*m)) (n j : ℕ) :
    ECPolyDefs.pub (ShapeOf p m k).size n j = encoded (p := p) i k (HashRows.pub n j) :=
  (encoded_pin i (n.testBit j)).symm

def numericArgs (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m) (i : Fin (4*m))
    (k : ℕ) (g : ℕ) : ECPolyDefs.Word × ECPolyDefs.Word × ECPolyDefs.Word :=
  let t := cellOffset (p := p) i k
  let K := (ShapeOf p m k).size
  let D := d p
  let X := ECPolyDefs.word K (t+1) D
  let yo := t+1+ECPolyDefs.triple D
  let Y := ECPolyDefs.word K yo D
  let out := fun l => ECPolyDefs.word K (t+ECPolyDefs.pt D+l*ECPolyDefs.run D (e p)) D
  let pick := fun l => ECPolyDefs.select K ((seedData s).getD (4*(i.val/4)+l) 0)
    ((seedData s).getD (4*(i.val/4)+2+l) 0) yo t
  let co := [p, E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val]
  let u := fun j => ECPolyDefs.pub K (co.getD j 0)
  let pub := ECPolyDefs.pub K
  match g with
  | 0 => (u 1,X,Y)
  | 1 => (pub 1,out 0,u 3)
  | 2 => (out 1,Y,pub 0)
  | 3 => (pub 1,X,u 2)
  | 4 => (out 3,X,u 4)
  | 5 => (out 4,X,u 5)
  | _ => (pick 0,X,pick 1)

def physicalArgs (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m) (i : Fin (4*m))
    (g : Fin 7) : HashRows.Wires (d p) (hd p) (Sh p) :=
  if g=6 then seedWires E s ⟨i.val/4, by omega⟩
  else GateRoutes.wires (hd p) p (coeff E) g

/-- Each operand in the serialized slot addresses the corresponding physical input bit.
    This includes both branches of the parity selection for gate 6. -/
theorem operands_eq (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m) (i : Fin (4*m))
    (g : Fin 7) :
    let words := numericArgs E s i k g.val
    let wires := physicalArgs E s i g
    (∀ j, words.1 j = encoded i k (wires.a j)) ∧
    (∀ j, words.2.1 j = encoded i k (wires.x j)) ∧
    (∀ j, words.2.2 j = encoded i k (wires.b j)) := by
  dsimp only
  fin_cases g
  · exact ⟨publicWord i E.a₁.val,xWord i,yWord i⟩
  · exact ⟨publicWord i 1,outputWord i 0,publicWord i E.a₃.val⟩
  · exact ⟨outputWord i 1,yWord i,publicWord i 0⟩
  · exact ⟨publicWord i 1,xWord i,publicWord i E.a₂.val⟩
  · exact ⟨outputWord i 3,xWord i,publicWord i E.a₄.val⟩
  · exact ⟨outputWord i 4,xWord i,publicWord i E.a₆.val⟩
  · exact ⟨(seedOperands (k := k) E s i).1,xWord i,(seedOperands (k := k) E s i).2⟩

end DetDLP.M3B.SlotOperands
end

section
set_option autoImplicit false
namespace DetDLP.M3B.SlotOperands

open S8H0 GateSemantics ECPhysicalNet ECArithBlock ECFits

variable {p m k : ℕ} [Fact p.Prime]

def hashGate (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m)
    (i : Fin (4*m)) (k g : ℕ) : ECPolyDefs.N :=
  let t := cellOffset (p := p) i k
  let r := fun j => t + ECPolyDefs.pt (d p) + j * ECPolyDefs.run (d p) (e p)
  let words := numericArgs E s i k g
  ECPolyDefs.hash (ShapeOf p m k).size p (d p) (e p)
    (r g) (r 7 + g * ECPolyDefs.aux (d p)) words.1 words.2.1 words.2.2

theorem hashGate_fits (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m)
    (i : Fin (4*m)) (g : Fin 7) :
    Fits (hashGate E s i k g.val)
      (rewire (HashRows.block p (physicalArgs E s i g)) (bankName (k := k) i)) := by
  let w := numericArgs E s i k g.val
  let r := physicalArgs E s i g
  obtain ⟨ha,hx,hb⟩ := operands_eq (k := k) E s i g
  have hf := (m3b_ec_hash_and_range_fits p m k i).2 g (coeff E)
    w.1 w.2.1 w.2.2 r.a r.x r.b ha hx hb
  have heq : {GateRoutes.wires (hd p) p (coeff E) g with a := r.a, x := r.x, b := r.b} = r := by
    by_cases h : g = 6
    · subst g
      rfl
    · simp only [r, physicalArgs, if_neg h]
  rw [heq] at hf
  exact hf

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

local notation "D" => d p

def out (i : Fin (4*m)) (k g : ℕ) : ECPolyDefs.Word :=
  ECPolyDefs.word (ShapeOf p m k).size ((cellOffset (p := p) i k)+pt D+g*ECPolyDefs.run D (e p)) D

def zeroN (p m k : ℕ) := ECPolyDefs.rows 1 1
  (fun _ _ => reg (ShapeOf p m k).size) (fun _ v => !v 0)

def parityN (i : Fin (4*m)) (k : ℕ) := ECPolyDefs.rows 1 2
  (fun _ j => reg (if j=0 then (cellOffset (p := p) i k)+1+ECPolyDefs.triple D else (cellOffset (p := p) i k))) (fun _ v => v 1 == !v 0)

def comparisonN (i : Fin (4*m)) (k : ℕ) := ECPolyDefs.eqs D (out (p := p) i k 2) (out (p := p) i k 5)

def thresholdN (i : Fin (4*m)) (k T : ℕ) :=
  let diff := (cellOffset (p := p) i k) + bankSize D (e p)
  col (D+1) true (out (p := p) i k 6) (ECPolyDefs.word (ShapeOf p m k).size diff D) (pub (ShapeOf p m k).size T)
    (fun j => reg (diff+D+j))

private theorem encodedRoute (i : Fin (4*m)) (r : Ref (Sh p)) :
    encoded i k r = EBit (route (slot (k := k) i) r) := by
  simp only [encoded,EBit,routeBank,routeRead]

omit [Fact p.Prime] in
private theorem cellIndex (i : Fin (4*m)) (a : Addr (SlotCell p k)) :
    (cell (p := p) (k := k) i a).index.val = (cellOffset (p := p) i k) + a.index.val := by
  change a.index.val+(SlotCell p k).size*i.val = _
  have sz : (SlotCell p k).size = slotSize D (e p) (busWidth p k) := by
    simp only [Sh,GateRoutes.S,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,
      bank,Shape.size,slotSize,bankSize,ECPolyDefs.triple,pt,ECPolyDefs.run,ECPolyDefs.aux]
    ring
  unfold cellOffset
  rw [← sz]
  ring

private theorem bankSize_eq (p : ℕ) : (Sh p).size = bankSize (d p) (e p) := by
  simp only [Sh,GateRoutes.S,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,
    bank,Shape.size,bankSize,ECPolyDefs.triple,pt,ECPolyDefs.run,ECPolyDefs.aux]
  ring

private theorem outBit (i : Fin (4*m)) (g : Fin 7) (j : Fin D) :
    out (p := p) i k g.val j = EBit (.reg (slot (k := k) i (CurveRows.outbit g j))) := by
  change _ = EBit (route (slot (k := k) i) (.reg (CurveRows.outbit g j)))
  rw [← encodedRoute, encoded_reg]
  unfold out ECPolyDefs.word
  rw [if_pos j.isLt]
  apply congrArg reg
  change _ = (cellOffset (p := p) i k)+(1+((RegisterMap.triple D).size+(RegisterMap.triple D).size)+
    (j.val+(RegisterMap.run D (e p)).size*g.val))
  simp only [RegisterMap.triple,RegisterMap.run,RegisterMap.mul,Shape.size,
    pt,ECPolyDefs.triple,ECPolyDefs.run]
  ring

omit [Fact p.Prime] in
theorem zeroFits (i : Fin (4*m)) :
    Fits (zeroN p m k) (rewire (PointGraph.zeroLast (Sh p).size) (bankName (k := k) i)) := by
  have h := zeroM (bankName (p := p) (k := k) i)
  rw [show bankName (p := p) (k := k) i (Fin.last _) = Fin.last _ from Fin.lastCases_last] at h
  exact h

theorem parityFits (i : Fin (4*m)) :
    Fits (parityN (p := p) i k) (rewire (parityRow p) (bankName (k := k) i)) := by
  unfold parityN parityRow
  rw [rwRows]
  apply rowM
  · intro l j
    fin_cases j
    · change _ = EBit (route (slot (k := k) i) (.reg (CurveRows.ybit ⟨0,hd p⟩)))
      rw [← encodedRoute,encoded_reg]
      apply congrArg reg
      change cellOffset (p := p) i k+1+ECPolyDefs.triple D =
        cellOffset (p := p) i k+(CurveRows.ybit (e := e p) ⟨0,hd p⟩).index.val
      simp only [CurveRows.ybit,Addr.index,Fin.val_castAdd,Fin.val_natAdd,
        RegisterMap.triple,Shape.size,ECPolyDefs.triple]
      omega
    · change reg (cellOffset (p := p) i k) = EBit (route (slot (k := k) i) (.reg CurveRows.flag))
      rw [← encodedRoute,encoded_reg]
      exact congrArg reg (Nat.add_zero (cellOffset (p := p) i k)).symm
  · intro l v
    change (v 1 == !v 0) = decide (v 1 = !v 0)
    cases v 0 <;> cases v 1 <;> rfl

theorem comparisonFits (i : Fin (4*m)) :
    Fits (comparisonN (p := p) i k) (rewire (onCurve p) (bankName (k := k) i)) := by
  unfold comparisonN onCurve
  rw [rwEq]
  exact eqM (outBit (p := p) (k := k) i 2) (outBit (p := p) (k := k) i 5)

theorem thresholdFits (i : Fin (4*m)) (T : ℕ) :
    Fits (thresholdN (p := p) i k T) (threshold T (slotPath (p := p) (k := k) i)) := by
  unfold thresholdN threshold
  apply colM
  · intro j
    unfold RangeRows.pad
    by_cases hj : j.val < D
    · rw [dif_pos hj]
      exact outBit i 6 ⟨j.val,hj⟩
    · rw [dif_neg hj]
      unfold out ECPolyDefs.word
      rw [if_neg hj]
      rfl
  · intro j
    unfold RangeRows.pad ECPolyDefs.word
    by_cases hj : j.val < D
    · rw [if_pos hj, dif_pos hj]
      change reg _ = reg (cell (p := p) (k := k) i (.snd (.fst (.word ⟨j.val,hj⟩))) : Addr (ShapeOf p m k)).index.val
      rw [cellIndex]
      apply congrArg reg
      change (cellOffset (p := p) i k)+bankSize D (e p)+j.val = (cellOffset (p := p) i k)+((Sh p).size+j.val)
      rw [bankSize_eq, Nat.add_assoc]
    · rw [if_neg hj,dif_neg hj]
      rfl
  · intro j
    rfl
  · intro j
    change reg _ = reg (cell (p := p) (k := k) i (.snd (.snd (.fst (.word j)))) : Addr (ShapeOf p m k)).index.val
    rw [cellIndex]
    apply congrArg reg
    change (cellOffset (p := p) i k)+bankSize D (e p)+D+j.val = (cellOffset (p := p) i k)+((Sh p).size+(D+j.val))
    rw [bankSize_eq]
    omega

end DetDLP.M3B.SlotRows
end

section
set_option autoImplicit false
namespace DetDLP.M3B.SlotAssembly

open S8H0 ECPhysicalNet ECArithBlock GateSemantics ECFits NamedBlocks
open SlotRows SlotOperands SlotFitCombinators

variable {p m k : ℕ} [Fact p.Prime]

def hashCounts (d : ℕ) : ℕ × ℕ :=
  let mul := S8H.PointAddresses.mul d
  let g := mul.ng + 4*d
  let e := mul.ne + (4*d)*2
  (g+g+(2*d+((d+1)+(d+1))),e+e+((2*d)*5+((d+1)*5+(d+1)*5)))

theorem hash_counts (K p d e r a : ℕ) (u x v : ECPolyDefs.Word) :
    ECPolyDefs.ng (ECPolyDefs.hash K p d e r a u x v) = (hashCounts d).1 ∧
    ECPolyDefs.ne (ECPolyDefs.hash K p d e r a u x v) = (hashCounts d).2 := ⟨rfl,rfl⟩

def slotCounts (d : ℕ) : ℕ × ℕ :=
  let g := (d+1)+(d+1)
  let e := (d+1)*5+(d+1)*5
  (1+((g+7*g)+(1+(7*(hashCounts d).1+(d+(d+1))))),
   1+((e+7*e)+(2+(7*(hashCounts d).2+(d*2+(d+1)*5)))))

theorem slot_counts (K p d e w base T : ℕ) (cs s : List ℕ) (j : ℕ) :
    ECPolyDefs.ng (ECPolyDefs.slotN K p d e w base T cs s j) = (slotCounts d).1 ∧
    ECPolyDefs.ne (ECPolyDefs.slotN K p d e w base T cs s j) = (slotCounts d).2 := by
  dsimp only [ECPolyDefs.slotN,ECPolyDefs.cat,ECPolyDefs.copies,ECPolyDefs.pbound,
    ECPolyDefs.gbound,ECPolyDefs.bnd,ECPolyDefs.eqs,ECPolyDefs.col,ECPolyDefs.rows,
    ECPolyDefs.ne,ECPolyDefs.ng]
  exact ⟨rfl,rfl⟩

def rangeN (i : Fin (4*m)) (k : ℕ) :=
  let K := (ShapeOf p m k).size
  let t := cellOffset (p := p) i k
  ECPolyDefs.cat (ECPolyDefs.pbound K p (d p) t) (ECPolyDefs.copies 7 (fun g =>
    ECPolyDefs.gbound K p (d p) (t+ECPolyDefs.pt (d p)+g*ECPolyDefs.run (d p) (e p))))

def productsN (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m) (i : Fin (4*m)) (k : ℕ) :=
  ECPolyDefs.copies 7 (hashGate E s i k)

theorem productsFits (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m) (i : Fin (4*m)) :
    Fits (productsN E s i k)
      (rewire (products E s ⟨i.val/4,by omega⟩) (bankName (k := k) i)) := by
  unfold productsN products
  rw [rwMany]
  let f := hashGate E s i k
  have count (g : ℕ) : ECPolyDefs.ng (f g) = (hashCounts (d p)).1 ∧
      ECPolyDefs.ne (f g) = (hashCounts (d p)).2 := hash_counts ..
  refine many1M 6 (hashCounts (d p)).1 (hashCounts (d p)).2 f _ ?_ (fun g => (count g).1) (fun g => (count g).2)
  intro g
  by_cases h : g = 6
  · subst g
    exact hashGate_fits (k := k) E s i 6
  · simpa only [physicalArgs, if_neg h] using hashGate_fits (k := k) E s i g

def numeric (p m k T : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m) (j : ℕ) :=
  let D := d p
  let e := e p
  let w := busWidth p k
  ECPolyDefs.slotN (ShapeOf p m k).size p D e w (j*ECPolyDefs.slotSize D e w) T
    [p,E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val] (seedData s) (j/4)

/-- Every row of this slot has the physical owner, signal and Boolean test prescribed by slotAt. -/
theorem singleSlot (E : WeierstrassCurve (ZMod p)) (s : ECSeed p m) (i : Fin (4*m)) (T : ℕ) :
    Fits (numeric p m k T E s i.val) (slotAt (k := k) E s T i) := by
  let z := zeroN p m k
  let r := rangeN (p := p) i k
  let b := parityN (p := p) i k
  let q := productsN E s i k
  let c := comparisonN (p := p) i k
  let t := thresholdN (p := p) i k T
  change Fits (ECPolyDefs.cat z (ECPolyDefs.cat r (ECPolyDefs.cat b
    (ECPolyDefs.cat q (ECPolyDefs.cat c t))))) _
  have physical : Fits (ECPolyDefs.cat (ECPolyDefs.cat z (ECPolyDefs.cat r
      (ECPolyDefs.cat b (ECPolyDefs.cat q c)))) t) (slotAt (k := k) E s T i) := by
    change Fits _ (joinB (rewire (baseBlock E s ⟨i.val/4,by omega⟩) (bankName (k := k) i))
      (threshold T (slotPath (k := k) i)))
    simp only [baseBlock,rwJoin]
    exact joinM (joinM (zeroFits i) (joinM (m3b_ec_hash_and_range_fits p m k i).1
      (joinM (parityFits i) (joinM (productsFits E s i) (comparisonFits i))))) (thresholdFits i T)
  simpa only [cat_assoc] using physical

end DetDLP.M3B.SlotAssembly

open DetDLP DetDLP.M3B DetDLP.M3B.ECFits S8H0 GateSemantics ECPhysicalNet ECChainBlocks
open DetDLP.M3B.SlotFitCombinators DetDLP.M3B.SlotAssembly

theorem solution (p m k T : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m) :
    let K := (ShapeOf p m k).size
    let d := GateSemantics.d p
    let e := GateSemantics.e p
    let w := busWidth p k
    let cs := [p, E.a₁.val, E.a₂.val, E.a₃.val, E.a₄.val, E.a₆.val]
    let sd := (List.finRange m).flatMap fun i =>
      [(seed i false).1.val + 1, (seed i false).2.val, (seed i true).1.val + 1, (seed i true).2.val]
    Fits (ECPolyDefs.copies (4 * m) (fun i => ECPolyDefs.slotN K p d e w (i * ECPolyDefs.slotSize d e w) T cs sd (i / 4)))
      (manyB (4 * m) (slotAt (k := k) E seed T)) := by
  let f := numeric p m k T E seed
  have count (j : ℕ) : ECPolyDefs.ng (f j) = (slotCounts (GateSemantics.d p)).1 ∧
      ECPolyDefs.ne (f j) = (slotCounts (GateSemantics.d p)).2 := slot_counts (w := busWidth p k) ..
  exact manyM (4*m) (slotCounts (GateSemantics.d p)).1 (slotCounts (GateSemantics.d p)).2 f
    (slotAt (k := k) E seed T) (fun i => singleSlot E seed i T)
    (fun j => (count j).1) (fun j => (count j).2)
end
