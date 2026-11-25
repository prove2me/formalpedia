-- Prove2me | solution 1 for DetDLP.m3b_ec_multiplier_agreement
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T01:59:15.480563+00:00
-- url     : https://prove2.me/submissions/1745c04c-516b-4985-9c54-3b1f0cbbf414

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs

set_option autoImplicit false
set_option maxHeartbeats 600000
open DetDLP DetDLP.M3B S8H0 RegisterMap NamedBlocks S8J
namespace ECMulMatch
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


open w4_M5Network
private theorem idxMap {a b : Type} [DecidableEq a] [DecidableEq b] (f : a → b) (h : Function.Injective f) (l : List a) (i : a) : (l.map f).idxOf (f i)=l.idxOf i := by
  induction l with
  | nil => rfl
  | cons j l ih => by_cases hj : i=j <;> simp_all [h.eq_iff,eq_comm]
private theorem readIndex {a : Type} [DecidableEq a] (l : List a) (x : a → Bool) (i : a) (hi : i ∈ l) :
    (l.map x).getD (l.idxOf i) false = x i := by
  have h := List.idxOf_lt_length_of_mem hi
  rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map,List.getElem_idxOf]
private theorem reordered (G : WireGraph) (g : Fin G.nV) (x : Fin (G.nE+G.nE) → Bool) :
    let p := (G.ports g).map Fin.val
    let L := ((G.ports g).filter (fun e => decide ((G.endpoints e).1=g))).map Fin.val
    let R := ((G.ports g).filter (fun e => decide ((G.endpoints e).1≠g))).map Fin.val
    p.map (fun e => (bits (w3_m5Layout G).gate g x).getD ((L++R).idxOf e) false) =
      List.ofFn (fun j => x (w3_m5LocalInc G g j).val) := by
  let src := fun e : Fin G.nE => decide ((G.endpoints e).1=g)
  let dst := fun e : Fin G.nE => decide ((G.endpoints e).2=g)
  let left := (List.finRange G.nE).filter src; let right := (List.finRange G.nE).filter dst
  let val := fun e => x (G.incidentHalf g e)
  have hL : (G.ports g).filter src=left := by
    unfold WireGraph.ports left; rw [List.filter_filter]; apply List.filter_congr; intro j _
    by_cases h : (G.endpoints j).1=g <;> simp [h,src]
  have hR : (G.ports g).filter (fun e => decide ((G.endpoints e).1≠g))=right := by
    unfold WireGraph.ports right; rw [List.filter_filter]; apply List.filter_congr; intro j _
    have h := G.loopless j; by_cases h1 : (G.endpoints j).1=g <;> by_cases h2 : (G.endpoints j).2=g <;> simp_all [dst]
  have eb : edges (w3_m5Layout G).gate g = left.map G.leftHalf ++ right.map G.rightHalf := by
    change (List.finRange (G.nE+G.nE)).filter (fun e => decide (w3_m5HalfGate G e=g)) = _
    rw [splitFin,List.filter_append,List.filter_map,List.filter_map]; simp only [Function.comp_def,w3_m5HalfGate,Fin.addCases_left,Fin.addCases_right]; rfl
  have bitsEq : bits (w3_m5Layout G).gate g x = (left++right).map val := by
    unfold bits; rw [eb]; change List.map x (left.map (Fin.castAdd G.nE) ++ right.map (Fin.natAdd G.nE)) = _
    simp only [List.map_append,List.map_map]; congr 1
    · apply List.map_congr_left; intro j hj; have h : (G.endpoints j).1=g := by simpa [left,src] using hj
      simp [val,WireGraph.incidentHalf,h,WireGraph.leftHalf]
    · apply List.map_congr_left; intro j hj; have h : (G.endpoints j).2=g := by simpa [right,dst] using hj
      have hh : (G.endpoints j).1 ≠ g := fun e => G.loopless j (e.trans h.symm)
      simp [val,WireGraph.incidentHalf,hh,WireGraph.rightHalf]
  dsimp only; rw [hL,hR,←List.map_append,bitsEq,List.map_map]; conv_lhs => rw [← List.ofFn_get (G.ports g),List.map_ofFn]
  apply congrArg List.ofFn; funext j
  let e := (G.ports g).get j
  have mem : e ∈ left++right := by
    have h := (G.mem_ports g e).mp (List.get_mem _ j); simpa [left,right,src,dst] using h
  exact (congrArg (fun n => ((left++right).map val).getD n false) (idxMap Fin.val Fin.val_injective _ e)).trans (readIndex _ _ _ mem)
open w4_M5GraphBounds w4_M5PortTensor w4_M5Dispatch in
private theorem mul_tensor (q : List Unit) (hd : 1 ≤ q.length) (v : Fin (vertexCount q.length)) (a) :
    evalNat q v.val (List.ofFn a) = tensor hd v a := by
  let u := (vertexIndex q.length).symm v
  have hi : vertexIndex q.length u = v := (vertexIndex q.length).apply_symm_apply v
  have h := evalNat_at q hd u (List.ofFn a)
  rw [hi] at h
  exact h.trans ((w4_M5GateEq.gate_eq q hd v (List.ofFn a) u).trans (by
    unfold tensor; congr 2; funext i; simp [i.isLt]))


open w4_M5GraphBounds w4_M5PortTensor w4_M5Dispatch in
private theorem paddedTensor (d : ℕ) (hd : 1 ≤ d) (g : Fin (vertexCount d)) (a : Fin ((graph d hd).deg g) → Bool) :
    evalNat (List.replicate d ()) g.val (List.ofFn a) = tensor hd g a := by
  generalize hq : List.replicate d () = q; have h := congrArg List.length hq; simp only [List.length_replicate] at h
  subst d; exact mul_tensor q hd g a
private theorem dispatch (d : ℕ) (hd : 1 ≤ d) (g : Fin (w3_fpMulLayout d hd).ng) (x : Fin (w3_fpMulLayout d hd).ne → Bool) :
    let ps := w4_M5PortEval.portsNat (S8H.PointAddresses.wires d) g.val (w4_M5EdgeNat.srcNat d) (w4_M5EdgeNat.dstNat d)
    let L := ps.filter (fun j => decide (w4_M5EdgeNat.srcNat d j=g.val)); let R := ps.filter (fun j => decide (w4_M5EdgeNat.srcNat d j≠g.val))
    w4_M5Dispatch.evalNat (List.replicate d ()) g.val (ps.map fun j => (bits (w3_fpMulLayout d hd).gate g x).getD ((L++R).idxOf j) false) = w3_fpMulTests d hd g (fun j => x j.val) := by
  let H := w4_M5GraphBounds.graph d hd
  change Fin H.nV at g; change Fin (H.nE+H.nE) → Bool at x
  have p := w4_M5PortEval.portsNat_eq H g (w4_M5EdgeNat.srcNat d) (w4_M5EdgeNat.dstNat d) (fun i => congrArg Prod.fst (w4_M5EdgeNat.endpointsNat_eq hd i)) (fun i => congrArg Prod.snd (w4_M5EdgeNat.endpointsNat_eq hd i))
  have hs (i : Fin H.nE) : w4_M5EdgeNat.srcNat d i.val = (H.endpoints i).1.val := congrArg Prod.fst (w4_M5EdgeNat.endpointsNat_eq hd i)
  have left : ((H.ports g).map Fin.val).filter (fun j => decide (w4_M5EdgeNat.srcNat d j=g.val)) = ((H.ports g).filter (fun e => decide ((H.endpoints e).1=g))).map Fin.val := by
    rw [List.filter_map]; congr 1; apply List.filter_congr; intro i _; simp only [Function.comp_apply,hs,Fin.val_inj]
  have right : ((H.ports g).map Fin.val).filter (fun j => decide (w4_M5EdgeNat.srcNat d j≠g.val)) = ((H.ports g).filter (fun e => decide ((H.endpoints e).1≠g))).map Fin.val := by
    rw [List.filter_map]; congr 1; apply List.filter_congr; intro i _; simp only [Function.comp_apply,hs,ne_eq,Fin.val_inj]
  dsimp only; rw [S8H.PointAddresses.wires_eq hd,p,left,right]
  let v : Fin (w3_forgetSides H).nV := g
  exact (congrArg (w4_M5Dispatch.evalNat (List.replicate d ()) g.val) (reordered (w3_forgetSides H) v x)).trans (paddedTensor d hd g _)
private theorem ext_spec {d : ℕ} (h : 1 ≤ d) (j : Fin (4*d)) : (if j.val<2*d then j.val else (w4_M5GraphBounds.graph d h).nE-2*d+(j.val-2*d)) = (w4_M5PortTensor.ext h j).val := by
  unfold w4_M5PortTensor.ext w4_M5PortTensor.extEdge; by_cases h₁ : j.val<d <;> by_cases h₂ : j.val<2*d <;> simp only [h₁,h₂,if_true,if_false,dif_pos,dif_neg,reduceDIte,reduceIte] <;> try omega
  · change j.val = j.val + d*0; omega
  · change j.val = (j.val-d) + d*1; omega
  · let n := w4_MulParams.n0 d; let t := w4_M5GraphBounds.W d; let u := w4_MulParams.L2 d * (w4_MulParams.L1 d*t); let v := (2*n-1)*t
    change w4_M5GraphBounds.edgeCount d t-2*d+(j.val-2*d) = 2*d+(2*(n*t)+(2*u+(2*u+(u+(u+(2*n*t+(v+(v+(j.val-2*d)))))))))
    unfold w4_M5GraphBounds.edgeCount; dsimp [v,u,n,t]; omega

private theorem prodM {s : RegisterMap.Shape} {d K off : ℕ} (hd : 1 ≤ d) {a b z : ECPolyDefs.Word} {A B Z : HashRows.Word s} {R : Fin (w3_fpMulLayout d hd).nb → Ref s}
    (hr : ∀ j, ECPolyDefs.reg (off+j.val) = EBit (R j)) (ha : ∀ j, a j = EBit (A j)) (hb : ∀ j, b j = EBit (B j)) (hz : ∀ j, z j = EBit (Z j)) :
    Fits (ECPolyDefs.prod K d off a b z) (HashRows.product hd A B Z R) := by
  unfold ECPolyDefs.prod HashRows.product; dsimp only; apply joinM
  · have h := S8H.PointAddresses.mul_spec hd
    refine ⟨h.ng,h.ne,h.gate,?_,?_⟩
    · intro j; change Fin (w3_fpMulLayout d hd).ne at j
      exact (congrArg (off+·) (h.bit j)).trans (congrArg Prod.fst (hr _))
    · intro g x; change Fin (w3_fpMulLayout d hd).ng at g; change Fin (w3_fpMulLayout d hd).ne → Bool at x
      have rd (i : Fin (w3_fpMulLayout d hd).nb) (b : Bool) : b = (R i).read b := by
        have H := readBit (hr i) b; cases b <;> exact H
      have eqn : (fun j : {k : Fin (w3_fpMulLayout d hd).ne // (w3_fpMulLayout d hd).gate k=g} => x j.val) =
          (fun j => (R ((w3_fpMulLayout d hd).bit j.val)).read (x j.val)) := funext (fun j => rd _ _)
      have he := congrArg (w3_fpMulTests d hd g) eqn
      have res := (dispatch d hd g x).trans he
      dsimp only [ECPolyDefs.check,mapped]
      unfold w4_M5PortEval.portsNat at res
      exact res
  · apply eqM
    · intro j; change ECPolyDefs.reg (off+(if j.val < 2*d then j.val else S8H.PointAddresses.wires d-2*d+(j.val-2*d))) = _
      rw [S8H.PointAddresses.wires_eq hd,ext_spec hd j]; exact hr _
    · intro j; unfold HashRows.busRef; split_ifs <;> first | apply ha | apply hb | apply hz
end ECMulMatch

open HashRows

theorem solution {s : RegisterMap.Shape} {d K off : ℕ} (hd : 1 ≤ d) (a b z : ECPolyDefs.Word) (A B Z : HashRows.Word s) (R : Fin (w3_fpMulLayout d hd).nb → Ref s)
    (hr : ∀ j, ECPolyDefs.reg (off+j.val) = ((R j).source.val,(R j).read false,(R j).read true))
    (ha : ∀ j, a j = ((A j).source.val,(A j).read false,(A j).read true)) (hb : ∀ j, b j = ((B j).source.val,(B j).read false,(B j).read true))
    (hz : ∀ j, z j = ((Z j).source.val,(Z j).read false,(Z j).read true)) :
    let q := ECPolyDefs.prod K d off a b z; let c := HashRows.product hd A B Z R
    ECPolyDefs.ng q = c.core.A.ng ∧ ECPolyDefs.ne q = c.core.A.ne ∧
    (∀ j : Fin c.core.A.ne, ECPolyDefs.gate q j.val=(c.core.A.gate j).val ∧ ECPolyDefs.signal q j.val=(c.name j).val) ∧
    (∀ (g : Fin c.core.A.ng) (x : Fin c.core.A.ne → Bool), ECPolyDefs.check q g.val (((List.finRange c.core.A.ne).filter (fun j => decide (c.core.A.gate j=g))).map x) = c.core.t g (fun j => x j.val)) := by
  have h := ECMulMatch.prodM (K:=K) hd hr ha hb hz
  exact ⟨h.g,h.e,fun j => ⟨h.own j,h.name j⟩,h.chk⟩
