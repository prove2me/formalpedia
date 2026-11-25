-- Prove2me | solution 3 for DetDLP.s8i_ec_moment_query
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T13:58:19.389333+00:00
-- url     : https://prove2.me/submissions/72035196-cad0-4c9b-8e10-fdd5fc363b2f

import Definitions.Def_DetDLP_S8N_MomentOwner
import Theorems.Thm_DetDLP_s8n_ec_moment_signal_addresses

section
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace DetDLP.S8N.ECAddEquiv
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes S8H.ECPointArithmetic S8K.ECAddArithmetic S8O.ECAddLayout S8N.ECAddRoutes S8M.ECMapRows
noncomputable section
variable {p : ℕ} [Fact p.Prime] {s : Shape}
private abbrev Z := zmodEquiv (fits p).le
private abbrev R := runEquiv (GateSemantics.hd p) (fits p).le
abbrev Witness (p : ℕ) := AddCert p × ((GateAux p × (GateAux p × Unit) × GateAux p × (GateAux p × Unit) × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × Unit) × Unit)
private abbrev Cell (p : ℕ) := CheckedRun (width p) p (GateSemantics.hd p) × AuxBank (width p)
@[ext] structure Slice (p : ℕ) where
  o : Bool
  a : Fin 4 → Bounded (d := width p) p
  b : Fin 2 → Bool
  g : Fin 15 → Cell p
private abbrev out (u : Slice p) : Coords p := (u.o,Z (u.a 0),Z (u.a 1))
private abbrev runAt (u : Slice p) (k : Fin 15) : Run p := R (u.g k).1
private def gate (v : Cell p) : GateAux p := (auxEquiv _ v.2,value v.1.1.val.2.1,v.1.1.val.2.2)
private def witness (u : Slice p) : Witness p :=
  let r := runAt u; let t := fun k => gate (u.g k)
  ((r 0,(u.b 0,Z (u.a 2),r 1),r 2,(u.b 1,Z (u.a 3),r 3),r 4,r 5,r 6,r 7,r 8,r 9,r 10,r 11,r 12,r 13,r 14,()),(t 0,(t 1,()),t 2,(t 3,()),t 4,t 5,t 6,t 7,t 8,t 9,t 10,t 11,t 12,t 13,t 14,()),())
def pack (o : Coords p) (w : Witness p) : Slice p :=
  let ⟨⟨g0,(b1,a1,g1),g2,(b3,a3,g3),g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,_⟩,⟨t0,(t1,()),t2,(t3,()),t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,_⟩,_⟩ := w
  ⟨o.1,fun k => Z.symm (![o.2.1,o.2.2,a1,a3] k),![b1,b3],fun k => (R.symm (![g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14] k),(auxEquiv _).symm ((![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14] k).1))⟩
theorem unpack (u : Slice p) : pack (out u) (witness u) = u := by
  rcases u with ⟨o,a,b,g⟩; apply Slice.ext <;> first | rfl | (funext k; fin_cases k <;> simp [pack,witness,gate,runAt])
private theorem gate_restore (r : Run p) (t : GateAux p) (h : w3_slotLt _ r.1.val p t.2) : gate (R.symm r,(auxEquiv _).symm t.1) = t := by
  refine Prod.ext ((auxEquiv _).apply_symm_apply _) ?_; let v := R.symm r
  have hv : (Z v.1).val = r.1.val := congrArg (fun z : Run p => z.1.val) (R.apply_symm_apply r)
  rw [GateSemantics.resVal] at hv; obtain ⟨_,_,uniq⟩ := (w3_slotLt_spec (r.1.val_lt.trans (fits p)) (fits p).le).2 r.1.val_lt
  exact (uniq _ (hv ▸ (below_iff p v.1.val).1 v.1.property)).trans (uniq _ h).symm
theorem repack (E : WeierstrassCurve (ZMod p)) (P Q o : Coords p) (w : Witness p) (h : (addChecks E P Q o w.1).bits w.2) :
    out (pack o w) = o ∧ witness (pack o w) = w := by
  rcases w with ⟨⟨g0,⟨b1,a1,g1⟩,g2,⟨b3,a3,g3⟩,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,⟨⟩⟩,⟨t0,⟨t1,⟨⟩⟩,t2,⟨t3,⟨⟩⟩,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,⟨⟩⟩,⟨⟩⟩
  have H0 := gate_restore g0 t0 h.1.1.2; have H1 := gate_restore g1 t1 h.1.2.1.1.2; have H2 := gate_restore g2 t2 h.1.2.2.1.2; have H3 := gate_restore g3 t3 h.1.2.2.2.1.1.2; have H4 := gate_restore g4 t4 h.1.2.2.2.2.1.2; have H5 := gate_restore g5 t5 h.1.2.2.2.2.2.1.2; have H6 := gate_restore g6 t6 h.1.2.2.2.2.2.2.1.2; have H7 := gate_restore g7 t7 h.1.2.2.2.2.2.2.2.1.2; have H8 := gate_restore g8 t8 h.1.2.2.2.2.2.2.2.2.1.2; have H9 := gate_restore g9 t9 h.1.2.2.2.2.2.2.2.2.2.1.2; have H10 := gate_restore g10 t10 h.1.2.2.2.2.2.2.2.2.2.2.1.2; have H11 := gate_restore g11 t11 h.1.2.2.2.2.2.2.2.2.2.2.2.1.2; have H12 := gate_restore g12 t12 h.1.2.2.2.2.2.2.2.2.2.2.2.2.1.2; have H13 := gate_restore g13 t13 h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2; have H14 := gate_restore g14 t14 h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  simp [pack,out,witness,runAt,H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14]
private def chooseSlope {α : Type} (i j bx by' : Bool) (ch tan zero : α) : α :=
  if !i && !j && !bx then ch else if !i && !j && bx && !by' then tan else zero
private abbrev slopeVal (P Q : Coords p) (u : Slice p) := chooseSlope P.1 Q.1 (u.b 0) (u.b 1) (runAt u 5).1 (runAt u 8).1 0
private abbrev S (p : ℕ) := addShape (width p) (GateSemantics.e p)
private def data (u : Slice p) (l : Bits (width p)) : (S p).Data := ((u.o,fun k => (u.a k).val),(u.b,l),fun k => (rawRun (u.g k).1,(u.g k).2))
private abbrev bits (x : ZMod p) : Bits (width p) := ((Z.symm x).val).1
private theorem bits_val (x : ZMod p) : (value (bits x)).val = x.val := by rw [← GateSemantics.resVal _ (Z.symm x).property,Equiv.apply_symm_apply]
private theorem slope_bit (i j b c : Bool) (x y : ZMod p) (k : ℕ) :
    mux i j b c (x.val.testBit k) (y.val.testBit k) = (chooseSlope i j b c x y 0).val.testBit k := by
  unfold mux chooseSlope; split <;> first | rfl | split <;> simp
private def dst (P Q : Coords p) (b c : Bool) (x y : ZMod p) : Coords p :=
  if P.1 then Q else if Q.1 then (false,P.2) else if b && c then (true,0,0) else (false,x,y)
private theorem dst_bits (P Q : Coords p) (b c : Bool) (x y : ZMod p) : let D := dst P Q b c x y
    D.1 = (if P.1 then Q.1 else !Q.1 && b && c) ∧
    (∀ k, D.2.1.val.testBit k = dest P.1 Q.1 b c (P.2.1.val.testBit k) (Q.2.1.val.testBit k) (x.val.testBit k)) ∧
    (∀ k, D.2.2.val.testBit k = dest P.1 Q.1 b c (P.2.2.val.testBit k) (Q.2.2.val.testBit k) (y.val.testBit k)) := by
  rcases P with ⟨i,_⟩; rcases Q with ⟨j,_⟩; cases i <;> cases j <;> cases b <;> cases c <;> simp [dst,dest]
private abbrev block (E : WeierstrassCurve (ZMod p)) := @addBlock (width p) (GateSemantics.e p) s (GateSemantics.hd p) p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val
theorem rows_iff (E : WeierstrassCurve (ZMod p)) (P Q : Coords p) (u : Slice p) (l : Bits (width p)) (f : Path (S p) s) (v : Bits (s.size+1))
    (i j : Ref s) (x y X Y : Word s) (H : At f v (data u l)) (I : i.eval v = P.1) (J : j.eval v = Q.1)
    (hx : evalWord x v P.2.1.val) (hy : evalWord y v P.2.2.val) (hX : evalWord X v Q.2.1.val) (hY : evalWord Y v Q.2.2.val) :
    (block E i x y j X Y f).OK v ↔ l = bits (slopeVal P Q u) ∧ (addChecks E P Q (out u) (witness u).1).bits (witness u).2 := by
  let z := fun k => (runAt u k).1; let a := fun k => Z (u.a k); let L := slopeVal P Q u
  have one : (1 : ZMod p).val = 1 := by have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩; exact ZMod.val_one _
  have valA (k) : (value (u.a k).val.1).val = (a k).val := (GateSemantics.resVal _ _).symm
  have ltA (v : Bounded (d:=width p) p) := (below_iff p v.val).1 v.property
  have ltG (k) : w3_slotLt _ (z k).val p (gate (u.g k)).2 := by change w3_slotLt _ (Z _).val _ _; rw [GateSemantics.resVal]; exact ltA _
  let eqw (a b : ZMod p) := ∀ k : Fin (width p), a.val.testBit k = b.val.testBit k
  let inv (b : Bool) (x y r : ZMod p) := if b then eqw x 0 ∧ eqw y 0 else eqw r 1
  have invEq (b : Bool) (x y r : ZMod p) : (∀ k : Fin (width p), if b then x.val.testBit k = false ∧ y.val.testBit k = false else r.val.testBit k = (1 : ℕ).testBit k) ↔ inv b x y r := by cases b <;> simp [inv,eqw,one,forall_and]
  let D := dst P Q (u.b 0) (u.b 1) (z 11) (z 14); have dd := dst_bits P Q (u.b 0) (u.b 1) (z 11) (z 14)
  have slEq : (∀ k : Fin (width p), (value l).val.testBit k = L.val.testBit k) ↔ l = bits L := by
    simp only [← bits_val L,value_bit,funext_iff]
  refine (rows_iff_decoded (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val i j x y X Y _ _ _ _ f v u.o _ u.b l (fun k => (u.g k).1) _ H hx hy hX hY).trans ?_; dsimp only
  simp only [ltA,implies_true,and_self,true_and]; simp only [valA,I,J,invEq]
  let g := ECAddRoutes.args (-1 : ZMod p).val 1 (3 : ZMod p).val (-27*E.c₄).val 0 P.2.1.val P.2.2.val Q.2.1.val Q.2.2.val (value l).val (fun k => (a k).val) (fun k => (z k).val)
  let ht (k : Fin 15) := w3_slotHashBits (GateSemantics.hd p) (g k).1 (g k).2.2 (g k).2.1 (z k).val (runAt u k).2 (gate (u.g k)).1
  change ((∀ k, ht k) ∧ inv (u.b 0) (z 0) (a 2) (z 1) ∧ inv (u.b 1) (z 2) (a 3) (z 3) ∧
    (∀ k : Fin (width p), (value l).val.testBit k = mux P.1 Q.1 (u.b 0) (u.b 1) ((z 5).val.testBit k) ((z 8).val.testBit k)) ∧ _) ↔ l = bits L ∧ _
  simp only [slope_bit,← dd.1]; change ((∀ k, ht k) ∧ _ ∧ _ ∧ (∀ k : Fin (width p), (value l).val.testBit k = L.val.testBit k) ∧ u.o = D.1 ∧ (∀ k : Fin (width p), (a 0).val.testBit k = dest P.1 Q.1 (u.b 0) (u.b 1) _ _ ((z 11).val.testBit k)) ∧ (∀ k : Fin (width p), (a 1).val.testBit k = dest P.1 Q.1 (u.b 0) (u.b 1) _ _ ((z 14).val.testBit k))) ↔ _
  rw [slEq]; simp only [← dd.2.1,← dd.2.2]
  by_cases hl : l = bits L
  · let test (k : Fin 15) (a x b : ZMod p) := w3_slotHashBits (GateSemantics.hd p) a.val b.val x.val (z k).val (runAt u k).2 (gate (u.g k)).1
    let lt (k : Fin 15) := w3_slotLt _ (z k).val p (gate (u.g k)).2
    change _ ↔ l = bits L ∧ (((test 0 (-1) P.2.1 Q.2.1 ∧ lt 0) ∧ ((test 1 (z 0) (a 2) 0 ∧ lt 1) ∧ inv (u.b 0) (z 0) (a 2) (z 1)) ∧ (test 2 1 P.2.2 Q.2.2 ∧ lt 2) ∧ ((test 3 (z 2) (a 3) 0 ∧ lt 3) ∧ inv (u.b 1) (z 2) (a 3) (z 3)) ∧ (test 4 (-1) P.2.2 Q.2.2 ∧ lt 4) ∧ (test 5 (z 4) (a 2) 0 ∧ lt 5) ∧ (test 6 P.2.1 P.2.1 0 ∧ lt 6) ∧ (test 7 3 (z 6) (-27*E.c₄) ∧ lt 7) ∧ (test 8 (z 7) (a 3) 0 ∧ lt 8) ∧ (test 9 L L 0 ∧ lt 9) ∧ (test 10 (-1) P.2.1 (z 9) ∧ lt 10) ∧ (test 11 (-1) Q.2.1 (z 10) ∧ lt 11) ∧ (test 12 (-1) (z 11) P.2.1 ∧ lt 12) ∧ (test 13 L (z 12) 0 ∧ lt 13) ∧ (test 14 (-1) P.2.2 (z 13) ∧ lt 14) ∧ True) ∧ u.o = D.1 ∧ eqw (a 0) D.2.1 ∧ eqw (a 1) D.2.2)
    simp only [hl,eq_self,true_and,and_true,show ∀ k, lt k from ltG,Fin.forall_fin_succ,Fin.forall_fin_zero,ht,g,ECAddRoutes.args,Matrix.cons_val_zero,Matrix.cons_val_succ,bits_val,test,ZMod.val_zero,one,eqw]
    tauto
  · simp [hl]
/-- Realizability in any enclosing bank, with the two coordinate triples fixed. -/
def Accepted (E : WeierstrassCurve (ZMod p)) (P Q : Coords p) (w : (S p).Data) : Prop :=
  ∃ (s : Shape) (f : Path (S p) s) (v : Bits (s.size+1)) (i j : Ref s) (x y X Y : Word s), At f v w ∧
    i.eval v = P.1 ∧ j.eval v = Q.1 ∧ evalWord x v P.2.1.val ∧ evalWord y v P.2.2.val ∧ evalWord X v Q.2.1.val ∧ evalWord Y v Q.2.2.val ∧ (block E i x y j X Y f).OK v
theorem decodeAccepted (E : WeierstrassCurve (ZMod p)) (P Q : Coords p) (w : (S p).Data) (hw : Accepted E P Q w) :
    ∃ u : Slice p, data u (bits (slopeVal P Q u)) = w ∧ (addChecks E P Q (out u) (witness u).1).bits (witness u).2 := by
  obtain ⟨s,f,v,i,j,x,y,X,Y,H,I,J,hx,hy,hX,hY,ok⟩ := hw
  have hr := ((joinB_iff _ _ _).1 ok); have A := (many_iff _ _ _).1 hr.1; have G := (many_iff _ _ _).1 ((joinB_iff _ _ _).1 hr.2).1
  have bound {k : Path (triple (width p)) s} {a : Triple (width p)} (h : At k v a) := (checker_iff p k v a h).1
  let r (k : Fin 15) := (w.2.2 k).1
  let u : Slice p := ⟨w.1.1,fun k => ⟨w.1.2 k,bound (fun t => H (.fst (.snd (.vec k t)))) (A k)⟩,w.2.1.1,fun k =>
    ((⟨(r k).1,bound (fun t => H (.snd (.snd (.vec k (.fst (.fst t)))))) ((joinB_iff _ _ _).1 (G k)).1⟩,
    (⟨(r k).2.1.1,bound (fun t => H (.snd (.snd (.vec k (.fst (.snd (.fst (.fst t)))))))) ((joinB_iff _ _ _).1 (G k)).2⟩,(r k).2.1.2),(r k).2.2),(w.2.2 k).2)⟩
  obtain ⟨hl,h⟩ := (rows_iff E P Q u w.2.1.2 f v i j x y X Y H I J hx hy hX hY).1 ok
  exact ⟨u,hl ▸ (rfl : data u w.2.1.2 = w),h⟩
/-- Raw output words are interpreted as naturals; no reduction modulo the field is needed. -/
def outputWords (w : (S p).Data) : Bool × ℕ × ℕ := (w.1.1,(value (w.1.2 0).1).val,(value (w.1.2 1).1).val)
def coordWords (o : Coords p) := (o.1,o.2.1.val,o.2.2.val)
/-- Uniqueness concerns the whole register slice. The final clause applies to every accepted slice. -/
theorem acceptedSlice_unique (E : WeierstrassCurve (ZMod p)) (P Q : (S8K.SWEquiv.short E).toAffine.Point) :
    (∃! w : (addShape (width p) (GateSemantics.e p)).Data, Accepted E (coords P) (coords Q) w) ∧
    ∀ w, Accepted E (coords P) (coords Q) w → outputWords w = coordWords (coords (P+Q)) := by
  let o := coords (P+Q); obtain ⟨c,hc,uc⟩ := swAdd_unique_bits E w3_m5_modmul_r2 P Q
  let u := pack o c; obtain ⟨ho,he⟩ := repack E (coords P) (coords Q) o c hc
  have hu : (addChecks E (coords P) (coords Q) (out u) (witness u).1).bits (witness u).2 := by rw [show out u = o from ho,show witness u = c from he]; exact hc
  let l := bits (slopeVal (coords P) (coords Q) u); let w := data u l
  let v : Bits ((S p).size+1) := Fin.lastCases false ((S p).decode.symm w)
  have H : At id v w := by intro j; change v j.index.castSucc = _; simp [v,← Addr.correct j ((S p).decode.symm w)]
  have ok : Accepted E (coords P) (coords Q) w := ⟨_,id,v,.pin _,.pin _,pub _,pub _,pub _,pub _,H,rfl,rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,
    (rows_iff E _ _ u l id v _ _ _ _ _ _ H rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).2 ⟨rfl,hu⟩⟩
  have unique (w' : (S p).Data) (hw : Accepted E (coords P) (coords Q) w') : w' = w := by
    obtain ⟨t,ht,h⟩ := decodeAccepted E _ _ w' hw
    have ot : out t = o := swAdd_sound E w3_m5_modmul_r2 P Q _ _ ((swAdd_lift E _ _ _ _).1 _ h)
    rw [ot] at h; have ut : t = u := by rw [← unpack t,ot,uc (witness t) h]
    exact ht.symm.trans (ut ▸ rfl)
  refine ⟨⟨w,ok,unique⟩,?_⟩; intro w' hw; rw [unique w' hw]
  change (u.o,(value (u.a 0).val.1).val,(value (u.a 1).val.1).val) = coordWords o
  rw [← GateSemantics.resVal _ (u.a 0).property,← GateSemantics.resVal _ (u.a 1).property]; exact congrArg coordWords ho
end
end DetDLP.S8N.ECAddEquiv
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace DetDLP.S8M.ECFoldEquiv
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes
open S8H.ECPointArithmetic S8K.ECAddArithmetic S8O.ECAddLayout S8N.ECAddRoutes S8M.ECMapRows
open S8N.ECAddEquiv (Accepted acceptedSlice_unique)
open ECFoldRoutes
open private DetDLP.S8M.ECFoldRoutes.foldStep DetDLP.S8M.ECFoldRoutes.outputFlag DetDLP.S8M.ECFoldRoutes.outputX DetDLP.S8M.ECFoldRoutes.outputY from Definitions.Def_DetDLP_S8M_ECFoldRoutes
noncomputable section
variable {p n : ℕ} [Fact p.Prime] {s : Shape}
abbrev FoldSlice (p n : ℕ) := (foldShape n (width p) (GateSemantics.e p)).Data
abbrev Wires (s : Shape) := Ref s × Word s × Word s
/-- The flag is read directly and both coordinate words represent canonical field values. -/
def Reads (a : Wires s) (v : Bits (s.size+1)) (c : Coords p) : Prop :=
  a.1.eval v = c.1 ∧ evalWord a.2.1 v c.2.1.val ∧ evalWord a.2.2 v c.2.2.val

namespace Steps
private abbrev oneShape (p : ℕ) := addShape (width p) (GateSemantics.e p)
private abbrev Point (E : WeierstrassCurve (ZMod p)) := (S8K.SWEquiv.short E).toAffine.Point
private abbrev stage (E : WeierstrassCurve (ZMod p)) (a b : Wires s) :=
  @addBlock (width p) (GateSemantics.e p) s (GateSemantics.hd p) p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2
private def canonical (E : WeierstrassCurve (ZMod p)) (P Q : Point E) : (oneShape p).Data :=
  (acceptedSlice_unique E P Q).1.exists.choose
private theorem stage_iff (E : WeierstrassCurve (ZMod p)) (P Q : Point E) (a b : Wires s)
    (f : Path (oneShape p) s) (v : Bits (s.size+1)) (w : (oneShape p).Data) (h : At f v w)
    (ha : Reads a v (coords P)) (hb : Reads b v (coords Q)) :
    (stage E a b f).OK v ↔ w = canonical E P Q := by
  let U := (acceptedSlice_unique E P Q).1
  have hw : Accepted E (coords P) (coords Q) (canonical E P Q) := U.exists.choose_spec
  constructor
  · intro ok; exact U.unique ⟨_,f,v,_,_,_,_,_,_,h,ha.1,hb.1,ha.2.1,ha.2.2,hb.2.1,hb.2.2,ok⟩ hw
  · rintro rfl
    obtain ⟨u,hu,checks⟩ := DetDLP.S8N.ECAddEquiv.decodeAccepted _ _ _ _ hw
    rw [← hu] at h
    exact (DetDLP.S8N.ECAddEquiv.rows_iff _ _ _ u _ f v _ _ _ _ _ _ h ha.1 hb.1 ha.2.1 ha.2.2 hb.2.1 hb.2.2).2 ⟨rfl,checks⟩
private abbrev output (f : Path (oneShape p) s) : Wires s :=
  (.reg (f (.fst (.fst .bit))),word (fun j : Addr (.word (width p)) => f (.fst (.snd (.vec 0 (.fst j))))),
    word (fun j : Addr (.word (width p)) => f (.fst (.snd (.vec 1 (.fst j))))))
private theorem stage_out (E : WeierstrassCurve (ZMod p)) (P Q : Point E) (f : Path (oneShape p) s)
    (v : Bits (s.size+1)) (h : At f v (canonical E P Q)) : Reads (output f) v (coords (P+Q)) := by
  let w := canonical E P Q
  have ho := (acceptedSlice_unique E P Q).2 w (acceptedSlice_unique E P Q).1.exists.choose_spec
  have words (k : Fin 4) := word_eval (fun j : Addr (.word (width p)) => f (.fst (.snd (.vec k (.fst j))))) v (w.1.2 k).1
    (fun i => ((Ref.reg _).correct v).trans (h (.fst (.snd (.vec k (.fst (.word i)))))))
  have hx : (value (w.1.2 0).1).val = (coords (P+Q)).2.1.val := congrArg (fun z : Bool × ℕ × ℕ => z.2.1) ho
  have hy : (value (w.1.2 1).1).val = (coords (P+Q)).2.2.val := congrArg (fun z : Bool × ℕ × ℕ => z.2.2) ho
  exact ⟨(h (.fst (.fst .bit))).trans (congrArg Prod.fst ho),hx ▸ words 0,hy ▸ words 1⟩
private def accum {E : WeierstrassCurve (ZMod p)} (P : Point E) (Ps : Fin n → Point E) (k : ℕ) (hk : k ≤ n) : Point E :=
  P + ∑ j : Fin k, Ps ⟨j.val,by omega⟩
private theorem accum_succ {E : WeierstrassCurve (ZMod p)} (P : Point E) (Ps : Fin n → Point E) (k : Fin n) :
    accum P Ps (k.val+1) k.isLt = accum P Ps k.val k.isLt.le + Ps k := by
  simp [accum, Fin.sum_univ_castSucc,add_assoc]
private abbrev part (q : Path (foldShape n (width p) (GateSemantics.e p)) s) (i : Fin n) : Path (oneShape p) s := fun j => q (.vec i j)
private def wireAt (a : Wires s) (q : Path (foldShape n (width p) (GateSemantics.e p)) s) (k : ℕ) (hk : k ≤ n) : Wires s :=
  if h : k = 0 then a else output (part q ⟨k-1,by omega⟩)
def transcript {E : WeierstrassCurve (ZMod p)} (P : Point E) (Ps : Fin n → Point E) : FoldSlice p n :=
  fun k => canonical E (accum P Ps k.val k.isLt.le) (Ps k)
private theorem chain {E : WeierstrassCurve (ZMod p)} (P : Point E) (Ps : Fin n → Point E) (a : Wires s) (b : Fin n → Wires s)
    (q : Path (foldShape n (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1)) (w : FoldSlice p n) (h : At q v w)
    (ha : Reads a v (coords P)) (hb : ∀ i, Reads (b i) v (coords (Ps i))) (k : ℕ) (hk : k ≤ n) :
    ((∀ i : Fin n, i.val < k → (stage E (wireAt a q i.val i.isLt.le) (b i) (part q i)).OK v) ↔
      (∀ i : Fin n, i.val < k → w i = transcript P Ps i)) ∧
    ((∀ i : Fin n, i.val < k → w i = transcript P Ps i) → Reads (wireAt a q k hk) v (coords (accum P Ps k hk))) := by
  induction k with
  | zero => simpa [wireAt,accum] using ha
  | succ k ih =>
    let i : Fin n := ⟨k,hk⟩
    obtain ⟨iffPre,outPre⟩ := ih (by omega)
    have H (j : Fin n) : At (part q j) v (w j) := fun t => h (.vec j t)
    have last (pre : ∀ j : Fin n, j.val < k → w j = transcript P Ps j) :=
      stage_iff E (accum P Ps k (by omega)) (Ps i) (wireAt a q k (by omega)) (b i) (part q i) v (w i) (H i) (outPre pre) (hb i)
    constructor
    · constructor
      · intro ok
        have pre := iffPre.mp (fun j hj => ok j (by omega))
        intro j hj; by_cases hlt : j.val < k
        · exact pre j hlt
        · have eq : j = i := Fin.ext (by change j.val = k; omega)
          subst j; exact (last pre).mp (ok i (Nat.lt_succ_self _))
      · intro eq
        have pre := fun j (hj : j.val < k) => eq j (by omega)
        intro j hj; by_cases hlt : j.val < k
        · exact iffPre.mpr pre j hlt
        · have hji : j = i := Fin.ext (by change j.val = k; omega)
          subst j; exact (last pre).mpr (eq i (Nat.lt_succ_self _))
    · intro eq
      have ht := H i
      rw [eq i (Nat.lt_succ_self _)] at ht
      change Reads (wireAt a q (i.val+1) _) v (coords (accum P Ps (i.val+1) _))
      rw [accum_succ]; simpa [wireAt] using stage_out E (accum P Ps k (by omega)) (Ps i) (part q i) v ht
private abbrev routed (E : WeierstrassCurve (ZMod p)) (a : Wires s) (b : Fin n → Wires s) (t : Wires s) :=
  @foldBlock s n (width p) (GateSemantics.e p) (GateSemantics.hd p) p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val
    a.1 a.2.1 a.2.2 (fun i => (b i).1) (fun i => (b i).2.1) (fun i => (b i).2.2) t.1 t.2.1 t.2.2
theorem targetRows (E : WeierstrassCurve (ZMod p)) (P : Point E) (Ps : Fin n → Point E)
    (a : Wires s) (b : Fin n → Wires s) (t : Wires s) (q : Path (foldShape n (width p) (GateSemantics.e p)) s)
    (v : Bits (s.size+1)) (w : FoldSlice p n) (h : At q v w) (ha : Reads a v (coords P))
    (hb : ∀ i, Reads (b i) v (coords (Ps i))) :
    (routed E a b t q).OK v ↔ w = transcript P Ps ∧ t.1.eval v = (coords (P+∑ i,Ps i)).1 ∧
      (∀ i : Fin (width p), (t.2.1 i).eval v = (coords (P+∑ i,Ps i)).2.1.val.testBit i) ∧
      (∀ i : Fin (width p), (t.2.2 i).eval v = (coords (P+∑ i,Ps i)).2.2.val.testBit i) := by
  rw [foldBlock_iff]
  have step (i : Fin n) : (DetDLP.S8M.ECFoldRoutes.foldStep (GateSemantics.hd p) p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val a.1 a.2.1 a.2.2 (fun j => (b j).1) (fun j => (b j).2.1) (fun j => (b j).2.2) q i).OK v ↔
      (stage E (wireAt a q i.val i.isLt.le) (b i) (part q i)).OK v := by
    by_cases hi : i.val = 0 <;> simp [DetDLP.S8M.ECFoldRoutes.foldStep,wireAt,hi,stage,part,output]
  simp only [step]
  have C := chain P Ps a b q v w h ha hb n le_rfl
  simp only [Fin.is_lt, forall_const] at C
  let result := coords (P + ∑ i, Ps i)
  let last := wireAt a q n le_rfl
  have pins (hw : ∀ i, w i = transcript P Ps i) :
      (last.1.eval v = t.1.eval v ∧
        (∀ i : Fin (width p), (last.2.1 i).eval v = (t.2.1 i).eval v) ∧
        (∀ i : Fin (width p), (last.2.2 i).eval v = (t.2.2 i).eval v)) ↔
      t.1.eval v = result.1 ∧
        (∀ i : Fin (width p), (t.2.1 i).eval v = result.2.1.val.testBit i) ∧
        (∀ i : Fin (width p), (t.2.2 i).eval v = result.2.2.val.testBit i) := by
    have H : Reads last v result := C.2 hw
    constructor
    · rintro ⟨hf,hx,hy⟩
      exact ⟨hf.symm.trans H.1, fun i => (hx i).symm.trans (H.2.1 i),
        fun i => (hy i).symm.trans (H.2.2 i)⟩
    · rintro ⟨hf,hx,hy⟩
      exact ⟨H.1.trans hf.symm, fun i => (H.2.1 i).trans (hx i).symm,
        fun i => (H.2.2 i).trans (hy i).symm⟩
  constructor
  · rintro ⟨ok,hf,hx,hy⟩
    have hw := C.1.mp ok
    refine ⟨funext hw,(pins hw).mp ?_⟩
    by_cases hn : n = 0 <;>
      simpa [last,wireAt,DetDLP.S8M.ECFoldRoutes.outputFlag,DetDLP.S8M.ECFoldRoutes.outputX,
        DetDLP.S8M.ECFoldRoutes.outputY,hn] using And.intro hf (And.intro hx hy)
  · rintro ⟨rfl,hf,hx,hy⟩
    have hw := fun i => (rfl : transcript P Ps i = _)
    refine ⟨C.1.mpr hw,?_⟩
    have eq := (pins hw).mpr ⟨hf,hx,hy⟩
    by_cases hn : n = 0 <;>
      simpa [last,wireAt,DetDLP.S8M.ECFoldRoutes.outputFlag,DetDLP.S8M.ECFoldRoutes.outputX,
        DetDLP.S8M.ECFoldRoutes.outputY,hn] using eq

end Steps
end
end DetDLP.S8M.ECFoldEquiv
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8N.SeedAtomEquiv

open DetDLP.S8N.ECSeedBank DetDLP.S8M.ECAtomSlot
open DetDLP.S8I.ECQueryCount DetDLP.S8H0.GateSemantics DetDLP.S8H4.Semantics M89S1
private abbrev edgesV2 := DetDLP.S8H0.GateSemantics.e

noncomputable def seed (p m : ℕ) [Fact p.Prime] (η : List Bool)
    (hη : η.length ≤ m * 4 * bitLen p) :
    {v : (ecSeedShape m (S8C.atomWidth p)).Data // ecSeedOK p m η v} ≃ Mass p m η :=
  ecSeedEquiv p m η hη

open S8H0 RegisterMap GateRoutes NamedBlocks HashRows ResidueWires
open RoutesV2 S8G.SeedAndAtomBank S8G.SeedSliceEquiv
variable {p m : ℕ} [Fact p.Prime] {s : Shape}
private abbrev D := S8C.atomWidth
private def sidePath (q : Path (ecSeedShape m (D p)) s) (b : Bool) : Path (seedShape m (D p)) s
  | .vec i a => seedSlotPath q i b a
private def half (v : (ecSeedShape m (D p)).Data) (b : Bool) : (seedShape m (D p)).Data :=
  fun i => if b then (v i).2 else (v i).1
private def emptyMass (S : FpSeed p m) : S8G.FpMoment.Mass p m [] := ⟨S,by simp [S8G.FpMoment.seedSet]⟩
private noncomputable def enc (S : FpSeed p m) := ((seedEquiv p m [] (Nat.zero_le _)).symm (emptyMass S)).val
omit [Fact p.Prime] in
private theorem halfAt (q : Path (ecSeedShape m (D p)) s) (u : Bits (s.size+1)) (v : (ecSeedShape m (D p)).Data)
    (h : ∀ j, (q j).get (s.decode (u ∘ Fin.castSucc)) = j.get v) (b : Bool) :
    ∀ j, (sidePath q b j).get (s.decode (u ∘ Fin.castSucc)) = j.get (half v b) := by
  rintro ⟨i,a⟩; cases b <;> apply h
private theorem sideOK (q : Path (ecSeedShape m (D p)) s) (u : Bits (s.size+1)) (v : (ecSeedShape m (D p)).Data)
    (h : ∀ j, (q j).get (s.decode (u ∘ Fin.castSucc)) = j.get v) (b : Bool) :
    (∀ i, (ecSeedSlotBlock p (seedSlotPath q i b)).OK u) ↔ ∃ S, half v b = enc S := by
  have H := seedOK_iff (sidePath q b) u (half v b) (halfAt q u v h b) (η:=[]) (Nat.zero_le _)
  rw [seedBlock_iff] at H
  simp only [List.length_nil, Fin.forall_fin_zero, and_true] at H
  refine H.trans ⟨?_,?_⟩
  · intro ok; let z := seedEquiv p m [] (Nat.zero_le _) ⟨half v b,ok⟩
    exact ⟨z.val,(congrArg Subtype.val ((seedEquiv p m [] (Nat.zero_le _)).symm_apply_apply ⟨half v b,ok⟩)).symm⟩
  · rintro ⟨S,hS⟩; rw [hS]; exact ((seedEquiv p m [] (Nat.zero_le _)).symm (emptyMass S)).prop
private theorem reads (q : Path (ecSeedShape m (D p)) s) (u : Bits (s.size+1)) (v : (ecSeedShape m (D p)).Data)
    (h : ∀ j, (q j).get (s.decode (u ∘ Fin.castSucc)) = j.get v) (b : Bool) (S : FpSeed p m) (he : half v b = enc S) (i : Fin m) :
    evalWord (ecSeedA (seedSlotPath q i b)) u ((S i).1.val+1) ∧ evalWord (ecSeedB (seedSlotPath q i b)) u (S i).2.val := by
  have hv := halfAt q u v h b; rw [he] at hv
  let e := seedEquiv p m [] (Nat.zero_le _)
  have H := seedEquiv_words (sidePath q b) u (enc S) hv (Nat.zero_le _) (e.symm (emptyMass S)).prop i
  change evalWord _ _ (((e (e.symm (emptyMass S))).val i).1.val+1) ∧ evalWord _ _ (((e (e.symm (emptyMass S))).val i).2.val) at H
  rw [e.apply_symm_apply] at H; exact H
omit [Fact p.Prime] in
private theorem prefixRows (q : Path (ecSeedShape m (D p)) s) (u : Bits (s.size+1)) (S : ECSeed p m) (η : List Bool)
    (hη : η.length ≤ m*4*bitLen p) (hw : ∀ b i, evalWord (ecSeedA (seedSlotPath q i b)) u ((S i b).1.val+1) ∧
      evalWord (ecSeedB (seedSlotPath q i b)) u (S i b).2.val) :
    (∀ i : Fin η.length, i.val < m*4*bitLen p ∧ (ecPrefixBit p q i.val).eval u = η[i]) ↔ S ∈ seedSet p m η := by
  let L := List.ofFn (ecBits S)
  have len : (L.take η.length).length = η.length := List.length_take_of_le (by simpa [L] using hη)
  have H (i : Fin η.length) : (ecPrefixBit p q i.val).eval u = (L.take η.length)[i.val]'(by rw [len]; exact i.isLt) := by
    simp only [L,List.getElem_take,List.getElem_ofFn,ecPrefixBit,dif_pos (i.isLt.trans_le hη),ecBits,packBits,ecWords]
    split <;> first | apply (hw _ _).1 | apply (hw _ _).2
  simp only [seedSet,Finset.mem_filter,Finset.mem_univ,true_and]; change _ ↔ L.take η.length = η
  constructor
  · intro z; exact List.ext_getElem len (fun i _ hi => (H ⟨i,hi⟩).symm.trans (z ⟨i,hi⟩).2)
  · intro z i; exact ⟨i.isLt.trans_le hη,(H i).trans (by simp only [z]; rfl)⟩

/-- The V2 rows recognize exactly the canonical four-coefficient seed slices, including the prefix. -/
theorem seedRows (q : Path (ecSeedShape m (D p)) s) (u : Bits (s.size+1)) (v : (ecSeedShape m (D p)).Data)
    (h : ∀ j, (q j).get (s.decode (u ∘ Fin.castSucc)) = j.get v) (η : List Bool) (hη : η.length ≤ m*4*bitLen p) :
    (ecSeedBlockV2 p m η q).OK u ↔ ecSeedOK p m η v := by
  rw [ecSeedBlockV2_iff]; constructor
  · rintro ⟨slots,pins⟩
    obtain ⟨A,hA⟩ := (sideOK q u v h false).mp (fun i => (slots i).1)
    obtain ⟨B,hB⟩ := (sideOK q u v h true).mp (fun i => (slots i).2)
    let S : ECSeed p m := fun i b => if b then B i else A i
    have W : ∀ b i, evalWord (ecSeedA (seedSlotPath q i b)) u ((S i b).1.val+1) ∧ evalWord (ecSeedB (seedSlotPath q i b)) u (S i b).2.val := by
      intro b i; cases b <;> first | exact reads q u v h _ A hA i | exact reads q u v h _ B hB i
    exact ⟨⟨S,(prefixRows q u S η hη W).mp pins⟩,fun i => Prod.ext (congrFun hA i) (congrFun hB i)⟩
  · rintro ⟨S,hS⟩
    have he (b : Bool) : half v b = enc (fun i => S.val i b) := by
      funext i; cases b <;> first | exact congrArg Prod.fst (hS i) | exact congrArg Prod.snd (hS i)
    have H (b : Bool) := (sideOK q u v h b).mpr ⟨_,he b⟩
    exact ⟨fun i => ⟨H false i,H true i⟩,(prefixRows q u S.val η hη (fun b => reads q u v h b _ (he b))).mpr S.prop⟩

theorem seedReads (q : Path (ecSeedShape m (D p)) s) (u : Bits (s.size+1)) (v : (ecSeedShape m (D p)).Data)
    (h : ∀ j, (q j).get (s.decode (u ∘ Fin.castSucc)) = j.get v) (η : List Bool) (hη : η.length ≤ m*4*bitLen p)
    (ok : ecSeedOK p m η v) (b : Bool) (i : Fin m) : let S := (seed p m η hη ⟨v,ok⟩).val
      evalWord (ecSeedA (seedSlotPath q i b)) u ((S i b).1.val+1) ∧ evalWord (ecSeedB (seedSlotPath q i b)) u (S i b).2.val := by
  apply reads q u v h; funext k
  have eq := congrArg (fun z => z.val k) ((seed p m η hη).symm_apply_apply ⟨v,ok⟩)
  cases b <;> first | exact congrArg Prod.fst eq.symm | exact congrArg Prod.snd eq.symm

noncomputable def atomBank {E : WeierstrassCurve (ZMod p)} [E.IsElliptic] (S : ECSeed p m) {T : ℕ} (hT : T ≤ p) :
    {v : Fin m → (slotShape (d p) (edgesV2 p)).Data // ∀ i, sliceOK S i E T (v i)} ≃ Tuple (ecFactorBlock E T S) :=
  Equiv.subtypePiEquivPi.trans ((Equiv.piCongrRight fun i => S8M.ECAtomSlot.slotEquiv (E := E) S i hT).trans
    { toFun := fun f => ⟨fun i => (f i).val,Fintype.mem_piFinset.mpr fun i => (f i).prop⟩
      invFun := fun t i => ⟨t.val i,Fintype.mem_piFinset.mp t.prop i⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl })

end DetDLP.S8N.SeedAtomEquiv
end

section
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8N.FreeFold
open S8H0 RegisterMap NamedBlocks ResidueWires HashRows GateRoutes
open S8H.ECPointArithmetic S8K.ECAddArithmetic S8M.ECMapRows S8M.ECFoldRoutes S8M.ECFoldEquiv
noncomputable section
variable {p n : ℕ} [Fact p.Prime] {s : Shape} (E : WeierstrassCurve (ZMod p))
abbrev Pt := (S8K.SWEquiv.short E).toAffine.Point
abbrev block (a : Wires s) (b : Fin n → Wires s) (t : Wires s) (q : Path (foldShape n (width p) (GateSemantics.e p)) s) :=
  foldBlock (GateSemantics.hd p) p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val a.1 a.2.1 a.2.2
    (fun i => (b i).1) (fun i => (b i).2.1) (fun i => (b i).2.2) t.1 t.2.1 t.2.2 q
def canonical (P : Pt E) (Ps : Fin n → Pt E) : FoldSlice p n :=
  S8M.ECFoldEquiv.Steps.transcript P Ps
/-- The fold fixes the transcript and its physical target pins even when the target is not a priori a point. -/
theorem rows (P : Pt E) (Ps : Fin n → Pt E) (a : Wires s) (b : Fin n → Wires s) (t : Wires s) (q : Path (foldShape n (width p) (GateSemantics.e p)) s)
    (v : Bits (s.size+1)) (w : FoldSlice p n) (H : At q v w) (ha : Reads a v (coords P)) (hb : ∀ i, Reads (b i) v (coords (Ps i))) :
    (block E a b t q).OK v ↔ w = canonical E P Ps ∧ t.1.eval v = (coords (P+∑ i,Ps i)).1 ∧
      (∀ i : Fin (width p), (t.2.1 i).eval v = (coords (P+∑ i,Ps i)).2.1.val.testBit i) ∧
      (∀ i : Fin (width p), (t.2.2 i).eval v = (coords (P+∑ i,Ps i)).2.2.val.testBit i) := by
  exact S8M.ECFoldEquiv.Steps.targetRows E P Ps a b t q v w H ha hb
end
end DetDLP.S8N.FreeFold
end

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentSem

open S8H0 RegisterMap NamedBlocks ResidueWires
open S8J.CircuitRealizes

abbrev shape (p m : ℕ) (j : Fin 4) :=
  RoutesV2.bank j m (GateSemantics.d p) (GateSemantics.e p)

noncomputable section

def rawOf (s : Shape) (u : Bits (s.size+1)) := s.decode (u ∘ Fin.castSucc)
def extendOf (s : Shape) (v : s.Data) := (PointGraph.dropLast.symm (s.decode.symm v)).val

theorem rawOf_extendOf (s : Shape) (v : s.Data) : rawOf s (extendOf s v) = v :=
  (congrArg s.decode (PointGraph.dropLast.apply_symm_apply (s.decode.symm v))).trans
    (s.decode.apply_symm_apply v)

private def pinnedEquiv (s : Shape) (B : B (s.size+1)) :
    let N := joinB (PointGraph.zeroLast s.size) B
    let C := AnchoredLayout.block N.core (s.size+1)
    let w := AnchoredLayout.wiring N.core N.name
    let A := circuit C w
    {b : Fin A.nb → Bool // ∀ g, test C w g (fun e => b (A.bit e.1)) = true} ≃
      {v : s.Data // B.OK (PointGraph.dropLast.symm (s.decode.symm v)).val} := by
  intro N C w A
  let D := PointGraph.dropLast.trans s.decode
  refine ((w3_factorEquiv _ _).symm.trans
    ((S8J.CircuitRealizes.decode C w).trans (AnchoredLayout.assignments _ _))).trans ?_
  let Z := fun u : Bits (s.size+1) => u (Fin.last _) = false
  refine (Equiv.subtypeEquivRight (q:=fun u => Z u ∧ B.OK u)
    (fun u => (joinB_iff ..).trans (and_congr_left fun _ => PointGraph.zeroLast_iff _))).trans ?_
  refine (Equiv.subtypeSubtypeEquivSubtypeInter Z (fun u => B.OK u)).symm.trans (Equiv.subtypeEquiv D ?_)
  intro u
  change B.OK u.val ↔ B.OK (D.symm (D u)).val
  rw [Equiv.symm_apply_apply]

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (hm : 1 ≤ m)
variable (j : Fin 4) (T : ℕ) (η : List Bool)

abbrev rowsAt :=
  RoutesV2.network (GateSemantics.hd p) hm p T (GateSemantics.coeff E)
    E.b₂.val (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val j η id

abbrev net := joinB (PointGraph.zeroLast (shape p m j).size) (rowsAt E hm j T η)
abbrev core := AnchoredLayout.block (net E hm j T η).core ((shape p m j).size+1)
abbrev wires := AnchoredLayout.wiring (net E hm j T η).core (net E hm j T η).name

def layout : w3_FactorLayout := circuit (core E hm j T η) (wires E hm j T η)
def tests : w3_factorTest (layout E hm j T η) := test _ (wires E hm j T η)
abbrev Physical := {b : Fin (layout E hm j T η).nb → Bool //
  ∀ g, tests E hm j T η g (fun e => b ((layout E hm j T η).bit e.1)) = true}

abbrev bits := Bits ((shape p m j).size+1)
abbrev raw (u : bits (p:=p) (m:=m) j) := rawOf (shape p m j) u
abbrev extend (v : (shape p m j).Data) := extendOf (shape p m j) v

omit [Fact p.Prime] in
theorem raw_extend (v : (shape p m j).Data) :
    raw (p:=p) (m:=m) j (extend (p:=p) (m:=m) j v) = v :=
  rawOf_extendOf (shape p m j) v

/-- Decode copy cycles and anchors, then drop the distinguished zero wire. -/
def physicalEquiv : Physical E hm j T η ≃
    {v : (shape p m j).Data // (rowsAt E hm j T η).OK (extend (p:=p) (m:=m) j v)} :=
  pinnedEquiv (shape p m j) (rowsAt E hm j T η)

end
end DetDLP.S8N.MomentSem
end

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentSem

open S8H0 RegisterMap NamedBlocks GateRoutes ResidueWires
open S8N.ECSeedBank S8M.ECAtomSlot S8I.ECQueryCount
open M89S1

noncomputable section
variable {p m T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (hm : 1 ≤ m) (hT : T ≤ p) (η : List Bool) (hη : η.length ≤ m*4*bitLen p)

abbrev SeedData := (ecSeedShape m (GateSemantics.d p)).Data
abbrev SeedValid := {v : SeedData (p:=p) (m:=m) // ecSeedOK p m η v}
abbrev Slot := (slotShape (GateSemantics.d p) (GateSemantics.e p)).Data
abbrev Slots (S : ECSeed p m) :=
  {a : Fin m → Slot (p:=p) // ∀ i, sliceOK S i E T (a i)}

private theorem addressIndex (t : Shape) (i : Fin t.size) : (address t i).index = i := by
  induction t with
  | bit => exact Fin.ext (by have := i.isLt; change i.val < 1 at this; change 0 = i.val; omega)
  | word => rfl
  | pair l r il ir =>
    simp only [address]; split <;> simp only [Addr.index,il,ir] <;> apply Fin.ext
    · rfl
    · change l.size + (i.val-l.size) = i.val; omega
  | vec n t ih =>
    simp only [address,Addr.index,ih,Prod.mk.eta]
    exact finProdFinEquiv.apply_symm_apply i

theorem decodeRegion {s l : Shape} (q : Path l s) (u : Bits (s.size+1)) (v : l.Data)
    (h : ∀ a, (q a).get (rawOf s u) = a.get v) :
    l.decode ((u ∘ route q) ∘ Fin.castSucc) = v := by
  apply l.decode.symm.injective
  rw [Equiv.symm_apply_apply]
  funext i
  have hL := (Addr.correct (q (address l i)) (u ∘ Fin.castSucc)).symm
  have hR := Addr.correct (address l i) (l.decode.symm v)
  rw [Equiv.apply_symm_apply, addressIndex] at hR
  change u (route q i.castSucc) = _
  simp only [route, Fin.lastCases_castSucc]
  exact hL.trans ((h _).trans hR)

/-- Seed validity and all point slots for the requested number of tuple copies. -/
def validTuples (j : Fin 4) (v : (shape p m j).Data) : Prop :=
  ∃ H : ecSeedOK p m η v.1, ∀ k : Fin (RoutesV2.copies j), ∀ i : Fin m,
    sliceOK ((SeedAtomEquiv.seed p m η hη) ⟨v.1,H⟩).val i E T (v.2.1 k i)

include hη in
theorem seedRowsAt (j : Fin 4) (u : bits (p:=p) (m:=m) j) :
    (RoutesV2.ecSeedBlockV2 p m η (RoutesV2.seeds (s:=shape p m j) id)).OK u ↔
      ecSeedOK p m η (raw (p:=p) (m:=m) j u).1 :=
  SeedAtomEquiv.seedRows (RoutesV2.seeds (s:=shape p m j) id) u _ (fun _ => rfl) η hη

omit [E.IsElliptic] in
theorem atomRowsAt (j : Fin 4) (u : bits (p:=p) (m:=m) j)
    (hs : ecSeedOK p m η (raw (p:=p) (m:=m) j u).1) (k : Fin (RoutesV2.copies j)) (i : Fin m) :
    let q : Path (shape p m j) (shape p m j) := id
    let v := raw (p:=p) (m:=m) j u
    (slotBlock (GateSemantics.hd p) p T (GateSemantics.coeff E)
      (RoutesV2.seedA q i false) (RoutesV2.seedB q i false)
      (RoutesV2.seedA q i true) (RoutesV2.seedB q i true) (RoutesV2.atom q k i)).OK u ↔
    sliceOK ((SeedAtomEquiv.seed p m η hη) ⟨v.1,hs⟩).val i E T (v.2.1 k i) := by
  let q : Path (shape p m j) (shape p m j) := id
  let v := raw (p:=p) (m:=m) j u
  let S := ((SeedAtomEquiv.seed p m η hη) ⟨v.1,hs⟩).val
  have seedRead : ∀ a, (RoutesV2.seeds q a).get ((shape p m j).decode (u ∘ Fin.castSucc)) =
      a.get v.1 := fun _ => rfl
  have A := SeedAtomEquiv.seedReads (RoutesV2.seeds q) u _ seedRead η hη hs false i
  have B := SeedAtomEquiv.seedReads (RoutesV2.seeds q) u _ seedRead η hη hs true i
  refine (slotBlock_slice_iff (T:=T) (E:=E) _ _ _ _ S i (RoutesV2.atom q k i) u
    A.1 A.2 B.1 B.2).trans ?_
  exact iff_of_eq (congrArg (sliceOK S i E T)
    (decodeRegion (RoutesV2.atom q k i) u (v.2.1 k i) (fun _ => rfl)))

omit [E.IsElliptic] in
private theorem noOutputRows (j : Fin 4) (hj : RoutesV2.outputs j = 0)
    (u : bits (p:=p) (m:=m) j) :
    (rowsAt E hm j T η).OK u ↔ validTuples (T:=T) E η hη j (raw (p:=p) (m:=m) j u) := by
  have seedOk := seedRowsAt η hη j u
  apply (RoutesV2.network_iff (GateSemantics.hd p) hm p T (GateSemantics.coeff E)
    E.b₂.val (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val j η id u).trans
  constructor
  · rintro ⟨hs,ha,_⟩
    exact ⟨seedOk.mp hs, fun k i => (atomRowsAt E η hη j u (seedOk.mp hs) k i).mp (ha k i)⟩
  · rintro ⟨hs,ha⟩
    exact ⟨seedOk.mpr hs, fun k i => (atomRowsAt E η hη j u hs k i).mpr (ha k i),
      fun t => Fin.elim0 (Fin.cast hj t)⟩

private def splitNoOutput (j : Fin 4) (hj : RoutesV2.outputs j = 0) :
    {r : (shape p m j).Data // validTuples (T:=T) E η hη j r} ≃
    (Σ s : SeedValid (p:=p) (m:=m) η,
      Fin (RoutesV2.copies j) → Slots (T:=T) E ((SeedAtomEquiv.seed p m η hη) s).val) where
  toFun r := ⟨⟨r.val.1,r.property.choose⟩,fun k => ⟨r.val.2.1 k,r.property.choose_spec k⟩⟩
  invFun
    | ⟨s,a⟩ => ⟨(s.val,(fun k => (a k).val),fun t => Fin.elim0 (Fin.cast hj t)),
        ⟨s.property,fun k => (a k).property⟩⟩
  left_inv := by
    rintro ⟨⟨s,a,z⟩,h⟩
    exact Subtype.ext (Prod.ext rfl (Prod.ext rfl (funext fun i => Fin.elim0 (Fin.cast hj i))))
  right_inv := by rintro ⟨⟨s,hs⟩,a⟩; rfl

/-- When no common sum is requested, the physical register bank is in bijection
with one seed and a family of allowed tuples, one per wired copy. -/
def noOutputEquiv (j : Fin 4) (hj : RoutesV2.outputs j = 0) :
    Physical E hm j T η ≃
    Σ S : Mass p m η, Fin (RoutesV2.copies j) → Tuple (ecFactorBlock E T S.val) := by
  refine (physicalEquiv E hm j T η).trans ?_
  refine (Equiv.subtypeEquivRight (q:=validTuples (T:=T) E η hη j) (fun v => ?_)).trans ?_
  · simpa only [raw_extend] using noOutputRows E hm η hη j hj (extend (p:=p) (m:=m) j v)
  · exact (splitNoOutput (T:=T) E η hη j hj).trans
      (Equiv.sigmaCongr (SeedAtomEquiv.seed p m η hη) (fun s => Equiv.piCongrRight
        (fun _ => SeedAtomEquiv.atomBank ((SeedAtomEquiv.seed p m η hη) s).val hT)))

end
end DetDLP.S8N.MomentSem
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSem

open S8I.ECQueryCount
noncomputable section

/-- With two copies, the same seed is shared by an ordered pair of allowed tuples. -/
def doubleEquiv {p m T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hm : 1 ≤ m) (hT : T ≤ p) (η : List Bool) (hη : η.length ≤ m*4*bitLen p) :
    Physical E hm 2 T η ≃ Double p m E T η :=
  (noOutputEquiv E hm hT η hη 2 (by decide)).trans
    (Equiv.sigmaCongrRight (fun _ => finTwoArrowEquiv _))

theorem doubleCard {p m T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hm : 1 ≤ m) (hT : T ≤ p) (η : List Bool) (hη : η.length ≤ m*4*bitLen p) :
    Fintype.card (Physical E hm 2 T η) = value p m E T η 2 :=
  (Fintype.card_congr (doubleEquiv E hm hT η hη)).trans (double_card p m E T η)

end
end DetDLP.S8N.MomentSem
end

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentSem

open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank RangeRows HashRows GateRoutes
open S8H.ECPointArithmetic S8K.ECAddArithmetic S8O.ECAddLayout
open S8M.ECMapRows S8M.ECFoldEquiv S8M.ECAtomSlot

noncomputable section
variable {p m T : ℕ} [Fact p.Prime] {s : Shape}
variable (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (hp : 3 < p)

abbrev shorten := S8K.SWEquiv.equiv E (S8K.SWEquiv.six_ne_zero hp)
abbrev mappedShape (p : ℕ) := mapShape (width p) (GateSemantics.e p)
abbrev nodeShape (p : ℕ) := slotShape (width p) (GateSemantics.e p)

def mapCert (P : E.toAffine.Point) :=
  (mapBlock_unique E hp w3_m5_modmul_r2 P).exists.choose

theorem mapCertOutput (P : E.toAffine.Point) :
    output (mapCert E hp P) = coords (shorten E hp P) :=
  ecToSW_sound E hp w3_m5_modmul_r2 P _ _
    ((ecToSW_lift E _ _ _).1 _ (mapBlock_unique E hp w3_m5_modmul_r2 P).exists.choose_spec)

abbrev mapW {p : ℕ} (f : Path (mappedShape p) s) : Wires s :=
  (RoutesV2.mapFlag f, RoutesV2.mapX f, RoutesV2.mapY f)

abbrev pointW {p : ℕ} (f : Path (nodeShape p) s) : Wires s :=
  (RoutesV2.pointFlag f, RoutesV2.pointX f, RoutesV2.pointY f)

theorem regionAt {l : Shape} (q : Path l s) (u : Bits (s.size+1)) (v : l.Data)
    (H : ∀ a, (q a).get (rawOf s u) = a.get v) : At q u v :=
  fun a => (Addr.correct (q a) (u ∘ Fin.castSucc)).symm.trans (H a)

theorem atomPointRead (S : ECSeed p m) (hT : T ≤ p) (i : Fin m)
    (f : Path (nodeShape p) s) (u : Bits (s.size+1)) (v : {v // sliceOK S i E T v})
    (H : At f u v.val) : Reads (pointW f) u (coords (slotEquiv S i hT v).val) := by
  obtain ⟨hf,hx,hy⟩ := slotEquiv_coords S i hT v
  refine ⟨(H (.fst CurveRows.flag)).trans hf.symm, ?_, ?_⟩
  · rw [hx]
    exact word_eval (fun a => f (.fst (xa (.fst a)))) u _ (fun i =>
      ((Ref.reg _).correct u).trans (H (.fst (xa (.fst (.word i))))))
  · rw [hy]
    exact word_eval (fun a => f (.fst (ya (.fst a)))) u _ (fun i =>
      ((Ref.reg _).correct u).trans (H (.fst (ya (.fst (.word i))))))

/-- All auxiliary registers of one physically routed conversion are fixed by the input point. -/
theorem mapRowsUnique (P : E.toAffine.Point) (f : Path (mappedShape p) s)
    (a : Wires s) (u : Bits (s.size+1)) (z : (mappedShape p).Data)
    (H : At f u z) (hP : Reads a u (coords P)) :
    (mapBlock (GateSemantics.hd p) p E.b₂.val E.a₁.val E.a₃.val
      a.1 a.2.1 a.2.2 f).OK u ↔ z = sliceData (mapCert E hp P) := by
  let t := mapCert E hp P
  have ht := (mapBlock_unique E hp w3_m5_modmul_r2 P).exists.choose_spec
  have ok (H' : At f u (sliceData t)) :=
    (mapBlock_iff E _ t f u _ _ _ H' hP.1 hP.2.1 hP.2.2).mpr ht
  constructor
  · intro yes
    apply (acceptedSlice_unique E hp w3_m5_modmul_r2 P).unique
      ⟨_,f,u,a.1,a.2.1,a.2.2,H,hP.1,hP.2.1,hP.2.2,yes⟩
    let B := mappedShape p
    let w : Bits (B.size+1) := Fin.lastCases false (B.decode.symm (sliceData t))
    have atw : At id w (sliceData t) := by
      intro k
      change w k.index.castSucc = _
      simp [w,← Addr.correct k (B.decode.symm (sliceData t))]
    exact ⟨B,id,w,.pin (coords P).1,pub _,pub _,atw,rfl,fun _ => rfl,fun _ => rfl,
      (mapBlock_iff E _ t id w _ _ _ atw rfl (fun _ => rfl) (fun _ => rfl)).mpr ht⟩
  · intro eq
    rw [eq] at H
    exact ok H

theorem mapPointRead (P : E.toAffine.Point) (f : Path (mappedShape p) s)
    (u : Bits (s.size+1)) (H : At f u (sliceData (mapCert E hp P))) :
    Reads (mapW f) u (coords (shorten E hp P)) := by
  let t := mapCert E hp P
  rw [←mapCertOutput]
  refine ⟨H (.fst (.fst .bit)), ?_, ?_⟩
  · change evalWord _ _ ((zmodEquiv (fits p).le) t.1.2.1).val
    rw [GateSemantics.resVal]
    exact word_eval (fun k => f (.fst (.snd (.fst (.fst k))))) u _ (fun i =>
      ((Ref.reg _).correct u).trans (H (.fst (.snd (.fst (.fst (.word i)))))))
  · change evalWord _ _ ((zmodEquiv (fits p).le) t.1.2.2).val
    rw [GateSemantics.resVal]
    exact word_eval (fun k => f (.fst (.snd (.snd (.fst k))))) u _ (fun i =>
      ((Ref.reg _).correct u).trans (H (.fst (.snd (.snd (.fst (.word i)))))))

end
end DetDLP.S8N.MomentSem
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSem

open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank RangeRows HashRows GateRoutes
open S8H.ECPointArithmetic S8K.ECAddArithmetic S8M.ECFoldEquiv S8M.ECMapRows

noncomputable section
variable {p : ℕ} [Fact p.Prime] {s : Shape}

abbrev targetShape (p : ℕ) := RoutesV2.targetShape (width p)
abbrev targetW {p : ℕ} (f : Path (targetShape p) s) : Wires s :=
  (RoutesV2.targetFlag f,RoutesV2.targetX f,RoutesV2.targetY f)

def packedTarget (c : Coords p) : (targetShape p).Data :=
  (c.1,((zmodEquiv (fits p).le).symm c.2.1).val,((zmodEquiv (fits p).le).symm c.2.2).val)

/-- The fold reads exactly the finite coordinate words of its common target. -/
def targetMatches (a : Wires s) (u : Bits (s.size+1)) (c : Coords p) : Prop :=
  a.1.eval u = c.1 ∧ (∀ i : Fin (width p), (a.2.1 i).eval u = c.2.1.val.testBit i) ∧
  (∀ i : Fin (width p), (a.2.2 i).eval u = c.2.2.val.testBit i)

private theorem wordUnique (w : Triple (width p)) (x : ZMod p) (h : below p w)
    (e : ∀ i : Fin (width p), (value w.1).val.testBit i = x.val.testBit i) :
    w = ((zmodEquiv (fits p).le).symm x).val := by
  let Z := zmodEquiv (fits p).le
  have eq : Z ⟨w,h⟩ = x := by
    apply ZMod.val_injective
    rw [GateSemantics.resVal]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < width p
    · exact e ⟨i,hi⟩
    · have pw : 2^(width p) ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow ((value w.1).isLt.trans_le pw),
        Nat.testBit_lt_two_pow (x.val_lt.trans_le ((fits p).le.trans pw))]
  have hf := congrArg Z.symm eq
  rw [Equiv.symm_apply_apply] at hf
  exact congrArg Subtype.val hf

private theorem wordPacked (x : ZMod p) :
    (value (((zmodEquiv (fits p).le).symm x).val).1).val = x.val :=
  (GateSemantics.resVal _ ((zmodEquiv (fits p).le).symm x).prop).symm.trans
    (congrArg ZMod.val ((zmodEquiv (fits p).le).apply_symm_apply x))

omit [Fact p.Prime] in
private theorem targetReads (f : Path (targetShape p) s) (u : Bits (s.size+1))
    (w : (targetShape p).Data) (H : At f u w) :
    (targetW f).1.eval u = w.1 ∧
    evalWord (targetW f).2.1 u (value w.2.1.1).val ∧
    evalWord (targetW f).2.2 u (value w.2.2.1).val := by
  refine ⟨H (.fst .bit),?_,?_⟩
  · exact word_eval (fun a => f (.snd (.fst (.fst a)))) u _ (fun i =>
      ((Ref.reg _).correct u).trans (H (.snd (.fst (.fst (.word i))))))
  · exact word_eval (fun a => f (.snd (.snd (.fst a)))) u _ (fun i =>
      ((Ref.reg _).correct u).trans (H (.snd (.snd (.fst (.word i))))))

/-- The target includes two comparison certificates. Once both words and the
infinity flag are fixed by a fold, these auxiliary bits are uniquely fixed too. -/
theorem targetUnique {C : WeierstrassCurve (ZMod p)} (P : C.toAffine.Point)
    (f : Path (targetShape p) s) (u : Bits (s.size+1))
    (w : (targetShape p).Data) (H : At f u w) :
    (RoutesV2.targetBlock p f).OK u ∧ targetMatches (targetW f) u (coords P) ↔
      w = packedTarget (coords P) := by
  have X := checker_iff p (fun a => f (.snd (.fst a))) u w.2.1 (fun a => H _)
  have Y := checker_iff p (fun a => f (.snd (.snd a))) u w.2.2 (fun a => H _)
  have R := targetReads f u w H
  delta RoutesV2.targetBlock
  rw [joinB_iff,joinB_iff,X,Y,rows_iff]
  constructor
  · rintro ⟨⟨hx,hy,_⟩,hf,h1,h2⟩
    exact Prod.ext (R.1.symm.trans hf) (Prod.ext
      (wordUnique _ _ hx (fun i => (R.2.1 i).symm.trans (h1 i)))
      (wordUnique _ _ hy (fun i => (R.2.2 i).symm.trans (h2 i))))
  · rintro rfl
    have Pread : Reads (targetW f) u (coords P) := by
      refine ⟨R.1,?_,?_⟩
      · simpa only [packedTarget,wordPacked] using R.2.1
      · simpa only [packedTarget,wordPacked] using R.2.2
    refine ⟨⟨((zmodEquiv (fits p).le).symm _).prop,((zmodEquiv (fits p).le).symm _).prop,?_⟩,
      Pread.1,fun i => Pread.2.1 i,fun i => Pread.2.2 i⟩
    intro i
    change decide ((!((targetW f).1.eval u)) ||
      (((targetW f).2.1 i).eval u = false ∧ ((targetW f).2.2 i).eval u = false)) = true
    rw [Pread.1,Pread.2.1 i,Pread.2.2 i]
    cases P <;> simp [coords]

theorem packedTarget_injective {C : WeierstrassCurve (ZMod p)} :
    Function.Injective (fun P : C.toAffine.Point => packedTarget (coords P)) := by
  intro P Q eq
  have hf := congrArg (fun z : (targetShape p).Data => z.1) eq
  have g (x y : ZMod p) (h : ((zmodEquiv (fits p).le).symm x).val =
      ((zmodEquiv (fits p).le).symm y).val) : x = y :=
    (zmodEquiv (fits p).le).symm.injective (Subtype.ext h)
  have hx := g _ _ (congrArg (fun z : (targetShape p).Data => z.2.1) eq)
  have hy := g _ _ (congrArg (fun z : (targetShape p).Data => z.2.2) eq)
  have e : coords P = coords Q := Prod.ext hf (Prod.ext hx hy)
  cases P <;> cases Q <;> simp_all [coords]

end
end DetDLP.S8N.MomentSem
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSem

open S8H0 RegisterMap NamedBlocks ResidueWires HashRows GateRoutes
open S8H.ECPointArithmetic S8K.ECAddArithmetic S8M.ECMapRows S8M.ECFoldEquiv

noncomputable section
section Indices
variable {m : ℕ}

def headIndex (hm : 1 ≤ m) : Fin m := ⟨0, by omega⟩
def tailIndex (i : Fin (m-1)) : Fin m := ⟨i.val + 1, by have h := i.isLt; omega⟩

def firstMapIndex (hm : 1 ≤ m) (k : Fin 2) : Fin (2*m) :=
  ⟨k.val * m, by have klt := k.isLt; interval_cases k.val <;> simp_all <;> omega⟩
def nextMapIndex (k : Fin 2) (i : Fin (m-1)) : Fin (2*m) :=
  ⟨k.val * m + i.val + 1, by
    have klt := k.isLt
    have ilt := i.isLt
    interval_cases k.val <;> simp_all <;> omega⟩

def flatten {A : Type} (F : Fin 2 → Fin m → A) (j : Fin (2*m)) :=
  F (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2

private theorem flattenFirst {A : Type} (hm : 1 ≤ m) (F : Fin 2 → Fin m → A) (k : Fin 2) :
    flatten F (firstMapIndex hm k) = F k (headIndex hm) := by
  have eq : firstMapIndex hm k = finProdFinEquiv (k,headIndex hm) := by
    apply Fin.ext
    simp [firstMapIndex,headIndex,Nat.mul_comm]
  rw [eq,flatten,Equiv.symm_apply_apply]

private theorem flattenNext {A : Type} (F : Fin 2 → Fin m → A) (k : Fin 2) (i : Fin (m-1)) :
    flatten F (nextMapIndex k i) = F k (tailIndex i) := by
  have eq : nextMapIndex k i = finProdFinEquiv (k,tailIndex i) := by
    apply Fin.ext
    change k.val * m + i.val + 1 = i.val + 1 + m*k.val
    ac_rfl
  rw [eq,flatten,Equiv.symm_apply_apply]

private theorem firstAddTail {A : Type} [AddCommMonoid A] (hm : 1 ≤ m) (F : Fin m → A) :
    F (headIndex hm) + ∑ i : Fin (m-1), F (tailIndex i) = ∑ i, F i := by
  cases m with
  | zero => omega
  | succ n => exact (Fin.sum_univ_succ F).symm

end Indices

variable {m p : ℕ} [Fact p.Prime] {s : Shape}
variable (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (hp : 3 < p) (hm : 1 ≤ m)

abbrev productShape (m p : ℕ) := RoutesV2.productShape m (width p) (GateSemantics.e p)
abbrev families (C : WeierstrassCurve (ZMod p)) (m : ℕ) := Fin 2 → Fin m → C.toAffine.Point

abbrev foldStart (P : families E m) (k : Fin 2) := shorten E hp (P k (headIndex hm))
abbrev foldTail (P : families E m) (k : Fin 2) (i : Fin (m-1)) :=
  shorten E hp (P k (tailIndex i))
abbrev sideSum (P : families E m) (k : Fin 2) := ∑ i, P k i
abbrev shortSum (P : families E m) (k : Fin 2) := shorten E hp (sideSum E P k)

def packedProduct (P : families E m) : (productShape m p).Data :=
  (packedTarget (coords (shortSum E hp P 0)),
   fun j => sliceData (mapCert E hp (flatten P j)),
   fun k => FreeFold.canonical E (foldStart E hp hm P k) (foldTail E hp P k))

def actualMaps (f : Path (productShape m p) s) (a : Fin (2*m) → Wires s)
    (u : Bits (s.size+1)) (j : Fin (2*m)) :=
  (mapBlock (GateSemantics.hd p) p E.b₂.val E.a₁.val E.a₃.val
    (a j).1 (a j).2.1 (a j).2.2 (RoutesV2.mapPath f j)).OK u

def actualFolds (f : Path (productShape m p) s) (u : Bits (s.size+1)) (k : Fin 2) :=
  (FreeFold.block E (mapW (RoutesV2.mapPath f (firstMapIndex hm k)))
    (fun i => mapW (RoutesV2.mapPath f (nextMapIndex k i)))
    (targetW (RoutesV2.target f)) (RoutesV2.foldPath f k)).OK u

def productRows (f : Path (productShape m p) s) (a : Fin (2*m) → Wires s) (u : Bits (s.size+1)) :=
  (RoutesV2.targetBlock p (RoutesV2.target f)).OK u ∧
  (∀ j, actualMaps E f a u j) ∧ (∀ k, actualFolds E hm f u k)

/-- Two physical folds share their target. The point maps, both addition transcripts,
and the target including its range witnesses are fixed by the two input tuples. -/
theorem productRows_iff (P : families E m) (f : Path (productShape m p) s)
    (a : Fin (2*m) → Wires s) (u : Bits (s.size+1)) (z : (productShape m p).Data)
    (H : At f u z) (ha : ∀ j, Reads (a j) u (coords (flatten P j))) :
    productRows E hm f a u ↔ z = packedProduct E hp hm P ∧ sideSum E P 0 = sideSum E P 1 := by
  have Ta : At (RoutesV2.target f) u z.1 := fun i => H (.fst i)
  have Ma (j : Fin (2*m)) : At (RoutesV2.mapPath f j) u (z.2.1 j) :=
    fun i => H (.snd (.fst (.vec j i)))
  have Fa (k : Fin 2) : At (RoutesV2.foldPath f k) u (z.2.2 k) :=
    fun i => H (.snd (.snd (.vec k i)))
  have maps (j : Fin (2*m)) := mapRowsUnique E hp (flatten P j) (RoutesV2.mapPath f j)
    (a j) u (z.2.1 j) (Ma j) (ha j)
  have folds (hmap : ∀ j, z.2.1 j = sliceData (mapCert E hp (flatten P j))) (k : Fin 2) :
      actualFolds E hm f u k ↔ z.2.2 k = FreeFold.canonical E (foldStart E hp hm P k)
        (foldTail E hp P k) ∧ targetMatches (targetW (RoutesV2.target f)) u
          (coords (shortSum E hp P k)) := by
    have read (j : Fin (2*m)) := mapPointRead E hp (flatten P j) (RoutesV2.mapPath f j)
      u ((hmap j) ▸ Ma j)
    have first := read (firstMapIndex hm k)
    rw [flattenFirst] at first
    have next (i : Fin (m-1)) :
        Reads (mapW (RoutesV2.mapPath f (nextMapIndex k i))) u (coords (foldTail E hp P k i)) := by
      simpa only [flattenNext] using read (nextMapIndex k i)
    have accept := FreeFold.rows E (foldStart E hp hm P k) (foldTail E hp P k)
      _ _ (targetW (RoutesV2.target f)) (RoutesV2.foldPath f k) u _ (Fa k) first next
    have sum : foldStart E hp hm P k + ∑ i, foldTail E hp P k i = shortSum E hp P k := by
      change shorten E hp _ + ∑ i, shorten E hp _ = shorten E hp _
      rw [←map_sum,←map_add,firstAddTail]
    rw [sum] at accept
    exact accept
  have tgt (k : Fin 2) := targetUnique (shortSum E hp P k) (RoutesV2.target f) u z.1 Ta
  constructor
  · rintro ⟨ht,hmaps,hfolds⟩
    have meq j := (maps j).mp (hmaps j)
    have result k := (folds meq k).mp (hfolds k)
    have common k := (tgt k).mp ⟨ht,(result k).2⟩
    exact ⟨Prod.ext (common 0) (Prod.ext (funext meq) (funext fun k => (result k).1)),
      (shorten E hp).injective (packedTarget_injective ((common 0).symm.trans (common 1)))⟩
  · rintro ⟨eq,coll⟩
    have meq j := congrArg (fun q : (productShape m p).Data => q.2.1 j) eq
    have feq k := congrArg (fun q : (productShape m p).Data => q.2.2 k) eq
    have common (k : Fin 2) : z.1 = packedTarget (coords (shortSum E hp P k)) := by
      have e := congrArg Prod.fst eq
      fin_cases k
      · exact e
      · change z.1 = packedTarget (coords (shorten E hp (sideSum E P 1)))
        rw [← coll]
        exact e
    have ok k := (tgt k).mpr (common k)
    exact ⟨(ok 0).1, fun j => (maps j).mpr (meq j),
      fun k => (folds meq k).mpr ⟨feq k,(ok k).2⟩⟩

end
end DetDLP.S8N.MomentSem
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSem

open S8H0 RegisterMap NamedBlocks GateRoutes ResidueWires
open S8M.ECMapRows S8M.ECFoldEquiv S8M.ECAtomSlot
open S8N.ECSeedBank S8I.ECQueryCount M89S1

noncomputable section
variable {p m T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (hp : 3 < p) (hm : 1 ≤ m) (hT : T ≤ p) (η : List Bool) (hη : η.length ≤ m*4*bitLen p)

abbrev pointsOf (S : ECSeed p m) (a : Fin 2 → Slots (T:=T) E S) : families E m :=
  fun k => (SeedAtomEquiv.atomBank S hT (a k)).val

def collisionTest (r : (shape p m 3).Data) : Prop :=
  ∃ hs : ecSeedOK p m η r.1,
  let S := ((SeedAtomEquiv.seed p m η hη) ⟨r.1,hs⟩).val
  ∃ ha : ∀ (k : Fin 2) (i : Fin m), sliceOK S i E T (r.2.1 k i),
  let P := pointsOf E hT S (fun k => ⟨r.2.1 k,ha k⟩)
  sideSum E P 0 = sideSum E P 1 ∧ ∀ t, r.2.2 t = packedProduct E hp hm P

private abbrev inputW {p m : ℕ} (j : Fin (2*m)) : Wires (shape p m 3) :=
  pointW (RoutesV2.atom (s:=shape p m 3) id
    (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)

/-- Acceptance of the entire j=3 row network fixes precisely one shared-seed
pair, its common sum, and every word in the product bank. -/
theorem collisionRows (u : bits (p:=p) (m:=m) 3) :
    (rowsAt E hm 3 T η).OK u ↔ collisionTest E hp hm hT η hη (raw (p:=p) (m:=m) 3 u) := by
  let r := raw (p:=p) (m:=m) 3 u
  let q : Path (shape p m 3) (shape p m 3) := id
  have prod (hs : ecSeedOK p m η r.1)
      (ha : ∀ (k : Fin 2) (i : Fin m), sliceOK ((SeedAtomEquiv.seed p m η hη) ⟨r.1,hs⟩).val i E T (r.2.1 k i))
      (t : Fin (RoutesV2.outputs 3)) :
      let S := ((SeedAtomEquiv.seed p m η hη) ⟨r.1,hs⟩).val
      let P := pointsOf E hT S (fun k => ⟨r.2.1 k,ha k⟩)
      productRows E hm (RoutesV2.product q t) inputW u ↔
      r.2.2 t = packedProduct E hp hm P ∧ sideSum E P 0 = sideSum E P 1 := by
    let S := ((SeedAtomEquiv.seed p m η hη) ⟨r.1,hs⟩).val
    let P := pointsOf E hT S (fun k => ⟨r.2.1 k,ha k⟩)
    apply productRows_iff E hp hm P (RoutesV2.product q t) inputW u (r.2.2 t)
      (regionAt _ u _ (fun _ => rfl))
    intro j
    let k := (finProdFinEquiv.symm j).1
    let i := (finProdFinEquiv.symm j).2
    exact atomPointRead E S hT i (RoutesV2.atom q k i) u ⟨r.2.1 k i,ha k i⟩
      (regionAt _ u _ (fun _ => rfl))
  have seedOK := seedRowsAt η hη 3 u
  apply (RoutesV2.network_iff (GateSemantics.hd p) hm p T (GateSemantics.coeff E)
    E.b₂.val (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val 3 η q u).trans
  constructor
  · rintro ⟨s,a,out⟩
    let hs := seedOK.mp s
    let ha := fun (k : Fin 2) (i : Fin m) => (atomRowsAt E η hη 3 u hs k i).mp (a k i)
    have h t := (prod hs ha t).mp (out t)
    exact ⟨hs,ha,(h ⟨0,by decide⟩).2,fun t => (h t).1⟩
  · rintro ⟨hs,ha,coll,pack⟩
    exact ⟨seedOK.mpr hs,fun k i => (atomRowsAt E η hη 3 u hs k i).mpr (ha k i),
      fun t => (prod hs ha t).mpr ⟨pack t,coll⟩⟩

end
end DetDLP.S8N.MomentSem
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSem

open S8N.ECSeedBank S8I.ECQueryCount M89S1
noncomputable section
variable {p m T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (hp : 3 < p) (hm : 1 ≤ m) (hT : T ≤ p) (η : List Bool) (hη : η.length ≤ m*4*bitLen p)

private abbrev GoodPairs (S : ECSeed p m) := {a : Fin 2 → Slots (T:=T) E S //
  sideSum E (pointsOf E hT S a) 0 = sideSum E (pointsOf E hT S a) 1}

private def splitCollisionBank :
    {r : (shape p m 3).Data // collisionTest E hp hm hT η hη r} ≃
    Σ s : SeedValid (p:=p) (m:=m) η, GoodPairs E hT ((SeedAtomEquiv.seed p m η hη) s).val where
  toFun r :=
    let hs := r.property.choose
    let ha := r.property.choose_spec.choose
    ⟨⟨r.val.1,hs⟩, ⟨fun k => ⟨r.val.2.1 k,ha k⟩,r.property.choose_spec.choose_spec.1⟩⟩
  invFun
    | ⟨s,⟨a,c⟩⟩ =>
      let S := ((SeedAtomEquiv.seed p m η hη) s).val
      let P := pointsOf E hT S a
      ⟨(s.val,(fun k => (a k).val),fun _ => packedProduct E hp hm P),
        ⟨s.prop,fun k => (a k).property,c,fun _ => rfl⟩⟩
  left_inv := by
    rintro ⟨r,h⟩
    exact Subtype.ext (Prod.ext rfl (Prod.ext rfl
      (funext fun t => (h.choose_spec.choose_spec.2 t).symm)))
  right_inv := by rintro ⟨s,a,c⟩; rfl

private def slotsCollision (S : ECSeed p m) : GoodPairs E hT S ≃ Collision (ecFactorBlock E T S) := by
  let e := (Equiv.piCongrRight fun _ : Fin 2 => SeedAtomEquiv.atomBank (E:=E) S hT).trans
    (finTwoArrowEquiv _)
  exact Equiv.subtypeEquiv e (fun _ => Iff.rfl)

/-- Satisfying assignments of the actual anchored collision circuit correspond
bijectively to one prefix-consistent seed and an ordered pair of tuples with equal sum. -/
def equalSumEquiv : Physical E hm 3 T η ≃ EqualSum p m E T η := by
  refine (physicalEquiv E hm 3 T η).trans ?_
  refine (Equiv.subtypeEquivRight (q:=collisionTest E hp hm hT η hη) (fun v => ?_)).trans ?_
  · simpa only [raw_extend] using collisionRows E hp hm hT η hη (extend (p:=p) (m:=m) 3 v)
  · exact (splitCollisionBank E hp hm hT η hη).trans
      (Equiv.sigmaCongr (SeedAtomEquiv.seed p m η hη)
        (fun s => slotsCollision E hT ((SeedAtomEquiv.seed p m η hη) s).val))

end
end DetDLP.S8N.MomentSem
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSem

open S8I.ECQueryCount
noncomputable section

variable {p m T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (hp : 3 < p) (hm : 1 ≤ m) (hT : T ≤ p) (η : List Bool) (hη : η.length ≤ m*4*bitLen p)

def massEquiv : Physical E hm 0 T η ≃ Mass p m η := by
  refine (noOutputEquiv E hm hT η hη 0 (by decide)).trans ?_
  exact {
    toFun := Sigma.fst
    invFun := fun s => ⟨s, Fin.elim0⟩
    left_inv := by
      rintro ⟨s, f⟩
      exact congrArg (Sigma.mk s) (funext fun i => Fin.elim0 i)
    right_inv := fun _ => rfl }

def oneTupleEquiv : Physical E hm 1 T η ≃ Single p m E T η :=
  (noOutputEquiv E hm hT η hη 1 (by decide)).trans
    (Equiv.sigmaCongrRight (fun _ => Equiv.funUnique (Fin 1) _))

include hp hT hη in
/-- Each of the four physical circuits counts the corresponding elliptic-curve moment. -/
theorem momentCard (j : Fin 4) :
    Fintype.card (Physical E hm j T η) = value p m E T η j := by
  fin_cases j
  · exact (Fintype.card_congr (massEquiv E hm hT η hη)).trans (mass_card p m E T η)
  · exact (Fintype.card_congr (oneTupleEquiv E hm hT η hη)).trans (single_card p m E T η)
  · exact doubleCard E hm hT η hη
  · exact (Fintype.card_congr (equalSumEquiv E hp hm hT η hη)).trans (equalSum_card p m E T η)

end
end DetDLP.S8N.MomentSem
end

set_option autoImplicit false
open DetDLP DetDLP.S8N DetDLP.S8H0 DetDLP.S8H0.NamedBlocks DetDLP.S8J.CircuitRealizes

theorem DetDLP.s8n_moment_assignment_count_inline {p m T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hp : 3 < p) (hm : 1 ≤ m) (hT : T ≤ p) (η : List Bool) (hη : η.length ≤ m*4*bitLen p)
    (j : Fin 4) :
    let bank := RoutesV2.bank j m (GateSemantics.d p) (GateSemantics.e p)
    let rows := RoutesV2.network (GateSemantics.hd p) hm p T (GateSemantics.coeff E)
      E.b₂.val (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val j η id
    let net := joinB (PointGraph.zeroLast bank.size) rows
    let B := AnchoredLayout.block net.core (bank.size+1)
    let W := AnchoredLayout.wiring net.core net.name
    let A := circuit B W
    Fintype.card {b : Fin A.nb → Bool // ∀ g, test B W g (fun e => b (A.bit e.1)) = true} =
      S8I.ECQueryCount.value p m E T η j :=
  MomentSem.momentCard E hp hm hT η hη j
end
end



section
section
set_option autoImplicit false
namespace DetDLP.S8N.MomentHeader
open Groundwork S8C S8H

def scale (m b : ℕ) : ℕ := 524288 * m * (b + 2)

def sizeField (w : List Bool) : ℕ :=
  let b := S8G.FpMoment.Code.width (S8M.PortPoly.prime w)
  scale (S8G.FpMoment.Code.slots b) b

theorem sizeField_poly : PolyT sizeField := by
  have hb := S8G.FpMoment.Code.width_poly S8N.PortPoly.prime_poly
  exact PolyT.mul (PolyT.mul (PolyT.const 524288) (S8G.FpMoment.Code.slots_poly hb))
    (PolyT.add hb (PolyT.const 2))

def make (a : S8G.FpMoment.Code.Addresses) (w : List Bool) : List Bool :=
  outerPacket w (WirePacket.packet (a.nv w) (a.ne w) (a.src w) (a.dst w)) (sizeField w)

theorem make_poly (a : S8G.FpMoment.Code.Addresses) (h : a.Uniform) : PolyT (make a) :=
  outerPacket_poly PolyT.id' (WirePacket.packet_poly h.nv h.ne h.vert h.edge h.src h.dst) sizeField_poly

theorem degreeBudget {m b : ℕ} (hm : 1 ≤ m) :
    max 12 (Nat.ceil (136*((b:ℝ)+2)^((3:ℝ)/4))) ≤ Nat.ceil ((scale m b:ℝ)^((9:ℝ)/10)) := by
  apply (S8G.FpMoment.degreeBudget hm).trans
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact_mod_cast (show S8G.FpMoment.scale m b ≤ scale m b by
    unfold scale S8G.FpMoment.scale
    exact Nat.mul_le_mul_right (b+2) (Nat.mul_le_mul_right m (by decide : 65536 ≤ 524288)))

end DetDLP.S8N.MomentHeader
end
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentTag
open M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

def word (j : Fin 4) (T : ℕ) (η : List Bool) :=
  queryWord 2 (encodeCurveInput p E) [countWord j.val,countWord T,η]

/-- The outer tag can be read before inspecting the query's dependent indices. -/
theorem tagIntro (make port : List Bool → List Bool) (L : ℕ) (hm : Groundwork.PolyT make)
    (he : Groundwork.PolyT port)
    (h : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      ∀ (j : Fin 4) (T : ℕ) (η : List Bool), T ≤ p →
      η.length ≤ blockCount (bitLen p)*4*bitLen p →
      S8C.Realizes make port L (word E j T η) (bitLen p)
        (S8I.ECQueryCount.value p (blockCount (bitLen p)) E T η j)) :
    S8C.TagSpec [2] := by
  refine ⟨make,port,L,hm,he,?_⟩
  rintro t ht base payload b n hq
  obtain rfl : t = 2 := by simpa using ht
  generalize hw : queryWord 2 base payload = w at hq ⊢
  have tag : Groundwork.PolyT.bval (DetDLP_W1_Queries.first w) = 2 := by subst w; simp [queryWord]
  cases hq <;> simp only [queryWord,DetDLP_W1_Queries.first_cons,id_eq,DetDLP_W1_Queries.decode_count] at tag
  all_goals first | contradiction | exact h _ (by assumption) _ _ _ _ (by assumption) (by assumption)

end DetDLP.S8N.MomentTag
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8N.PortEval
open S8H0 S8H.PortCombinators RegisterMap NamedBlocks GateRoutes RangeRows HashRows
open DetDLP.S8G.SeedAndAtomBank DetDLP.S8N.RoutesV2
open DetDLP.S8M.PortPoly (tile tab)
open DetDLP.S8N.PortPoly (seedSlotG)

theorem seedSlotFits {s : Shape} {d : ℕ} (p : ℕ)
    (q : GateRoutes.Path (seedSlot d) s) :
    FitsG (seedSlotG d p) (DetDLP.S8N.ECSeedBank.ecSeedSlotBlock p q).core := by
  refine catB (range_spec ..) (catB (range_spec ..) (add_spec _ ?_ ?_ ?_ ?_))
  all_goals intros; simp [DetDLP.S8G.SeedAndAtomBank.seedA,GateRoutes.word,HashRows.pub,HashRows.padded,regR,pinR,Ref.read] <;> split_ifs <;> simp_all

theorem tileFits {s : Shape} {n : ℕ} (g : GC) (b : Fin n → B (s.size+1))
    (h : ∀ i, FitsG g (b i).core) : FitsG (tile n g) (allRows n b).core := by
  cases n with
  | zero => exact ⟨Nat.zero_mul _,fun i => Fin.elim0 i⟩
  | succ n => induction n with
    | zero => refine ⟨(Nat.one_mul _).trans (h 0).1,fun i w => ?_⟩; exact (congrArg (fun j => g.2 j w) (Nat.mod_eq_of_lt ((h 0).1.symm ▸ i.isLt))).trans ((h 0).2 i w)
    | succ n ih =>
      have H := catB (h 0) (ih (fun i => b i.succ) fun i => h i.succ)
      change FitsG _ (joinB (b 0) (allRows (n+1) fun i => b i.succ)).core
      refine ⟨(Nat.succ_mul _ _).trans ((Nat.add_comm ..).trans H.1),fun i w => ?_⟩
      rw [←H.2 i w]; simp only [tile,tab,catG]; split_ifs with hi
      · rw [Nat.mod_eq_of_lt hi]
      · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi); simp [hk]

theorem seedRowsFits {s : Shape} {m d : ℕ} (p : ℕ)
    (q : Path (DetDLP.S8N.ECSeedBank.ecSeedShape m d) s) :
    FitsG (tile m (catG (seedSlotG d p) (seedSlotG d p)))
      (DetDLP.S8G.SeedAndAtomBank.allRows m (fun i => joinB
        (DetDLP.S8N.ECSeedBank.ecSeedSlotBlock p (seedSlotPath q i false))
        (DetDLP.S8N.ECSeedBank.ecSeedSlotBlock p (seedSlotPath q i true)))).core := by
  apply tileFits
  intro i
  apply catB
  · exact seedSlotFits p (seedSlotPath q i false)
  · exact seedSlotFits p (seedSlotPath q i true)
end DetDLP.S8N.PortEval
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace DetDLP.S8N.PortEval
open S8H0 S8H.PortCombinators RegisterMap NamedBlocks GateRoutes RangeRows HashRows S8J S8J.CircuitRealizes LocalGateEq
open DetDLP.S8G.SeedAndAtomBank DetDLP.S8N.RoutesV2

open S8M.PortPoly (bit prefixG)
abbrev edges {d : ℕ} (hd : 1 ≤ d) := (w4_M5GraphBounds.graph d hd).nE
variable {s : Shape} {d : ℕ}
abbrev Reads (r : Reader) (v : HashRows.Word s) := ∀ i b, r i b = (v i).read b
theorem wordReads {k : ℕ} (f : Path (.word k) s) : Reads (regR k) (GateRoutes.word f) := by intro i x; simp only [regR,GateRoutes.word,HashRows.padded]; split_ifs <;> rfl


theorem ecSeedFits {s : Shape} (p m : ℕ) (η : List Bool)
    (q : Path (ECSeedBank.ecSeedShape m (bitLen p+1)) s) :
    FitsG (PortPoly.ecSeedG m (bitLen p) (bitLen p+1) p η) (ecSeedBlockV2 p m η q).core := by
  refine catB (seedRowsFits p q) ⟨rfl,fun i w => ?_⟩
  rw [rows_local]
  by_cases h : i.val < m*4*bitLen p
  · have readSeed (a : Fin (bitLen p)) (y : Bool) (r : Path (seedSlot (bitLen p+1)) s) :
        (ECSeedBank.ecSeedA r a).read y = y ∧ (ECSeedBank.ecSeedB r a).read y = y := by
      have ha : a.val < bitLen p+1 := by omega
      simp only [ECSeedBank.ecSeedA, ECSeedBank.ecSeedB, S8G.SeedAndAtomBank.seedA,
        S8G.SeedAndAtomBank.seedB,GateRoutes.word,HashRows.padded,dif_pos ha,Ref.read,and_self]
    simp only [prefixG,bit,ecPrefixBit,dif_pos h,true_and,h,List.getD_eq_getElem _ _ i.isLt]
    split_ifs <;> simp only [(readSeed ..).1,(readSeed ..).2] <;> rfl
  · simp [prefixG,h]

section
open S8M.PortPoly (tab rd atomFixed)
theorem tile_one {k : ℕ} {g : GC} {A : B k} (h : FitsG g A.core) : FitsG (S8M.PortPoly.tile 1 g) A.core := by
  refine ⟨by simp [S8M.PortPoly.tile,tab,h.1],fun i w => ?_⟩; simpa only [S8M.PortPoly.tile,tab,Nat.mod_eq_of_lt (show i.val < g.1 by rw [h.1]; exact i.isLt)] using h.2 i w
theorem tiles_join {k n m : ℕ} {g : GC} {A B : NamedBlocks.B k} (ha : FitsG (S8M.PortPoly.tile n g) A.core) (hb : FitsG (S8M.PortPoly.tile m g) B.core) : FitsG (S8M.PortPoly.tile (n+m) g) (joinB A B).core := by
  have H := catB ha hb; refine ⟨by simpa only [S8M.PortPoly.tile,tab,catG,Nat.add_mul] using H.1,fun i w => ?_⟩
  rw [← H.2]; simp only [catG,S8M.PortPoly.tile,tab]; split_ifs with h
  · simp [h]
  · obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h); rw [hj]; simp [Nat.add_mod]
theorem tile_many {k n t : ℕ} {g : GC} (b : Fin (n+1) → B k) (h : ∀ i, FitsG (S8M.PortPoly.tile t g) (b i).core) : FitsG (S8M.PortPoly.tile ((n+1)*t) g) (RangeRows.many n b).core := by
  induction n with
  | zero => simpa [RangeRows.many] using h 0
  | succ n ih => rw [Nat.succ_mul,Nat.add_comm]; exact tiles_join (h 0) (ih (fun i => b i.succ) (fun i => h i.succ))

private theorem ranges {e : ℕ} (p : ℕ) : FitsG (S8M.PortPoly.tile 16 (rangeG d p)) (RangeRows.block d e p).core := by
  apply tiles_join (n:=2) (m:=14)
  · exact tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..))
  · exact tile_many (n:=6) (t:=2) _ fun i => tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..))

private theorem sixFits (hd : 1 ≤ d) (p : ℕ) (c : Coeff) : FitsG (S8M.PortPoly.hash (List.replicate d ()) d p 0 0 0) (HashRows.block p (S8H4.Routes.network.six hd p c)).core := by
  unfold S8M.PortPoly.hash genHashG HashRows.block; dsimp only [S8H4.Routes.network.six,GateRoutes.wires]
  refine catB (catB ?_ ?_) (catB ?_ (catB ?_ ?_))
  all_goals first | apply prod_spec | apply add_spec
  all_goals intros; simp only [Function.comp_apply,rd,if_pos,regR,pinR,S8H4.Routes.network.coord,GateRoutes.rword,GateRoutes.quot,GateRoutes.word,HashRows.padded,HashRows.pub,Ref.read] <;> split_ifs <;> rfl


end
theorem atomSlotFits {s : Shape} {d : ℕ} (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (A B C D : HashRows.Word s) (q : Path (S8M.ECAtomSlot.slotShape d (edges hd)) s)
    (ha : Reads (regR d) A) (hb : Reads (regR d) B)
    (hc : Reads (regR d) C) (he : Reads (regR d) D) :
    FitsG (PortPoly.atomSlotG (List.replicate d ()) d p T c)
      (S8M.ECAtomSlot.slotBlock hd p T c A B C D q).core := by
  unfold PortPoly.atomSlotG S8M.ECAtomSlot.slotBlock
  dsimp only
  refine catB ?_ ⟨rfl,fun i w => ?_⟩
  · refine catB (catG_spec (ranges p) (catB (many_spec fun i => hash_spec hd p c i.castSucc) ?_)) (catB (sixFits hd p c) (catB ?_ ?_))
    · refine ⟨rfl,fun i w => ?_⟩; unfold CurveRows.block; rw [rows_local]; rfl
    · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; cases h : w.getD 0 false <;> simp [zeroLastG,Ref.read,h]
    · apply add_spec <;> intros <;> simp only [regR,pinR,RangeRows.pad,Ref.read] <;> split_ifs <;> rfl
  rw [rows_local]
  have hi : i.val < d := i.isLt
  have hz : 0 < d := hd
  simp [S8H4.Routes.network.coord,S8H4.Routes.network.a6Reg,S8H4.Routes.network.b6Reg,
    GateRoutes.word,HashRows.padded,hi,hz,bit,←ha,←hb,←hc,←he,regR]
  rfl
end DetDLP.S8N.PortEval
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8N.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes LocalGateEq S8M S8M.PortPoly
open RangeRows HashRows
variable {s : Shape} {d e : ℕ}
private abbrev fstP {a b : Shape} (f : Path (.pair a b) s) : Path a s := fun j => f (.fst j)
private abbrev sndP {a b : Shape} (f : Path (.pair a b) s) : Path b s := fun j => f (.snd j)
private abbrev rwrd (f : Path (triple d) s) := word (fstP f)
private abbrev refw {n : ℕ} (f : Path (.word n) s) (i : Fin n) : Ref s := .reg (f (.word i))
def portWires (hd : 1 ≤ d) (p : ℕ) (a x b : Word s) (f : Path (ECMapRows.slot d e) s) : Wires d hd s :=
  let r := fstP f; let k := fstP (sndP r); let l := sndP k; let m := sndP l; let t := sndP f
  ⟨a,x,b,rwrd (fstP r),rwrd (fstP k),word (fstP l),word (fstP (fstP m)),word (fstP (sndP m)), word (fstP (sndP t)),fun i => .masked (p.testBit i) (sndP (sndP r) .bit),
   pad (refw (sndP (fstP m))),pad (refw (sndP (sndP m))),refw (fstP t), refw (fstP (sndP (sndP t))),refw (sndP (sndP (sndP t)))⟩
private theorem paddedProd (hd : 1 ≤ d) {a b z : Reader} {A B Z : HashRows.Word s} (f : Path (.word (edges hd)) s) (ha : Reads a A) (hb : Reads b B) (hz : Reads z Z) : FitsG (prodG (List.replicate d ()) d a b z) (HashRows.product hd A B Z (RangeRows.pad (fun i => .reg (f (.word i))))).core := by
  have H : (RangeRows.pad (n:=(w3_fpMulLayout d hd).nb) (fun i => Ref.reg (f (.word i)))) = (fun i => Ref.reg (f (.word ⟨i.val,i.isLt⟩))) := by funext i; exact dif_pos i.isLt
  rw [H]; exact prod_spec hd ha hb hz
theorem hashFits (hd : 1 ≤ d) (p a x b : ℕ) {A X B : HashRows.Word s} (ha : Reads (rd d a) A) (hx : Reads (rd d x) X) (hb : Reads (rd d b) B) (f : Path (ECMapRows.slot d (edges hd)) s) : FitsG (S8M.PortPoly.hash (List.replicate d ()) d p a x b) (HashRows.block p (portWires hd p A X B f)).core := by
  unfold S8M.PortPoly.hash genHashG HashRows.block portWires; dsimp only
  refine catB (catB ?_ ?_) (catB ?_ (catB ?_ ?_))
  · exact paddedProd hd _ ha hx (wordReads _)
  · exact paddedProd hd _ (wordReads _) (fun _ _ => rfl) (wordReads _)
  all_goals apply add_spec <;> intros <;> first | apply hb | (simp only [regR,pinR,rwrd,GateRoutes.word,HashRows.padded,HashRows.pub,Ref.read] <;> split_ifs <;> rfl)

theorem rowsReadFits {n k : ℕ} (r : Fin n → Fin k → Ref s) (f : ℕ → (Fin k → Bool) → Bool)
    (h : ∀ i j b, (r i j).read b = b) : FitsG (n, fun i w => f i (fun j => bit w j))
      (rows n k r (fun i => f i.val)).core := by
  refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; simp only [h]
private theorem maskFits (f : Ref s) (a b : Path (.word d) s) (hf : ∀ z, f.read z=z) :
    FitsG (d,fun _ w => bit w 1 == (!bit w 0 && bit w 2))
      (rows d 3 (fun i => ![f,word a i,word b i]) (fun _ v => v 1 == (!v 0 && v 2))).core := by
  apply rowsReadFits (f:=fun _ v => v 1 == (!v 0 && v 2)); intro i j z; fin_cases j <;> first | exact hf z | simp [word,HashRows.padded,i.isLt,Ref.read]
theorem mapFits (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) (fl : Ref s) (x y : HashRows.Word s) (q : Path (ECMapRows.mapShape d ((w4_M5GraphBounds.graph d hd).nE)) s) (hf : ∀ z, fl.read z = z) (hx : Reads (regR d) x) (hy : Reads (regR d) y) : FitsG (mapG (List.replicate d ()) d p b2 a1 a3) (ECMapRows.mapBlock hd p b2 a1 a3 fl x y q).core := by
  unfold mapG ECMapRows.mapBlock; dsimp only
  refine catB (tiles_join (n:=2) (m:=8) (tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..))) (tile_many (n:=3) (t:=2) _ fun _ => tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..)))) (catB ?_ (catB ?_ ?_))
  · refine catB ?_ (catB ?_ (catB ?_ ?_))
    all_goals apply hashFits <;> first | exact hx | exact hy | apply wordReads | intro i z; rfl
  · refine ⟨rfl,fun i w => ?_⟩; rw [eqs_local]; change (_ == _) = decide (_ = fl.read _); rw [hf]; rfl
  · apply tiles_join (n:=1) (m:=1)
    all_goals apply tile_one; exact maskFits fl _ _ hf
end DetDLP.S8N.PortEval
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8N.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes LocalGateEq S8M.PortPoly
variable {s : Shape} {d : ℕ}
private theorem splitTile (n m : ℕ) (g : GC) : tile (n+m) g = catG (tile n g) (tile m g) := by
  apply Prod.ext (Nat.add_mul ..); funext i w; simp only [tile,tab,catG]; split_ifs with h
  · rfl
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h); simp [Nat.add_mod]
private theorem assocG (a b c : GC) : catG (catG a b) c = catG a (catG b c) := by
  apply Prod.ext (Nat.add_assoc ..); funext i w; simp only [catG]; by_cases ha : i < a.1
  · simp [ha,show i<a.1+b.1 by omega]
  · by_cases hb : i < a.1+b.1
    · simp [ha,hb,show i-a.1<b.1 by omega]
    · simp [ha,hb,show ¬i-a.1<b.1 by omega,Nat.sub_sub]
private theorem pinReads (k : ℕ) : Reads (rd d (k+1)) (HashRows.pub (s:=s) k) := fun _ _ => rfl
private theorem readIn {w : HashRows.Word s} (hw : Reads (regR d) w) (i : Fin d) (b : Bool) : (w i).read b = b := by rw [←hw]; simp [regR,i.isLt]
theorem addStepFits (hd : 1 ≤ d) (p c : ℕ) (f g : Ref s) (x y X Y : HashRows.Word s) (q : Path (ECAddRoutes.addShape d (edges hd)) s) (hf : ∀ z, f.read z = z) (hg : ∀ z, g.read z = z) (hx : Reads (regR d) x) (hy : Reads (regR d) y) (hX : Reads (regR d) X) (hY : Reads (regR d) Y) : FitsG (addStepG (List.replicate d ()) d p c) (ECAddRoutes.addBlock hd p (p-1) (3%p) c f x y g X Y q).core := by
  unfold addStepG ECAddRoutes.addBlock; dsimp only
  rw [show 34=4+30 by decide,splitTile,assocG]; refine catB (tile_many (n:=3) (t:=1) _ fun _ => tile_one (range_spec ..)) (catB (tile_many (n:=14) (t:=2) _ fun _ => tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..))) (catB (many_spec fun i => ?_) ?_))
  · apply hashFits hd <;> fin_cases i <;> first | apply pinReads | exact hx | exact hy | exact hX | exact hY | apply wordReads
  · rw [splitTile 1 1,assocG]; refine catB (tile_one ?_) (catB (tile_one ?_) (catB ?_ (catB ?_ (tiles_join (n:=1) (m:=1) (tile_one ?_) (tile_one ?_)))))
    all_goals first
      | apply rowsReadFits (f:=fun i (h : Fin 4 → Bool) => if h 0 then !h 1 && !h 2 else h 3 == (1:ℕ).testBit i)
      | apply rowsReadFits (f:=fun _ (h : Fin 7 → Bool) => h 6 == ECAddRoutes.mux (h 0) (h 1) (h 2) (h 3) (h 4) (h 5))
      | apply rowsReadFits (f:=fun _ (h : Fin 5 → Bool) => h 4 == (if h 0 then h 1 else !h 1 && h 2 && h 3))
      | apply rowsReadFits (f:=fun _ (h : Fin 8 → Bool) => h 7 == ECAddRoutes.dest (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6))
    all_goals intro i j z; fin_cases j <;> first | exact hf z | exact hg z | apply readIn hx | apply readIn hy | apply readIn hX | apply readIn hY | rfl | (change (GateRoutes.word _ i.val).read z = z; simp [GateRoutes.word,HashRows.padded,i.isLt,Ref.read])
end DetDLP.S8N.PortEval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8N.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes RegisterMap NamedBlocks HashRows GateRoutes LocalGateEq S8M S8M.PortPoly RoutesV2
variable {s : Shape} {n d e : ℕ}
private abbrev slice (q : Path (ECFoldRoutes.foldShape n d e) s) (i : Fin n) :
    Path (DetDLP.S8N.ECAddRoutes.addShape d e) s := fun a => q (.vec i a)

private abbrev outFlag (q : Path (ECFoldRoutes.foldShape n d e) s) (i : Fin n) : Ref s :=
  .reg ((slice q i) (.fst (.fst .bit)))

private abbrev outX (q : Path (ECFoldRoutes.foldShape n d e) s) (i : Fin n) : Word s :=
  word (fun j : Addr (.word d) => (slice q i) (.fst (.snd (.vec 0 (.fst j)))))

private abbrev outY (q : Path (ECFoldRoutes.foldShape n d e) s) (i : Fin n) : Word s :=
  word (fun j : Addr (.word d) => (slice q i) (.fst (.snd (.vec 1 (.fst j)))))

private def foldStep (hd : 1 ≤ d) (p neg1 three c4Term : ℕ)
    (flag0 : Ref s) (x0 y0 : Word s) (flags : Fin n → Ref s)
    (xs ys : Fin n → Word s) (q : Path (ECFoldRoutes.foldShape n d e) s) (i : Fin n) :=
  let f := slice q i
  let prevFlag := if h : i.val = 0 then flag0 else outFlag q ⟨i.val - 1, by omega⟩
  let prevX := if h : i.val = 0 then x0 else outX q ⟨i.val - 1, by omega⟩
  let prevY := if h : i.val = 0 then y0 else outY q ⟨i.val - 1, by omega⟩
  DetDLP.S8N.ECAddRoutes.addBlock hd p neg1 three c4Term prevFlag prevX prevY (flags i) (xs i) (ys i) f

private def outputFlag (flag0 : Ref s) (q : Path (ECFoldRoutes.foldShape n d e) s) : Ref s :=
  if h : n = 0 then flag0 else outFlag q ⟨n - 1, by omega⟩

private def outputX (x0 : Word s) (q : Path (ECFoldRoutes.foldShape n d e) s) : Word s :=
  if h : n = 0 then x0 else outX q ⟨n - 1, by omega⟩

private def outputY (y0 : Word s) (q : Path (ECFoldRoutes.foldShape n d e) s) : Word s :=
  if h : n = 0 then y0 else outY q ⟨n - 1, by omega⟩


private theorem atBit {w : Word s} (h : Reads (regR d) w) (i : Fin d) (b : Bool) : (w i).read b = b := by rw [←h]; simp [regR,i.isLt]
private theorem eqWordFits (a b : Word s) (ha : Reads (regR d) a) (hb : Reads (regR d) b) : FitsG (d,fun _ w => decide (bit w 0 = bit w 1)) (rows d 2 (fun i => ![a i,b i]) (fun _ v => decide (v 0=v 1))).core := by
  apply rowsReadFits (f:=fun _ v => decide (v 0 = v 1)); intro i j z; fin_cases j <;> first | exact atBit ha i z | exact atBit hb i z

theorem targetFits (p : ℕ) (q : Path (targetShape d) s) : FitsG (PortPoly.targetG d p) (targetBlock p q).core := by
  refine catB (range_spec ..) (catB (range_spec ..) ?_)
  apply rowsReadFits (f:=fun _ v => decide (!v 0 || (v 1 = false ∧ v 2 = false)))
  intro i j z; fin_cases j <;> simp [targetFlag,targetX,targetY,word,HashRows.padded,i.isLt,Ref.read]

theorem foldChainFits (hd : 1 ≤ d) (p c : ℕ) (f t : Ref s) (x y X Y : Word s) (flags : Fin n → Ref s) (xs ys : Fin n → Word s)
    (q : Path (ECFoldRoutes.foldShape n d (edges hd)) s) (hf : ∀ z, f.read z=z) (ht : ∀ z,t.read z=z)
    (hx : Reads (regR d) x) (hy : Reads (regR d) y) (hX : Reads (regR d) X) (hY : Reads (regR d) Y)
    (hfl : ∀ i z, (flags i).read z=z) (hxs : ∀ i, Reads (regR d) (xs i)) (hys : ∀ i, Reads (regR d) (ys i)) :
    FitsG (PortPoly.foldChainG n d (addStepG (List.replicate d ()) d p c))
      (ECFoldRoutes.foldBlock hd p (p-1) (3%p) c f x y flags xs ys t X Y q).core := by
  unfold ECFoldRoutes.foldBlock PortPoly.foldChainG; dsimp only
  refine catB ?_ (catB (eqWordFits (outputX x q) X ?_ hX) (catB (eqWordFits (outputY y q) Y ?_ hY) (tileFits _ (foldStep hd p (p-1) (3%p) c f x y flags xs ys q) fun i => ?_)))
  · apply rowsReadFits (f:=fun _ v => decide (v 0=v 1)); intro i j z; fin_cases j
    · change (outputFlag f q).read z=z; unfold outputFlag; split <;> first | exact hf z | rfl
    · exact ht z
  · unfold outputX; split <;> first | exact hx | apply wordReads
  · unfold outputY; split <;> first | exact hy | apply wordReads
  · unfold foldStep; dsimp only; split <;> apply addStepFits <;> first | exact hf | exact hx | exact hy | apply hfl | apply hxs | apply hys | apply wordReads | intro z; rfl

theorem anchor_eq (m d e : ℕ) (j : Fin 4) : PortPoly.anchorCount (copies j) (outputs j) m d e = (RoutesV2.bank j m d e).size + 1 := by
  simp only [PortPoly.anchorCount,RoutesV2.bank,productShape,targetShape,ECSeedBank.ecSeedShape,S8G.SeedAndAtomBank.seedSlot,ECFoldRoutes.foldShape,ECAtomSlot.slotShape,S8H4.Routes.bank,GateRoutes.S,RegisterMap.bank,ECMapRows.mapShape,ECAddRoutes.addShape,ECMapRows.slot,RegisterMap.run,RegisterMap.triple,RegisterMap.mul,GateRoutes.auxShape,Shape.size]; ring

theorem treeFits (p m : ℕ) (hm : 1 ≤ m) (j : Fin 4) (T b2 c4 : ℕ) (c : Coeff) (η : List Bool) :
    let b := bitLen p; let d := b+1; let hd : 1 ≤ d := Nat.succ_pos _; let s := RoutesV2.bank j m d (edges hd)
    let N := joinB (PointGraph.zeroLast s.size) (RoutesV2.network hd hm p T c b2 (p-1) (3%p) c4 j η id)
    FitsG (PortPoly.tree (List.replicate d ()) b m p T (copies j) (outputs j) (edges hd) b2 c4 c η)
      (AnchoredLayout.block N.core (s.size+1)) := by
  dsimp only; unfold PortPoly.tree
  apply catG_spec (A:=⟨AnchoredLayout.anchors _,fun _ _ => true⟩) (B:=(joinB (PointGraph.zeroLast _) _).core)
  · exact ⟨anchor_eq _ _ _ j,fun _ _ => rfl⟩
  refine catB ⟨rfl,fun g w => (zeroLast_local _ g w).symm⟩ ?_
  unfold RoutesV2.network; dsimp only
  refine catB (ecSeedFits ..) (catB (tileFits _ _ fun k => tileFits _ _ fun i => ?_) (tileFits _ _ fun t => catB (targetFits ..) (catB (tileFits _ _ fun k => ?_) (tileFits _ _ fun k => ?_))))
  · apply atomSlotFits <;> simp only [RoutesV2.seedA, RoutesV2.seedB, ECSeedBank.ecSeedA, ECSeedBank.ecSeedB, S8G.SeedAndAtomBank.seedA,S8G.SeedAndAtomBank.seedB] <;> apply wordReads
  · apply mapFits <;> first | apply wordReads | intro z; rfl
  · apply foldChainFits <;> first | apply wordReads | (intro i; simp only [foldX,foldY,mapX,mapY]; apply wordReads) | intros; rfl
end DetDLP.S8N.PortEval
end


section

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentPort

open Groundwork DetDLP_W1_Queries S8H0 S8H.PortCombinators S8J.CircuitRealizes
open RegisterMap NamedBlocks

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev queryWordEC (j : Fin 4) (T : ℕ) (η : List Bool) :=
  M89S1.queryWord 2 (encodeCurveInput p E) [countWord j.val, countWord T, η]

private theorem fields (j : Fin 4) (T : ℕ) (η : List Bool) :
    let w := queryWordEC E j T η
    S8M.PortPoly.prime w = p ∧ PortPoly.idx w = j.val ∧
      PortPoly.threshold w = T ∧ PortPoly.prefixBits w = η ∧
      S8M.PortPoly.coeff w = GateSemantics.coeff E := by
  constructor
  · simp [queryWordEC, M89S1.queryWord, S8M.PortPoly.prime, second,
      encodeCurveInput, encodeNatListBin]
  · simp [queryWordEC, M89S1.queryWord, PortPoly.idx, PortPoly.threshold,
      PortPoly.prefixBits, S8M.PortPoly.coeff, GateSemantics.coeff,
      third, second, encodeCurveInput, w5_M6Sort.decode_encode]

private theorem subVal (a b : ZMod p) :
    (a.val + p - b.val) % p = (a - b).val := by
  rw [← ZMod.val_natCast]
  congr 1
  rw [Nat.cast_sub (by have := b.val_lt; omega), Nat.cast_add]
  simp

private theorem negVal (a : ZMod p) : (p - a.val) % p = (-a).val := by
  simpa using subVal (0 : ZMod p) a

private theorem curveConstants (j : Fin 4) (T : ℕ) (η : List Bool) :
    let w := queryWordEC E j T η
    S8M.PortPoly.bTwo w = E.b₂.val ∧ S8M.PortPoly.cTerm w = (-27 * E.c₄).val := by
  dsimp only
  obtain ⟨hp, _, _, _, hc⟩ := fields E j T η
  have hb : S8M.PortPoly.bTwo (queryWordEC E j T η) = E.b₂.val := by
    rw [S8M.PortPoly.bTwo, hc, hp, ← ZMod.val_natCast]
    congr 1
    simp [GateSemantics.coeff, WeierstrassCurve.b₂, pow_two]
  have hs : E.b₂.val * E.b₂.val % p = (E.b₂ ^ 2).val := by
    rw [← ZMod.val_natCast]
    simp [pow_two]
  have h4 : 24 * (2 * E.a₄.val + E.a₁.val * E.a₃.val) % p = (24 * E.b₄).val := by
    rw [← ZMod.val_natCast]
    simp [WeierstrassCurve.b₄]
  have h27 : 27 * E.c₄.val % p = (27 * E.c₄).val := by
    rw [← ZMod.val_natCast]
    simp
  have hc4 : ((E.b₂ ^ 2).val + p - (24 * E.b₄).val) % p = E.c₄.val := by
    rw [subVal]
    rfl
  refine ⟨hb, ?_⟩
  simp only [S8M.PortPoly.cTerm, hc, hb, hp, GateSemantics.coeff, hs, h4, hc4, h27]
  rw [negVal, neg_mul]

abbrev shape (p m : ℕ) (j : Fin 4) :=
  RoutesV2.bank j m (GateSemantics.d p) (GateSemantics.e p)

noncomputable abbrev net {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  joinB (PointGraph.zeroLast (shape p m j).size)
    (RoutesV2.network (GateSemantics.hd p) hm p T (GateSemantics.coeff E) E.b₂.val
      (-1 : ZMod p).val (3 : ZMod p).val (-27 * E.c₄).val j η id)

noncomputable abbrev core {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  AnchoredLayout.block (net E hm j T η).core ((shape p m j).size + 1)

noncomputable abbrev wires {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  AnchoredLayout.wiring (net E hm j T η).core (net E hm j T η).name

theorem decodedFits (hp : 3 < p) (hm : 1 ≤ blockCount (bitLen p))
    (j : Fin 4) (T : ℕ) (η : List Bool) :
    FitsG (PortPoly.decoded (queryWordEC E j T η)) (core E hm j T η) := by
  obtain ⟨hprime, hidx, hth, hpfx, hcoeff⟩ := fields E j T η
  obtain ⟨hb, hc4⟩ := curveConstants E j T η
  have hn : (-1 : ZMod p).val = p - 1 := by
    rw [ZMod.val_neg_of_ne_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
  simp only [PortPoly.decoded, hprime, hidx, hth, hpfx, hcoeff, hb, hc4,
    S8M.PortPoly.width, S8M.PortPoly.slots,
    S8G.FpMoment.Code.width_eq, S8G.FpMoment.Code.slots_eq, pad_eq,
    S8H.PointAddresses.wires_eq (GateSemantics.hd p)]
  simpa only [core, net, hn, ZMod.val_ofNat, RoutesV2.copies, RoutesV2.outputs] using
    DetDLP.S8N.PortEval.treeFits p (blockCount (bitLen p)) hm j T E.b₂.val (-27 * E.c₄).val
      (GateSemantics.coeff E) η

/-- The check field of a uniform address record, before port-query unpacking. -/
def check (z : List Bool × ℕ × List Bool) : Bool :=
  if z.2.1 < (PortPoly.decoded z.1).1 then (PortPoly.decoded z.1).2 z.2.1 z.2.2
  else S8H0.PortEval.agree z.2.2

theorem check_poly : PolyT check := by
  have hf : PolyT (@Prod.fst (List Bool) (ℕ × List Bool)) := PolyT.fst PolyT.id'
  have hc := PolyT.comp
    (show PolyT (fun w : List Bool => (PortPoly.decoded w).1) from PortPoly.decoded_poly.1) hf
  exact P2M_Groundwork_PolyT_ite__226169acf219
    (PolyT.decide_lt (PolyT.fst (PolyT.snd PolyT.id')) hc)
    PortPoly.decoded_poly.2
    (PolyT.comp S8H0.PortEval.agree_poly (PolyT.snd (PolyT.snd PolyT.id')))

open w4_M5Network in
theorem port_eval (hp : 3 < p) (hm : 1 ≤ blockCount (bitLen p))
    (j : Fin 4) (T : ℕ) (η : List Bool)
    (v : Fin (G (core E hm j T η) (wires E hm j T η)).subdivision.nV) (a) :
    S8C.portPacket check (encodePortQuery (queryWordEC E j T η) v.val (List.ofFn a)) =
      encodeNatListBin [if (G (core E hm j T η) (wires E hm j T η)).subdivisionTensor
        (S8J.CircuitRealizes.T (core E hm j T η) (wires E hm j T η)) v a then 1 else 0] :=
  fullPort_eval _ _ (decodedFits E hp hm j T η) v a

end DetDLP.S8N.MomentPort
end

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentGateBounds

open S8H0 RegisterMap NamedBlocks GateRoutes RangeRows HashRows GraphDegree
open S8G.SeedAndAtomBank S8M
open private joinFull manyFull rowsFull addFull mulFull from Definitions.Def_DetDLP_S8G_AnchoredBank
open private fixed from Definitions.Def_DetDLP_S8M_ECAtomSlot

/-- Every gate receives a wire, and its input count respects the M5 degree cap. -/
def checked {k : ℕ} (b : B k) (p : ℕ) := Function.Surjective b.core.A.gate ∧ good b (cap p)

private theorem join {k p : ℕ} {a b : B k} (ha : checked a p) (hb : checked b p) :
    checked (joinB a b) p := ⟨joinFull ha.1 hb.1, join_ok _ _ ha.2 hb.2⟩

private theorem indexed {n k p : ℕ} {f : Fin (n+1) → B k} (h : ∀ i, checked (f i) p) :
    checked (many n f) p := ⟨manyFull (fun i => (h i).1), many_ok n f (fun i => (h i).2)⟩

private theorem batch {s : Shape} {n p : ℕ} {f : Fin n → B (s.size+1)}
    (h : ∀ i, checked (f i) p) : checked (allRows n f) p := by
  cases n with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n => exact indexed h

private theorem row {s : Shape} {n k p : ℕ} (hi : 0 < k) (hk : k ≤ 12)
    (r : Fin n → Fin k → Ref s) (t : Fin n → (Fin k → Bool) → Bool) :
    checked (rows n k r t) p := ⟨rowsFull ⟨0,hi⟩, mono (row_ok n k r t) (small p k hk)⟩

private theorem carry {s : Shape} {n p : ℕ} (c : Bool) (a b z k : Fin n → Ref s) :
    checked (NamedBlocks.add c a b z k) p := ⟨addFull, mono (add_ok c a b z k) (small p 5 (by decide))⟩

private theorem mul {s : Shape} (p : ℕ)
    (r : Fin (w3_fpMulLayout (GateSemantics.d p) (GateSemantics.hd p)).nb → Ref s) :
    checked (mapped _ (w3_fpMulTests _ (GateSemantics.hd p)) r) p :=
  ⟨mulFull (GateSemantics.hd p), mul_ok p r⟩

private theorem hash {s : Shape} (p : ℕ) (w : Wires (GateSemantics.d p) (GateSemantics.hd p) s) :
    checked (HashRows.block p w) p := by
  unfold HashRows.block HashRows.product
  refine join (join (join (mul p _) ?_) (join (mul p _) ?_))
    (join (carry ..) (join (carry ..) (carry ..)))
  all_goals exact row (by decide) (by decide) _ _

private theorem atom {s : Shape} (p T : ℕ) (c : Coeff) (a b x y : Word s)
    (q : Path (ECAtomSlot.slotShape (GateSemantics.d p) (GateSemantics.e p)) s) :
    checked (ECAtomSlot.slotBlock (GateSemantics.hd p) p T c a b x y q) p := by
  have hr : checked (RangeRows.block (GateSemantics.d p) (GateSemantics.e p) p) p := by
    unfold RangeRows.block
    exact join (join (carry ..) (carry ..)) (indexed fun _ => join (carry ..) (carry ..))
  unfold ECAtomSlot.slotBlock
  refine join ?_ (row (by decide) (by decide) _ _)
  change checked (fixed _ _ _ _) p
  unfold fixed
  refine join ?_ (join (hash p _) (join (row (by decide) (by decide) _ _) (carry ..)))
  change checked (joinB _ _) p
  exact join hr (join (indexed fun _ => hash p _) (row (k:=5) (by decide) (by decide) _ _))

private theorem map {s : Shape} {e : ℕ} (p b a c : ℕ) (f : Ref s) (x y : Word s)
    (q : Path (ECMapRows.mapShape (GateSemantics.d p) e) s) :
    checked (ECMapRows.mapBlock (GateSemantics.hd p) p b a c f x y q) p := by
  unfold ECMapRows.mapBlock
  exact join (join (join (carry ..) (carry ..)) (indexed fun _ => join (carry ..) (carry ..)))
    (join (indexed fun _ => hash p _) (join (row (by decide) (by decide) _ _)
      (join (row (by decide) (by decide) _ _) (row (by decide) (by decide) _ _))))

private theorem step {s : Shape} {e : ℕ} (p n t c : ℕ) (f : Ref s) (x y : Word s)
    (g : Ref s) (X Y : Word s) (q : Path (ECAddRoutes.addShape (GateSemantics.d p) e) s) :
    checked (ECAddRoutes.addBlock (GateSemantics.hd p) p n t c f x y g X Y q) p := by
  unfold ECAddRoutes.addBlock
  refine join (indexed fun _ => carry ..) (join (indexed fun _ => join (carry ..) (carry ..))
    (join (indexed fun _ => hash p _) ?_))
  exact join (row (by decide) (by decide) _ _) (join (row (by decide) (by decide) _ _)
    (join (row (by decide) (by decide) _ _) (join (row (by decide) (by decide) _ _)
      (join (row (by decide) (by decide) _ _) (row (by decide) (by decide) _ _)))))

private theorem fold {s : Shape} {n e : ℕ} (p a b c : ℕ) (f : Ref s) (x y : Word s)
    (flags : Fin n → Ref s) (xs ys : Fin n → Word s) (g : Ref s) (X Y : Word s)
    (q : Path (ECFoldRoutes.foldShape n (GateSemantics.d p) e) s) :
    checked (ECFoldRoutes.foldBlock (GateSemantics.hd p) p a b c f x y flags xs ys g X Y q) p := by
  unfold ECFoldRoutes.foldBlock
  exact join (row (by decide) (by decide) _ _) (join (row (by decide) (by decide) _ _)
    (join (row (by decide) (by decide) _ _) (batch fun _ => step ..)))

theorem network {s : Shape} {m : ℕ} (hm : 1 ≤ m) (p T : ℕ) (c : Coeff)
    (b n t c4 : ℕ) (j : Fin 4) (η : List Bool)
    (q : Path (RoutesV2.bank j m (GateSemantics.d p) (GateSemantics.e p)) s) :
    checked (RoutesV2.network (GateSemantics.hd p) hm p T c b n t c4 j η q) p := by
  have seedSlot (z : Path (seedSlot (GateSemantics.d p)) s) : checked (ECSeedBank.ecSeedSlotBlock p z) p :=
    join (carry ..) (join (carry ..) (carry ..))
  unfold RoutesV2.network
  refine join (join (batch fun _ => join (seedSlot _) (seedSlot _)) (row (by decide) (by decide) _ _))
    (join (batch fun _ => batch fun _ => atom ..) (batch fun _ => ?_))
  exact join (join (carry ..) (join (carry ..) (row (by decide) (by decide) _ _)))
    (join (batch fun _ => map ..) (batch fun _ => fold ..))

end DetDLP.S8N.MomentGateBounds
end

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentUnary

open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes
open private joinFull from Definitions.Def_DetDLP_S8G_AnchoredBank

private theorem tree_le {m : ℕ} (hm : 1 ≤ m) (p T b2 c4 : ℕ) (c : Coeff)
    (j : Fin 4) (η : List Bool) :
    let b := bitLen p
    let d := GateSemantics.d p
    let e := GateSemantics.e p
    (PortPoly.tree (List.replicate d ()) b m p T (RoutesV2.copies j) (RoutesV2.outputs j) e b2 c4 c η).1 ≤
      MomentDimensions.anchored (RoutesV2.copies j) (RoutesV2.outputs j) m d e η.length := by
  dsimp only
  let s := RoutesV2.bank j m (GateSemantics.d p) (GateSemantics.e p)
  let R := RoutesV2.network (GateSemantics.hd p) hm p T c b2 (p-1) (3%p) c4 j η id
  let N := joinB (PointGraph.zeroLast s.size) R
  let A := (AnchoredLayout.block N.core (s.size+1)).A
  have hr : Function.Surjective R.core.A.gate :=
    (MomentGateBounds.network hm p T c b2 (p-1) (3%p) c4 j η id).1
  have hN : Function.Surjective N.core.A.gate := joinFull Function.surjective_id hr
  have hA : Function.Surjective A.gate := joinFull Function.surjective_id hN
  refine (DetDLP.S8N.PortEval.treeFits p m hm j T b2 c4 c η).1.trans_le ((w3_incDims A hA).1.trans_eq ?_)
  change (s.size+1) + (1 + MomentIncidences.count R) = _
  unfold R
  rw [MomentDimensions.network_count]
  exact congrArg (· + _) (MomentGeometry.anchor_eq m (GateSemantics.d p) (GateSemantics.e p) j).symm

private def index (i : ℕ) : Fin 4 :=
  ⟨if i = 3 then 3 else min i 2, by split_ifs <;> omega⟩

private theorem copies_index (i : ℕ) : RoutesV2.copies (index i) = min i 2 := by
  simp only [RoutesV2.copies, index]
  split_ifs <;> omega

private theorem outputs_index (i : ℕ) : RoutesV2.outputs (index i) = if i = 3 then 1 else 0 := by
  simp only [RoutesV2.outputs, index]
  split_ifs <;> omega

attribute [local irreducible] PortPoly.tree MomentDimensions.anchored

/-- Even malformed words describe local gates with positive arity. -/
theorem gates_le_incidences (w : List Bool) : (PortPoly.decoded w).1 ≤ MomentDimensions.incidences w := by
  let p := S8M.PortPoly.prime w
  let m := blockCount (bitLen p)
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have h := tree_le hm p (PortPoly.threshold w) (S8M.PortPoly.bTwo w) (S8M.PortPoly.cTerm w)
    (S8M.PortPoly.coeff w) (index (PortPoly.idx w)) (PortPoly.prefixBits w)
  rw [copies_index, outputs_index] at h
  change (PortPoly.tree (CoreCheck.pad p) (S8G.FpMoment.Code.width p) _ p _ _ _ _ _ _ _ _).1 ≤
    MomentDimensions.anchored _ _ _ _ _ _
  simp only [S8M.PortPoly.width, S8M.PortPoly.slots, S8G.FpMoment.Code.width_eq,
    S8G.FpMoment.Code.slots_eq, S8H.PortCombinators.pad_eq]
  change (PortPoly.tree _ (bitLen p) m p _ _ _ (S8H.PointAddresses.wires (bitLen p+1)) _ _ _ _).1 ≤
    MomentDimensions.anchored _ _ m (bitLen p+1) (S8H.PointAddresses.wires (bitLen p+1)) _
  rw [S8H.PointAddresses.wires_eq (Nat.succ_pos (bitLen p))]
  exact h

end DetDLP.S8N.MomentUnary

namespace DetDLP.S8N.MomentUnary

open Groundwork
open private unary_mul from Definitions.Def_DetDLP_W4_M5EvalFrontend

variable {α : Type} [Enc α]

private theorem uConst (n : ℕ) : Unary (fun _ : α => n) := PolyT.const _

private theorem uAdd {f g : α → ℕ} (hf : Unary f) (hg : Unary g) :
    Unary (fun x => f x + g x) := by
  apply (PolyT.append hf hg).congr
  intro x
  exact (List.replicate_add ..).symm

private theorem bounded {f g : α → ℕ} (hg : Unary g) (hf : PolyT f) (h : ∀ x, f x ≤ g x) :
    Unary f := by
  apply (PolyT.unary_min_length hf hg).congr
  intro x
  simp only [List.length_replicate, min_eq_left (h x)]

private theorem uAffine {d e : α → ℕ} (a b c : ℕ) (hd : Unary d) (he : Unary e) :
    Unary (fun x => a*d x + b*e x + c) :=
  uAdd (uAdd (unary_mul (uConst a) hd) (unary_mul (uConst b) he)) (uConst c)

private theorem anchoredU {c o m d e k : α → ℕ} (hc : Unary c) (ho : Unary o)
    (hm : Unary m) (hd : Unary d) (he : Unary e) (hk : Unary k) (hs : Unary (fun x => m x - 1)) :
    Unary (fun x => MomentDimensions.anchored (c x) (o x) (m x) (d x) (e x) (k x)) := by
  have d1 := uAdd hd (uConst 1)
  have twice := unary_mul (uConst 2) hm
  have reg : Unary (fun x => PortPoly.anchorCount (c x) (o x) (m x) (d x) (e x)) := by
    have seed := unary_mul hm (uAdd (unary_mul (uConst 16) hd) (uConst 6))
    have atoms := unary_mul hc (unary_mul hm (uAffine 122 14 46 hd he))
    have maps := unary_mul twice (uAffine 70 8 27 hd he)
    have folds := unary_mul (uConst 2) (unary_mul hs (uAffine 253 30 97 hd he))
    have target := uAdd (unary_mul (uConst 6) hd) (uConst 3)
    exact uAdd (uAdd seed (uAdd atoms (unary_mul ho (uAdd target (uAdd maps folds))))) (uConst 1)
  have hash : Unary (fun x => MomentIncidences.hash (d x) (e x)) := uAffine 4 36 10 he hd
  have atom : Unary (fun x => MomentIncidences.atom (d x) (e x)) :=
    uAdd (uAdd (uAdd (unary_mul (uConst 85) d1) (unary_mul (uConst 7) hash))
      (unary_mul (uConst 12) hd)) (uConst 1)
  have map : Unary (fun x => MomentIncidences.map (d x) (e x)) :=
    uAdd (uAdd (uAdd (unary_mul (uConst 50) d1) (unary_mul (uConst 4) hash))
      (uConst 2)) (unary_mul (uConst 6) hd)
  have step : Unary (fun x => MomentIncidences.step (d x) (e x)) :=
    uAdd (uAdd (uAdd (unary_mul (uConst 170) d1) (unary_mul (uConst 15) hash))
      (unary_mul (uConst 31) hd)) (uConst 5)
  have fold := uAdd (uAdd (uConst 2) (unary_mul (uConst 4) hd)) (unary_mul hs step)
  have target := uAdd (unary_mul (uConst 10) d1) (unary_mul (uConst 3) hd)
  have rows := uAdd (unary_mul hm (unary_mul (uConst 30) d1)) hk
  have product := uAdd target (uAdd (unary_mul twice map) (unary_mul (uConst 2) fold))
  exact uAdd reg (uAdd (uConst 1)
    (uAdd rows (uAdd (unary_mul hc (unary_mul hm atom)) (unary_mul ho product))))

theorem incidences_unary : Unary MomentDimensions.incidences := by
  let p := S8M.PortPoly.prime
  let b := fun w => S8G.FpMoment.Code.width (p w)
  let d := fun w => b w + 1
  let m := fun w => S8G.FpMoment.Code.slots (b w)
  let e := fun w => S8H.PointAddresses.wires (d w)
  have hp : PolyT p := DetDLP.S8N.PortPoly.prime_poly
  have hb : PolyT b := S8G.FpMoment.Code.width_poly hp
  have hu : Unary b := Unary.of_length (PolyT.bits (PolyT.sub hp (PolyT.const 1)))
  have hd : Unary d := uAdd hu (uConst 1)
  have hd' : PolyT d := PolyT.add hb (PolyT.const 1)
  have hm : Unary m := bounded (uAdd hu (uConst 2)) (S8G.FpMoment.Code.slots_poly hb) fun w => by
    change S8G.FpMoment.Code.slots (b w) ≤ b w + 2
    rw [S8G.FpMoment.Code.slots_eq]
    exact S8G.FpMoment.blockUpper _
  have hs : Unary (fun w => m w - 1) :=
    bounded hm (PolyT.sub (S8G.FpMoment.Code.slots_poly hb) (PolyT.const 1)) (fun w => Nat.sub_le _ _)
  have he : Unary e := bounded (unary_mul (uConst 1100) (uAdd hd (uConst 1)))
    (S8H.PointAddresses.mul_poly.nb hd') fun w => by
      have hpos : 1 ≤ d w := Nat.succ_pos _
      change S8H.PointAddresses.wires (d w) ≤ 1100*(d w+1)
      rw [S8H.PointAddresses.wires_eq hpos]
      exact (w4_M5GraphBounds.graph_edge_bound hpos).le
  have hc : Unary (fun w => min (PortPoly.idx w) 2) := by
    apply bounded (uConst 2) _ (fun w => min_le_right _ _)
    simp only [min_def]
    exact PolyT.ite' (PolyT.decide_le PortPoly.idx_poly (PolyT.const 2)) PortPoly.idx_poly (PolyT.const 2)
  have ho : Unary (fun w => if PortPoly.idx w = 3 then 1 else 0) :=
    bounded (uConst 1) (PolyT.ite' (PolyT.decide_eq PortPoly.idx_poly (PolyT.const 3))
      (PolyT.const 1) (PolyT.const 0)) (fun w => by split_ifs <;> decide)
  exact anchoredU hc ho hm hd he (Unary.of_length PortPoly.prefix_poly) hs

theorem gates_unary : Unary (fun w : List Bool => (PortPoly.decoded w).1) :=
  bounded incidences_unary PortPoly.decoded_poly.1 gates_le_incidences

theorem nv_unary : Unary MomentDimensions.nv :=
  uAdd (uAdd gates_unary incidences_unary) incidences_unary

theorem ne_unary : Unary MomentDimensions.ne :=
  uAdd incidences_unary (uAdd incidences_unary incidences_unary)

theorem vert : Unary (fun w => MomentDimensions.nv w + MomentDimensions.ne w) :=
  uAdd nv_unary ne_unary

theorem edge : Unary (fun w => MomentDimensions.ne w + MomentDimensions.ne w) :=
  uAdd ne_unary ne_unary

end DetDLP.S8N.MomentUnary
end

end

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentPacket

open Groundwork M89S1 DetDLP_W1_Queries S8C S8H w4_M5Network
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev constant := 1600000

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

theorem prime_word (j : Fin 4) (T : ℕ) (η : List Bool) :
    S8M.PortPoly.prime (DetDLP.S8N.MomentTag.word E j T η) = p := by
  simp [S8M.PortPoly.prime, DetDLP.S8N.MomentTag.word, queryWord, second,
    encodeCurveInput, encodeNatListBin]

theorem sizeField_word (j : Fin 4) (T : ℕ) (η : List Bool) :
    S8N.MomentHeader.sizeField (DetDLP.S8N.MomentTag.word E j T η) =
      S8N.MomentHeader.scale (blockCount (bitLen p)) (bitLen p) := by
  simp only [S8N.MomentHeader.sizeField, prime_word, S8G.FpMoment.Code.width_eq,
    S8G.FpMoment.Code.slots_eq]

theorem make_word (j : Fin 4) (T : ℕ) (η : List Bool)
    (a : S8G.FpMoment.Code.Addresses) (G : WireGraph)
    (nv : a.nv (DetDLP.S8N.MomentTag.word E j T η) = G.nV)
    (ne : a.ne (DetDLP.S8N.MomentTag.word E j T η) = G.nE)
    (src : ∀ i : Fin G.nE, a.src (DetDLP.S8N.MomentTag.word E j T η) i.val = (G.endpoints i).1.val)
    (dst : ∀ i : Fin G.nE, a.dst (DetDLP.S8N.MomentTag.word E j T η) i.val = (G.endpoints i).2.val) :
    let w := DetDLP.S8N.MomentTag.word E j T η
    let s := S8N.MomentHeader.scale (blockCount (bitLen p)) (bitLen p)
    S8N.MomentHeader.make a w = encodeBTNInstance w G.subdivision s s 1 := by
  dsimp only
  rw [S8N.MomentHeader.make, nv, ne, WirePacket.packet_eq G _ _ src dst, sizeField_word,
    outerPacket_eq]

theorem wordLen {m T : ℕ} (j : Fin 4) (η : List Bool) (hm : 1 ≤ m)
    (hT : T ≤ p) (hη : η.length ≤ m*4*bitLen p) :
    (DetDLP.S8N.MomentTag.word E j T η).length ≤ 256*m*bitLen p := by
  have hb : 1 ≤ bitLen p := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have hc : (encodeCurveInput p E).length ≤ 6*(2*bitLen p+4)+1 := by
    have hp := S8G.FpMoment.binaryLen (le_refl p)
    have h1 := S8G.FpMoment.binaryLen (ZMod.val_lt E.a₁).le
    have h2 := S8G.FpMoment.binaryLen (ZMod.val_lt E.a₂).le
    have h3 := S8G.FpMoment.binaryLen (ZMod.val_lt E.a₃).le
    have h4 := S8G.FpMoment.binaryLen (ZMod.val_lt E.a₄).le
    have h6 := S8G.FpMoment.binaryLen (ZMod.val_lt E.a₆).le
    simp only [encodeCurveInput, encodeNatListBin, Encoding.encodeList, List.length_cons,
      List.length_append, w3_frameLength, List.length_nil]
    omega
  have ht := S8G.FpMoment.binaryLen hT
  have hi := w3_queryIndexLength j.val
  have hj := j.isLt
  have htag : (countWord 2).length = 2 := by decide
  have hmb : bitLen p ≤ m*bitLen p := Nat.le_mul_of_pos_left _ hm
  simp only [DetDLP.S8N.MomentTag.word, queryWord, Encoding.encodeList, id_eq, List.length_cons,
    List.length_append, w3_frameLength, List.length_nil, htag]
  rw [show m*4*bitLen p = 4*(m*bitLen p) by ring] at hη
  rw [show 256*m*bitLen p = 256*(m*bitLen p) by ring]
  omega

theorem wordBudget {T : ℕ} (j : Fin 4) (η : List Bool) (hT : T ≤ p)
    (hη : η.length ≤ blockCount (bitLen p)*4*bitLen p) :
    let b := bitLen p
    let m := blockCount b
    let w := DetDLP.S8N.MomentTag.word E j T η
    S8N.MomentHeader.scale m b + w.length ≤ constant*m*b ∧
      S8N.MomentHeader.scale m b + w.length ≤ constant*(b+1)^constant := by
  dsimp only
  let b := bitLen p
  let m := blockCount b
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have hw := wordLen E j η hm hT hη
  have hs : S8N.MomentHeader.scale m b ≤ 1572864*m*b := by
    calc _ ≤ 524288*m*(3*b) := Nat.mul_le_mul_left _ (by omega)
         _ = _ := by ring
  have hfirst : S8N.MomentHeader.scale m b + (DetDLP.S8N.MomentTag.word E j T η).length ≤
      1600000*m*b := by nlinarith
  refine ⟨hfirst, hfirst.trans ?_⟩
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  calc m*b ≤ (b+2)*b := Nat.mul_le_mul_right b (S8G.FpMoment.blockUpper b)
       _ ≤ (b+1)^2 := by nlinarith
       _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

end DetDLP.S8N.MomentPacket
end



section
set_option autoImplicit false

namespace DetDLP.S8N.MomentMulBudget

open w4_MulParams w4_M5GraphBounds

theorem graph_edges {d : ℕ} (hd : 1 ≤ d) :
    (graph d hd).nE ≤ 260 * (d + 1) := by
  rw [graph_nE hd]
  by_cases hsmall : d < 28
  · interval_cases d <;> decide
  have hJ : J d ≤ 3 * (d + 1) := by
    by_contra! h
    have hsquare : (3 * (d + 1)) ^ 2 ≤ (J d) ^ 2 := by gcongr
    have hfactor : 256 ≤ 9 * (d + 1) := by omega
    have hproduct := Nat.mul_le_mul_right (d + 1) hfactor
    nlinarith only [hsquare, hproduct, J_upper hd]
  have hn : n0 d ≤ d := by
    have hk : 1 ≤ k d := by have := k_ge_four hd; omega
    have hprev := Nat.mul_le_mul_right (n0 d - 1) hk
    have hmin := n0_minimal hd
    omega
  have hnJ : n0 d * J d ≤ 4 * d + J d := by
    calc
      n0 d * J d = 4 * (k d * n0 d) := by rw [← four_mul_k hd]; ring
      _ ≤ 4 * (d + k d) := Nat.mul_le_mul_left _ (n0_covers_tightly hd).2.le
      _ = 4 * d + J d := by rw [Nat.mul_add, four_mul_k hd]
  calc
    4*d + (6*L d + 8*n0 d - 2)*(J d + 1) ≤ 4*d + (32*n0 d)*(J d + 1) := by
      gcongr
      have := L_upper hd
      omega
    _ = 4*d + 32*(n0 d*J d+n0 d) := by ring
    _ ≤ 260*(d+1) := by omega

end DetDLP.S8N.MomentMulBudget
end

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentEdgeBounds

open Groundwork S8H0 MomentDimensions

theorem anchored_budget {c o m d e k : ℕ} (hc : c ≤ 2) (ho : o ≤ 1)
    (hm : 1 ≤ m) (he : e ≤ 260*(d+1)) (hk : k ≤ 4*m*(d+1)) :
    6*anchored c o m d e k < 524288*m*(d+1) := by
  calc
    6*anchored c o m d e k ≤ 6*anchored 2 1 m d (260*(d+1)) (4*m*(d+1)) := by
      unfold anchored routed PortPoly.anchorCount MomentIncidences.atom
        MomentIncidences.map MomentIncidences.fold MomentIncidences.step
        MomentIncidences.hash MomentIncidences.target
      gcongr
    _ < 524288*m*(d+1) := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      unfold anchored routed PortPoly.anchorCount MomentIncidences.atom
        MomentIncidences.map MomentIncidences.fold MomentIncidences.step
        MomentIncidences.hash MomentIncidences.target
      simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
      ring_nf
      omega

theorem graph_budget {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool)
    (hη : η.length ≤ m*4*bitLen p) :
    2*(S8J.CircuitRealizes.G (MomentPort.core E hm j T η)
      (MomentPort.wires E hm j T η)).nE < S8N.MomentHeader.scale m (bitLen p) := by
  change 2*((MomentPort.core E hm j T η).A.ne + ((MomentPort.core E hm j T η).A.ne +
    (MomentPort.core E hm j T η).A.ne)) < _
  rw [MomentDimensions.core_count]
  have hc : RoutesV2.copies j ≤ 2 := min_le_right _ _
  have ho : RoutesV2.outputs j ≤ 1 := by unfold RoutesV2.outputs; split <;> decide
  have he : GateSemantics.e p ≤ 260*(GateSemantics.d p+1) :=
    MomentMulBudget.graph_edges (GateSemantics.hd p)
  have hk : η.length ≤ 4*m*(GateSemantics.d p+1) := by
    change η.length ≤ 4*m*(bitLen p+1+1)
    calc
      η.length ≤ m*4*bitLen p := hη
      _ ≤ 4*m*(bitLen p+1+1) := by rw [Nat.mul_comm m 4]; gcongr; omega
  have h := anchored_budget hc ho hm he hk
  change 2*(_ + (_ + _)) < 524288*m*(GateSemantics.d p+1)
  omega

end DetDLP.S8N.MomentEdgeBounds
end

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentGraphBounds

open Groundwork S8H0 GraphDegree S8H S8J.CircuitRealizes

open private joinFull from Definitions.Def_DetDLP_S8G_AnchoredBank
open private cycle_ok from Definitions.Def_DetDLP_S8H0_GraphDegree

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
variable (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool)

private theorem anchor (q : Block) (k D : ℕ) (hD : 1 ≤ D)
    (hf : Function.Surjective q.A.gate) (h : bounded q.A D) :
    Function.Surjective (AnchoredLayout.block q k).A.gate ∧ bounded (AnchoredLayout.block q k).A D := by
  refine ⟨joinFull (A := AnchoredLayout.anchors k) Function.surjective_id hf, ?_⟩
  intro g
  induction g using Fin.addCases with
  | left i =>
    exact (S8J.degree_left (AnchoredLayout.anchors k).gate q.A.gate i).le.trans (anchors_ok k D hD i)
  | right i => exact (S8J.degree_right (AnchoredLayout.anchors k).gate q.A.gate i).le.trans (h i)

theorem core_gates : Function.Surjective (MomentPort.core E hm j T η).A.gate ∧
    bounded (MomentPort.core E hm j T η).A (cap p) := by
  let n := MomentPort.net E hm j T η
  let k := (MomentPort.shape p m j).size+1
  have hnet : MomentGateBounds.checked n p := by
    have h := MomentGateBounds.network hm p T (GateSemantics.coeff E) E.b₂.val
      (-1 : ZMod p).val (3 : ZMod p).val (-27 * E.c₄).val j η id
    exact ⟨joinFull Function.surjective_id h.1,
      join_ok _ _ (anchors_ok 1 _ (small p 1 (by decide))) h.2⟩
  exact anchor n.core k (cap p) (small p 1 (by decide)) hnet.1 hnet.2

theorem gate_surj : Function.Surjective (circuit (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).gate := by
  have h := (core_gates E hm j T η).1
  intro g
  induction g using Fin.addCases with
  | left i =>
    obtain ⟨e, rfl⟩ := h i
    exact ⟨e.castAdd _, by simp only [circuit, CopyCycle.layout, Fin.addCases_left, Function.comp_apply]⟩
  | right i =>
    exact ⟨Fin.natAdd _ (i.castAdd _), by simp only [circuit, CopyCycle.layout,
      Fin.addCases_right, Fin.addCases_left]⟩

theorem degree (v : Fin (G (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).nV) :
    (G (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).deg v ≤ cap p :=
  cycle_ok (MomentPort.core E hm j T η).A (AnchoredLayout.signal (MomentPort.net E hm j T η).core (MomentPort.net E hm j T η).name)
    (MomentPort.wires E hm j T η).next rfl (core_gates E hm j T η).2 (small p 3 (by decide)) v

theorem degree_budget :
    max (Finset.univ.sup (G (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).deg) 2 ≤
      Nat.ceil ((S8N.MomentHeader.scale m (bitLen p) : ℝ)^((9 : ℝ)/10)) :=
  (max_le (Finset.sup_le fun v _ => degree E hm j T η v) (small p 2 (by decide))).trans
    (S8N.MomentHeader.degreeBudget hm)

theorem vertex_linear (hη : η.length ≤ m*4*bitLen p) :
    (G (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).nV + (G (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).nE ≤
      2*S8N.MomentHeader.scale m (bitLen p) := by
  let A := circuit (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)
  obtain ⟨hg, hb⟩ := w3_incDims A (gate_surj E hm j T η)
  have he : 2*A.ne < S8N.MomentHeader.scale m (bitLen p) := MomentEdgeBounds.graph_budget E hm j T η hη
  change A.ng + A.nb + A.ne ≤ _
  omega

theorem vertex_budget {L : ℕ} (hL : 2 ≤ L) (hη : η.length ≤ m*4*bitLen p) :
    (G (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).nV + (G (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).nE ≤
      (S8N.MomentHeader.scale m (bitLen p))^L := by
  let s := S8N.MomentHeader.scale m (bitLen p)
  have hs : 2 ≤ s := by
    have h : bitLen p+2 ≤ s := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hm)
    omega
  calc
    _ ≤ 2*s := vertex_linear E hm j T η hη
    _ ≤ s^2 := by rw [pow_two]; exact Nat.mul_le_mul_right s hs
    _ ≤ s^L := Nat.pow_le_pow_right (by omega) hL

end DetDLP.S8N.MomentGraphBounds
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentDestination
open Groundwork S8H S8H0 S8H.PointAddresses S8J.CircuitRealizes

def entry (e : ℕ) (s : ℕ → ℕ) (i : ℕ) :=
  if i < e then i else if i-e < e then i-e else CycleCode.next e s (i-e-e)

def dstUsing (name : List Bool → ℕ → ℕ) (w : List Bool) (i : ℕ) :=
  (PortPoly.decoded w).1 + MomentDimensions.incidences w +
    entry (MomentDimensions.incidences w) (name w) i

private theorem entryPoly {α : Type} [Enc α] {e g i : α → ℕ} {name : α → ℕ → ℕ}
    (hn : PolyT e) (hu : Unary e) (hg : PolyT g) (hi : PolyT i)
    (hs : PolyT fun z : α × ℕ => name z.1 z.2) :
    PolyT fun x => g x+e x+entry (e x) (name x) (i x) := by
  have j := PolyT.sub hi hn
  have r := PolyT.sub j hn
  have step := CycleCode.next_poly hu r hs
  exact PolyT.add (PolyT.add hg hn) (PolyT.ite' (PolyT.decide_lt hi hn) hi
    (PolyT.ite' (PolyT.decide_lt j hn) j step))

set_option maxHeartbeats 900000 in
theorem dstUsing_poly_of_unary {name : List Bool → ℕ → ℕ} (hu : Unary MomentDimensions.incidences)
    (hn : PolyT fun z : List Bool × ℕ => name z.1 z.2) :
    PolyT fun z : List Bool × ℕ => dstUsing name z.1 z.2 := by
  let α := List Bool × ℕ
  have w : PolyT (@Prod.fst (List Bool) ℕ) := PolyT.fst PolyT.id'
  have i : PolyT (@Prod.snd (List Bool) ℕ) := PolyT.snd PolyT.id'
  have name' : PolyT fun z : α × ℕ => name z.1.1 z.2 :=
    PolyT.comp hn (PolyT.prodMk (PolyT.fst (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id'))
  exact @entryPoly α _ (fun z => MomentDimensions.incidences z.1)
    (fun z => (PortPoly.decoded z.1).1) Prod.snd (fun z => name z.1)
    (PolyT.comp (f:=MomentDimensions.incidences) (g:=Prod.fst) MomentDimensions.incidences_poly w)
    (PolyT.comp (f:=fun x => List.replicate (MomentDimensions.incidences x) ()) (g:=Prod.fst) hu w)
    (PolyT.comp (f:=fun w => (PortPoly.decoded w).1) (g:=Prod.fst) PortPoly.decoded_poly.1 w) i name'

private theorem cycleDst {B : Block} {k : ℕ} (W : Wiring B.A.ne k) {c : Code} (hc : Models c B.A)
    (name : ℕ → ℕ) (h : ∀ i : Fin B.A.ne, name i.val = (W.signal i).val)
    (w : NamedWires.next W.signal = W.next) (i : Fin (G B W).nE) :
    c.ng+c.ne+entry c.ne name i.val = ((G B W).endpoints i).2.val := by
  have eq := AnchoredLayout.next_congr (fun i : Fin B.A.ne => name i.val) W.signal
    (fun i j => by rw [h i,h j]; exact Fin.val_inj)
  have H := CycleCode.models hc name
  rw [eq,w] at H
  exact congrArg₂ Nat.add H.ng (H.bit i)

theorem dstUsing_word {name : List Bool → ℕ → ℕ} {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (hp : 3 < p) (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool)
    (h : ∀ i : Fin (MomentPort.core E hm j T η).A.ne,
      name (DetDLP.S8N.MomentTag.word E j T η) i.val = ((MomentPort.wires E hm j T η).signal i).val)
    (i : Fin (G (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).nE) :
    dstUsing name (DetDLP.S8N.MomentTag.word E j T η) i.val =
      ((G (MomentPort.core E hm j T η) (MomentPort.wires E hm j T η)).endpoints i).2.val := by
  let w := DetDLP.S8N.MomentTag.word E j T η
  have H := MomentOwner.code_models E hm j T η
  have n : MomentDimensions.incidences w = (MomentOwner.code w).ne :=
    (MomentDimensions.incidences_word E hm j T η).trans H.ne.symm
  have g : (PortPoly.decoded w).1 = (MomentOwner.code w).ng := (MomentPort.decodedFits E hp hm j T η).1.trans H.ng.symm
  change dstUsing name w i.val = _
  rw [dstUsing,n,g]
  exact cycleDst _ H (name w) h rfl i

end DetDLP.S8N.MomentDestination
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentDestination
open Groundwork

theorem dstUsing_poly {name : List Bool → ℕ → ℕ} (hn : PolyT fun z : List Bool × ℕ => name z.1 z.2) :
    PolyT fun z : List Bool × ℕ => dstUsing name z.1 z.2 :=
  dstUsing_poly_of_unary MomentUnary.incidences_unary hn

end DetDLP.S8N.MomentDestination
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentRealizes

open S8J.CircuitRealizes DetDLP.S8N.MomentTag w4_M5Network
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
noncomputable section

abbrev Addresses := S8G.FpMoment.Code.Addresses
abbrev blocks (p : ℕ) : 1 ≤ blockCount (bitLen p) :=
  (by decide : 1 ≤ 2).trans (le_max_left _ _)

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (j : Fin 4) (T : ℕ) (η : List Bool)

abbrev AtWord (a : Addresses) : Prop :=
  let w := word E j T η
  let g := G (MomentPort.core E (blocks p) j T η) (MomentPort.wires E (blocks p) j T η)
  a.nv w = g.nV ∧ a.ne w = g.nE ∧
    (∀ i : Fin g.nE, a.src w i.val = (g.endpoints i).1.val) ∧
    (∀ i : Fin g.nE, a.dst w i.val = (g.endpoints i).2.val)

theorem ofAddresses [E.IsElliptic] (a : Addresses) (hp : 3 < p) (hT : T ≤ p)
    (hη : η.length ≤ blockCount (bitLen p)*4*bitLen p) (ha : AtWord E j T η a) :
    S8C.Realizes (S8N.MomentHeader.make a) (S8C.portPacket MomentPort.check) MomentPacket.constant
      (word E j T η) (bitLen p) (S8I.ECQueryCount.value p (blockCount (bitLen p)) E T η j) := by
  let hm := blocks p
  let b := MomentPort.core E hm j T η
  let W := MomentPort.wires E hm j T η
  let s := S8N.MomentHeader.scale (blockCount (bitLen p)) (bitLen p)
  let w := word E j T η
  have hscale : bitLen p + 2 ≤ s := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hm)
  have hs : 2 ≤ s := by omega
  have hbase : bitLen p ≤ s := by omega
  have he := MomentEdgeBounds.graph_budget E hm j T η hη
  have hbudget := MomentPacket.wordBudget E j η hT hη
  let A := circuit b W
  let sem : Logical b W ≃ {bits : Fin A.nb → Bool // ∀ g,
      test b W g (fun e => bits (A.bit e.1)) = true} :=
    (decode b W).symm.trans (w3_factorEquiv _ _)
  rw [← DetDLP.s8n_moment_assignment_count_inline E hp hm hT η hη j]
  apply realizes b W _ _ _ s _ w sem hs hbase he
    (MomentGraphBounds.vertex_budget E hm j T η (by decide : 2 ≤ MomentPacket.constant) hη)
    (MomentGraphBounds.degree_budget E hm j T η) hbudget.1 hbudget.2
    (MomentPacket.make_word E j T η a (G b W) ha.1 ha.2.1 ha.2.2.1 ha.2.2.2)
  intro v assignments
  refine ⟨?_, MomentPort.port_eval E hp hm j T η v assignments⟩
  have hq := (w3_incQueryBounds (circuit b W) (MomentGraphBounds.gate_surj E hm j T η)
    s (by omega) he.le w).2 v assignments
  let n := s + w.length + 1
  calc
    _ ≤ n^5 := Nat.le_trans (Nat.le_succ _) hq
    _ ≤ n^MomentPacket.constant := Nat.pow_le_pow_right (by dsimp [n]; omega) (by decide)
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by decide : 0 < MomentPacket.constant)

theorem tag (a : Addresses) (ha : a.Uniform)
    (hw : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
      (j : Fin 4) (T : ℕ) (η : List Bool), T ≤ p → η.length ≤ blockCount (bitLen p)*4*bitLen p →
      AtWord E j T η a) : S8C.TagSpec [2] := by
  refine tagIntro _ _ MomentPacket.constant (S8N.MomentHeader.make_poly a ha)
    (S8C.portPacket_poly MomentPort.check_poly) ?_
  intro p _ hp E _ j T η hT hη
  exact ofAddresses E j T η a hp hT hη (hw p hp E j T η hT hη)

end
end DetDLP.S8N.MomentRealizes
end

section
set_option autoImplicit false
open DetDLP DetDLP.S8N

private def momentAddresses (signal : List Bool → ℕ → ℕ) : MomentRealizes.Addresses :=
  ⟨MomentDimensions.nv, MomentDimensions.ne, MomentOwner.src,
    MomentDestination.dstUsing signal, MomentPort.check⟩

attribute [local irreducible] MomentDimensions.nv MomentDimensions.ne MomentOwner.src
  MomentDestination.dstUsing MomentPort.check

private theorem uniform (signal : List Bool → ℕ → ℕ)
    (hs : Groundwork.PolyT (fun z : List Bool × ℕ => signal z.1 z.2)) : (momentAddresses signal).Uniform := by
  unfold momentAddresses
  constructor
  · exact MomentDimensions.nv_poly
  · exact MomentDimensions.ne_poly
  · exact MomentUnary.vert
  · exact MomentUnary.edge
  · exact MomentOwner.src_poly
  · exact MomentDestination.dstUsing_poly (name := signal) hs
  · exact MomentPort.check_poly

theorem solution : S8C.GadgetLaws → S8C.TagSpec [2] := by
  intro _
  obtain ⟨signal, hs, hsword⟩ := s8n_ec_moment_signal_addresses
  apply MomentRealizes.tag (momentAddresses signal) (uniform signal hs)
  intro p _ hp E _ j T η _ _
  let hm := MomentRealizes.blocks p
  unfold MomentRealizes.AtWord momentAddresses
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact MomentDimensions.nv_of_gateCount E hm j T η (MomentPort.decodedFits E hp hm j T η).1
  · exact MomentDimensions.ne_word E hm j T η
  · exact MomentOwner.src_of_gateCount E hm j T η (MomentPort.decodedFits E hp hm j T η).1
  · exact MomentDestination.dstUsing_word (name := signal) E hp hm j T η
      (hsword p E hm j T η)
end
