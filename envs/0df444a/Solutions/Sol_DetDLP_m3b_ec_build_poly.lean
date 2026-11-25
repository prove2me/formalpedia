-- Prove2me | solution 1 for DetDLP.m3b_ec_build_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T23:26:59.83156+00:00
-- url     : https://prove2.me/submissions/eb9a9286-55ce-47ee-b05c-02a89d227655

import Definitions.Def_DetDLP_M3B_ECPolyDefs

set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP DetDLP.M3B.ECPolyDefs Groundwork
open DetDLP_W1_Queries (first more first_poly more_poly)
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const
  PolyT.length PolyT.mul PolyT.div PolyT.mod PolyT.map PolyT.getD
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  P2M_Groundwork_PolyT_ite__226169acf219 first_poly more_poly w4_M5Evaluator.clog2_poly
variable {α : Type} [Enc α]

private def step (n : ℕ) (c : List W × W) (_ : Bool) : List W × W :=
  if c.2.headD false = true then ((first c.2 |>.take n) :: c.1, (more c.2).take n) else c
private theorem parseP {f : α → W} (hf : PolyT f) : PolyT fun x => frames (f x) := by
  change PolyT fun x => (((f x).foldl (step (f x).length) ([],f x)).1).reverse
  apply PolyT.reverse; apply PolyT.fst; apply PolyT.foldl_add hf (by fun_prop) (by unfold step; fun_prop)
  obtain ⟨_,t,ht,_,_,hlen⟩ := hf.elim
  refine ⟨fun n => 6*t n+8, ((PB.const 6).mul ht).add (PB.const 8), ?_⟩
  intro x ⟨acc,w⟩ e he; have h := hlen x; rw [len_bools] at h; unfold step; split
  · simp only [len_pair,len_cons,len_bools,List.length_take]; omega
  · omega

private theorem decodeP {f : α → W} (hf : PolyT f) :
    PolyT fun x => w5_M6Sort.decode (f x) := PolyT.comp w5_M6Sort.decode_poly hf

private theorem addU {f g : α → ℕ} (a : Unary f) (b : Unary g) :
    Unary fun x => f x + g x := by simpa only [Unary,List.replicate_add] using PolyT.append a b

private theorem unary_mul {α} [Enc α] {g h : α → ℕ} (hg : Unary g) (hh : Unary h) :
    Unary (fun x => g x * h x) := by
  have H : PolyT (fun x => (List.replicate (g x) ()).flatMap (fun _ => List.replicate (h x) ())) :=
    Groundwork.PolyT.flatMap (Groundwork.PolyT.comp (g := fun p : α × Unit => p.1) hh (by fun_prop)) hg
  apply H.congr; intro x
  change _ = List.replicate (g x * h x) ()
  generalize g x = n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.flatMap_cons, ih, Nat.succ_mul]
    rw [← List.replicate_add, Nat.add_comm]

private theorem clogU {f : α → ℕ} (h : PolyT f) : Unary fun x => Nat.clog 2 (f x) := by
  apply (PolyT.unary_min_length (w4_M5Evaluator.clog2_poly h) (PolyT.bits h)).congr
  intro x; dsimp only; rw [min_eq_left]; rw [Nat.size_eq_bits_len]; exact Nat.clog_le_of_le_pow (Nat.lt_size_self _).le

private theorem asP {f : α → ℕ} (h : Unary f) : PolyT f := by
  simpa only [List.length_replicate] using PolyT.length h

open S8H.PointAddresses (wires)
attribute [local fun_prop] parseP decodeP w4_M5EdgeNat.srcNat_poly w4_M5EdgeNat.dstNat_poly
  w4_M5Evaluator.vertexCount_poly w5_M6Sort.cw_poly DetDLP_W1_Queries.frame_poly
  PolyT.testBit PolyT.decide_eq PolyT.decide_le PolyT.decide_lt

private theorem wiresP {d : α → ℕ} (hd : PolyT d) : PolyT fun x => wires (d x) := S8H.PointAddresses.mul_poly.nb hd
attribute [local fun_prop] wiresP
private theorem maxP {a b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => max (a x) (b x) := by simp only [max_def]; fun_prop
attribute [local fun_prop] maxP
private structure Eff (a : α → N) : Prop where
  g : PolyT fun x => ng (a x)
  e : PolyT fun x => ne (a x)
  o : ∀ {i : α → ℕ}, PolyT i → PolyT fun x => gate (a x) (i x)
  s : ∀ {i : α → ℕ}, PolyT i → PolyT fun x => signal (a x) (i x)

private theorem catP {a b : α → N} (A : Eff a) (B : Eff b) : Eff fun x => cat (a x) (b x) := by
  refine ⟨PolyT.add A.g B.g,PolyT.add A.e B.e,fun hi => ?_,fun hi => ?_⟩
  · exact PolyT.ite' (PolyT.decide_lt hi A.e) (A.o hi) (PolyT.add A.g (B.o (PolyT.sub hi A.e)))
  · exact PolyT.ite' (PolyT.decide_lt hi A.e) (A.s hi) (B.s (PolyT.sub hi A.e))

private theorem cpP {n : α → ℕ} {F : α → ℕ → N} (hn : PolyT n)
    (h : ∀ {j : α → ℕ}, PolyT j → Eff (fun x => F x (j x))) : Eff fun x => copies (n x) (F x) := by
  have Z := h (PolyT.const 0); refine ⟨PolyT.mul hn Z.g,PolyT.mul hn Z.e,fun hi => ?_,fun hi => ?_⟩
  · exact PolyT.add (PolyT.mul (PolyT.div hi Z.e) Z.g) ((h (PolyT.div hi Z.e)).o (PolyT.mod hi Z.e))
  · exact (h (PolyT.div hi Z.e)).s (PolyT.mod hi Z.e)

private theorem rowP {n m : α → ℕ} {w : α → ℕ → ℕ → Bit} {t : α → ℕ → (ℕ → Bool) → Bool}
    (hn : PolyT n) (hm : PolyT m) (hw : ∀ {i j : α → ℕ}, PolyT i → PolyT j → PolyT fun x => (w x (i x) (j x)).1) :
    Eff fun x => rows (n x) (m x) (w x) (t x) :=
  ⟨hn,PolyT.mul hn hm,fun hi => PolyT.div hi hm,fun hi => hw (PolyT.div hi hm) (PolyT.mod hi hm)⟩

private abbrev WordP (a : α → Word) := ∀ {i : α → ℕ}, PolyT i → PolyT fun x => (a x (i x)).1
private theorem eqP {n : α → ℕ} {a b : α → Word} (hn : PolyT n) (ha : WordP a) (hb : WordP b) :
    Eff fun x => eqs (n x) (a x) (b x) := by
  apply rowP hn (PolyT.const 2); intro i j hi hj
  simpa only [apply_ite Prod.fst] using PolyT.ite' (PolyT.decide_eq hj (PolyT.const 0)) (ha hi) (hb hi)

private theorem piece {β : Type} [Enc β] {i : α → ℕ} {a : α → β} {b : α → ℕ → β}
    (hi : PolyT i) (ha : PolyT a) (hb : ∀ {j : α → ℕ}, PolyT j → PolyT fun x => b x (j x)) :
    PolyT fun x => Nat.casesOn (motive:=fun _ => β) (i x) (a x) (b x) := by
  apply (PolyT.ite' (PolyT.decide_eq hi (PolyT.const 0)) ha (hb (PolyT.sub hi (PolyT.const 1)))).congr
  intro x; cases i x <;> simp

private theorem colP {n : α → ℕ} {v : α → Bool} {a b z c : α → Word} (hn : PolyT n)
    (ha : WordP a) (hb : WordP b) (hz : WordP z) (hc : WordP c) :
    Eff fun x => col (n x) (v x) (a x) (b x) (z x) (c x) := by
  unfold col; dsimp only; apply rowP hn (PolyT.const 5); intro i j hi hj
  let d := fun x => (c x (if i x=0 then n x-1 else i x-1)).1
  have hD : PolyT d := hc (PolyT.ite' (PolyT.decide_eq hi (PolyT.const 0)) (PolyT.sub hn (PolyT.const 1)) (PolyT.sub hi (PolyT.const 1)))
  let f := fun x => if j x=0 then (a x (i x)).1 else if j x=1 then (b x (i x)).1 else if j x=2 then (z x (i x)).1 else if j x=3 then (c x (i x)).1 else d x
  have F : PolyT f := PolyT.ite' (PolyT.decide_eq hj (PolyT.const 0)) (ha hi) (PolyT.ite' (PolyT.decide_eq hj (PolyT.const 1)) (hb hi) (PolyT.ite' (PolyT.decide_eq hj (PolyT.const 2)) (hz hi) (PolyT.ite' (PolyT.decide_eq hj (PolyT.const 3)) (hc hi) hD)))
  apply F.congr; intro x; dsimp [f,d]; rcases j x with _|_|_|_|_ <;> rfl


private theorem prodP {K d off : α → ℕ} {a b z : α → Word} (hd : PolyT d) (ho : PolyT off)
    (ha : WordP a) (hb : WordP b) (hz : WordP z) : Eff fun x => M3B.ECPolyDefs.prod (K x) (d x) (off x) (a x) (b x) (z x) := by
  unfold M3B.ECPolyDefs.prod; dsimp only; apply catP
  · have h := S8H.PointAddresses.mul_poly; exact ⟨h.ng hd,h.ne hd,fun hi => h.gate hd hi,fun hi => PolyT.add ho (h.bit hd hi)⟩
  · apply eqP (PolyT.mul (PolyT.const 4) hd)
    · intro i hi; change PolyT fun x => off x + if i x < 2*d x then i x else wires (d x)-2*d x+(i x-2*d x)
      let two := PolyT.mul (PolyT.const 2) hd; exact PolyT.add ho (PolyT.ite' (PolyT.decide_lt hi two) hi (PolyT.add (PolyT.sub (wiresP hd) two) (PolyT.sub hi two)))
    · intro i hi; simp only [apply_ite Prod.fst]; apply PolyT.ite' (PolyT.decide_lt hi hd) (ha hi)
      exact PolyT.ite' (PolyT.decide_lt hi (PolyT.mul (PolyT.const 2) hd)) (hb (PolyT.sub hi hd)) (hz (PolyT.sub hi (PolyT.mul (PolyT.const 2) hd)))

private theorem wordP {K n off : α → ℕ} (hk : PolyT K) (hn : PolyT n) (ho : PolyT off) :
    WordP fun x => word (K x) (off x) (n x) := by
  intro j hj; simp only [word,apply_ite Prod.fst,reg,pin]; exact PolyT.ite' (PolyT.decide_lt hj hn) (PolyT.add ho hj) hk
private theorem pubP {K n : α → ℕ} (hk : PolyT K) : WordP fun x => pub (K x) (n x) := fun _ => hk
private theorem regP {k : α → ℕ} (h : PolyT k) : PolyT fun x => (reg (k x)).1 := h
private theorem maskP {k : α → ℕ} {b : α → Bool} (h : PolyT k) : PolyT fun x => (mask (k x) (b x)).1 := h
private theorem hashP {K p d e r ax : α → ℕ} {a b z : α → Word}
    (hK : PolyT K) (hd : PolyT d) (he : PolyT e) (hr : PolyT r) (hx : PolyT ax)
    (ha : WordP a) (hb : WordP b) (hz : WordP z) : Eff fun x => M3B.ECPolyDefs.hash (K x) (p x) (d x) (e x) (r x) (ax x) (a x) (b x) (z x) := by
  let two := PolyT.mul (PolyT.const 2) hd; let one := PolyT.add hd (PolyT.const 1)
  let tr := PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1)
  let rem := PolyT.add hr tr; let q := PolyT.add rem tr; let u := PolyT.add q hd
  let v := PolyT.add (PolyT.add u two) he; let cp := PolyT.add (PolyT.add v two) he
  let sum : WordP (fun x => word (K x) (ax x+2*d x) (d x+1)) := wordP hK one (PolyT.add hx two)
  let c1 : WordP (fun x j => reg (ax x+j)) := fun hj => PolyT.add hx hj
  let c2 : WordP (fun x j => reg (ax x+3*d x+1+j)) := fun hj => PolyT.add (PolyT.add (PolyT.add hx (PolyT.mul (PolyT.const 3) hd)) (PolyT.const 1)) hj
  let c3 : WordP (fun x j => reg (ax x+4*d x+2+j)) := fun hj => PolyT.add (PolyT.add (PolyT.add hx (PolyT.mul (PolyT.const 4) hd)) (PolyT.const 2)) hj
  unfold M3B.ECPolyDefs.hash; dsimp only
  exact catP (catP (prodP hd (PolyT.add u two) ha hb (wordP hK two u))
    (prodP hd (PolyT.add v two) (wordP hK hd q) (pubP hK) (wordP hK two v)))
    (catP (colP two (wordP hK two v) (wordP hK hd rem) (wordP hK two u) c1)
      (catP (colP one (wordP hK hd rem) hz sum c2) (colP one (wordP hK hd hr) (fun _ => cp) sum c3)))

private theorem bndP {K p d t : α → ℕ} (hK : PolyT K) (hd : PolyT d) (ht : PolyT t) : Eff fun x => bnd (K x) (p x) (d x) (t x) := by
  unfold bnd; refine colP (PolyT.add hd (PolyT.const 1)) (wordP hK hd ht) (wordP hK hd (PolyT.add ht hd)) (pubP hK) ?_
  intro j hj; exact PolyT.add (PolyT.add ht (PolyT.mul (PolyT.const 2) hd)) hj
private theorem pboundP {K p d t : α → ℕ} (hK : PolyT K) (hd : PolyT d) (ht : PolyT t) : Eff fun x => pbound (K x) (p x) (d x) (t x) := by
  unfold pbound; exact catP (bndP hK hd (PolyT.add ht (PolyT.const 1))) (bndP hK hd (PolyT.add (PolyT.add ht (PolyT.const 1)) (PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1))))
private theorem gboundP {K p d t : α → ℕ} (hK : PolyT K) (hd : PolyT d) (ht : PolyT t) : Eff fun x => gbound (K x) (p x) (d x) (t x) := by
  unfold gbound; exact catP (bndP hK hd ht) (bndP hK hd (PolyT.add ht (PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1))))

private theorem boundedCases {β : Type} [Enc β] (n : ℕ) {f : α → ℕ → β} {i : α → ℕ} (hi : PolyT i)
    (atJ : ∀ j ≤ n, PolyT fun x => f x j) (last : ∀ x j, n ≤ j → f x j = f x n) : PolyT fun x => f x (i x) := by
  induction n generalizing f i with
  | zero => exact (atJ 0 le_rfl).congr fun x => (last x (i x) (Nat.zero_le _)).symm
  | succ n ih =>
    have hs := ih (f:=fun x j => f x (j+1)) (i:=fun x => i x-1) (PolyT.sub hi (PolyT.const 1))
      (fun j hj => atJ (j+1) (by omega)) (fun x j hj => last x (j+1) (by omega))
    apply (PolyT.ite' (PolyT.decide_eq hi (PolyT.const 0)) (atJ 0 (Nat.zero_le _)) hs).congr
    intro x; by_cases h : i x=0
    · simp [h]
    · simp [h,Nat.sub_add_cancel (show 1 ≤ i x by omega)]

private theorem trP {d : α → ℕ} (h : PolyT d) : PolyT fun x => M3B.ECPolyDefs.triple (d x) := PolyT.add (PolyT.mul (PolyT.const 3) h) (PolyT.const 1)
private theorem ptP {d : α → ℕ} (h : PolyT d) : PolyT fun x => pt (d x) := PolyT.add (PolyT.const 1) (PolyT.mul (PolyT.const 2) (trP h))
private theorem runP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => run (d x) (e x) :=
  PolyT.add (PolyT.add (PolyT.add (PolyT.mul (PolyT.const 2) (trP hd)) hd) (PolyT.mul (PolyT.const 2) (PolyT.add (PolyT.mul (PolyT.const 2) hd) he))) (PolyT.const 1)
private theorem auxP {d : α → ℕ} (hd : PolyT d) : PolyT fun x => aux (d x) :=
  PolyT.add (PolyT.mul (PolyT.const 2) hd) (PolyT.mul (PolyT.const 3) (PolyT.add hd (PolyT.const 1)))
private theorem sizeP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => gsize (d x) (e x) := PolyT.add (runP hd he) (auxP hd)
private abbrev ArgP (A : α → Word × Word × Word) := WordP (fun x => (A x).1) ∧ WordP (fun x => (A x).2.1) ∧ WordP (fun x => (A x).2.2)
private abbrev PointP (Q : α → XYZ) := (PolyT fun x => (Q x).1.1) ∧ WordP (fun x => (Q x).2.1) ∧ WordP (fun x => (Q x).2.2)
private theorem ptwP {K d t : α → ℕ} (hK : PolyT K) (hd : PolyT d) (ht : PolyT t) : PointP fun x => ptw (K x) (d x) (t x) :=
  ⟨ht,wordP hK hd (PolyT.add ht (PolyT.const 1)),wordP hK hd (PolyT.add (PolyT.add ht (PolyT.const 1)) (trP hd))⟩
private theorem ghP {K p d e t : α → ℕ} {A : α → Word × Word × Word} (hK : PolyT K) (hd : PolyT d) (he : PolyT e) (ht : PolyT t) (H : ArgP A) :
    Eff fun x => ghash (K x) (p x) (d x) (e x) (t x) (A x) := hashP hK hd he ht (PolyT.add ht (runP hd he)) H.1 H.2.1 H.2.2
private theorem argsCases (n : ℕ) {F : α → ℕ → Word × Word × Word} {i : α → ℕ} (hi : PolyT i)
    (atJ : ∀ j ≤ n, ArgP fun x => F x j) (last : ∀ x j, n ≤ j → F x j = F x n) : ArgP fun x => F x (i x) := by
  refine ⟨fun {b} hb => ?_,fun {b} hb => ?_,fun {b} hb => ?_⟩
  · apply boundedCases n (f:=fun x j => ((F x j).1 (b x)).1) hi
    · exact fun j hj => (atJ j hj).1 hb
    · intro x j hj; rw [last x j hj]
  · apply boundedCases n (f:=fun x j => ((F x j).2.1 (b x)).1) hi
    · exact fun j hj => (atJ j hj).2.1 hb
    · intro x j hj; rw [last x j hj]
  · apply boundedCases n (f:=fun x j => ((F x j).2.2 (b x)).1) hi
    · exact fun j hj => (atJ j hj).2.2 hb
    · intro x j hj; rw [last x j hj]
private theorem wp3 {f a b : α → Word} (hf : WordP f) (ha : WordP a) (hb : WordP b) : ArgP fun x => (f x,a x,b x) := ⟨hf,ha,hb⟩

private theorem rowsCases (c : ℕ) {n m : α → ℕ} {w : α → ℕ → ℕ → Bit} {test : α → ℕ → (ℕ → Bool) → Bool}
    (hn : PolyT n) (hm : PolyT m)
    (atJ : ∀ {i : α → ℕ}, PolyT i → ∀ j ≤ c, PolyT fun x => (w x (i x) j).1)
    (last : ∀ x i j, c ≤ j → w x i j = w x i c) : Eff fun x => rows (n x) (m x) (w x) (test x) := by
  apply rowP hn hm; intro i j hi hj; apply boundedCases c (f:=fun x j => (w x (i x) j).1) hj (atJ hi)
  intro x j h; rw [last x (i x) j h]
private theorem cmpP {n : α → ℕ} {f : α → Bit} {a b : α → Word} {test : α → ℕ → (ℕ → Bool) → Bool}
    (hn : PolyT n) (hf : PolyT fun x => (f x).1) (ha : WordP a) (hb : WordP b) :
    Eff fun x => rows (n x) 3 (fun i j => match j with | 0 => f x | 1 => a x i | _ => b x i) (test x) := by
  apply rowsCases 2 hn (PolyT.const 3)
  · intro i hi j hj; interval_cases j; exact hf; exact ha hi; exact hb hi
  · intro x i j hj; obtain ⟨t,rfl⟩ : ∃ t, j=t+2 := ⟨_,(Nat.sub_add_cancel hj).symm⟩; rfl
private theorem mapP {K p d e t : α → ℕ} {q : α → XYZ}
    (hK : PolyT K) (hd : PolyT d) (he : PolyT e) (ht : PolyT t) (hq : PointP q) :
    Eff fun x => mapN (K x) (p x) (d x) (e x) (t x) (q x) := by
  let go := fun (x : α) (j : ℕ) => t x + pt (d x) + j * gsize (d x) (e x)
  have G {j : α → ℕ} (h : PolyT j) : PolyT fun x => go x (j x) := PolyT.add (PolyT.add ht (ptP hd)) (PolyT.mul h (sizeP hd he))
  have R (j : ℕ) : WordP (fun x => word (K x) (go x j) (d x)) := wordP hK hd (G (PolyT.const j))
  have O := ptwP hK hd ht
  unfold mapN; dsimp only
  refine catP (catP (pboundP hK hd ht) (cpP (PolyT.const 4) (fun h => gboundP hK hd (G h))))
    (catP (cpP (PolyT.const 4) (fun {j} hj => ghP hK hd he (G hj) ?_))
    (catP (eqP (PolyT.const 1) (fun _ => ht) (fun _ => hq.1)) (catP ?_ ?_)))
  · apply argsCases 3 (F:=fun x l => match l with
      | 0 => (pub (K x) (36%p x),(q x).2.1,pub (K x) 0)
      | 1 => (pub (K x) 0,(q x).2.1,pub (K x) 0)
      | 2 => (pub (K x) (2%p x),(q x).2.2,word (K x) (go x 1) (d x))
      | _ => (pub (K x) (108%p x),word (K x) (go x 2) (d x),pub (K x) 0)) hj
    · intro l hl; interval_cases l
      · exact wp3 (pubP hK) hq.2.1 (pubP hK)
      · exact wp3 (pubP hK) hq.2.1 (pubP hK)
      · exact wp3 (pubP hK) hq.2.2 (R 1)
      · exact wp3 (pubP hK) (R 2) (pubP hK)
    · intro x l hl; obtain ⟨j,rfl⟩ : ∃ j, l=j+3 := ⟨l-3,by omega⟩; rfl
  · exact cmpP hd hq.1 O.2.1 (R 0)
  · exact cmpP hd hq.1 O.2.2 (R 3)

private theorem row5P {n : α → ℕ} {t : α → ℕ → (ℕ → Bool) → Bool} {f0 : α → Bit} {w0 w1 w2 w3 : α → Word}
    (hn : PolyT n) (F0 : PolyT fun x => (f0 x).1)
    (W0 : WordP w0) (W1 : WordP w1) (W2 : WordP w2) (W3 : WordP w3) :
    Eff fun x => rows (n x) 5 (fun k j => match j with | 0 => f0 x | 1 => w0 x k | 2 => w1 x k | 3 => w2 x k | _ => w3 x k) (t x) := by
  apply rowsCases 4 hn (PolyT.const 5)
  · intro i hi j hj; interval_cases j
    · exact F0
    · exact W0 hi
    · exact W1 hi
    · exact W2 hi
    · exact W3 hi
  · intro x i j hj; obtain ⟨t,rfl⟩ : ∃ t, j=t+4 := ⟨_,(Nat.sub_add_cancel hj).symm⟩; rfl

private theorem row9P {n : α → ℕ} {t : α → ℕ → (ℕ → Bool) → Bool} {f0 f1 f2 f3 : α → Bit} {w0 w1 w2 w3 w4 : α → Word}
    (hn : PolyT n) (F0 : PolyT fun x => (f0 x).1) (F1 : PolyT fun x => (f1 x).1) (F2 : PolyT fun x => (f2 x).1) (F3 : PolyT fun x => (f3 x).1)
    (W0 : WordP w0) (W1 : WordP w1) (W2 : WordP w2) (W3 : WordP w3) (W4 : WordP w4) :
    Eff fun x => rows (n x) 9 (fun k j => match j with | 0 => f0 x | 1 => f1 x | 2 => f2 x | 3 => f3 x | 4 => w0 x k | 5 => w1 x k | 6 => w2 x k | 7 => w3 x k | _ => w4 x k) (t x) := by
  apply rowsCases 8 hn (PolyT.const 9)
  · intro i hi j hj; interval_cases j
    · exact F0
    · exact F1
    · exact F2
    · exact F3
    · exact W0 hi
    · exact W1 hi
    · exact W2 hi
    · exact W3 hi
    · exact W4 hi
  · intro x i j hj; obtain ⟨t,rfl⟩ : ∃ t, j=t+8 := ⟨_,(Nat.sub_add_cancel hj).symm⟩; rfl

private theorem addNP {K p d e t c : α → ℕ} {P Q : α → XYZ} (hK : PolyT K) (hd : PolyT d) (he : PolyT e) (ht : PolyT t) (hP : PointP P) (hQ : PointP Q) : Eff fun x => addN (K x) (p x) (d x) (e x) (t x) (c x) (P x) (Q x) := by
  let cp := fun (x : α) (j : ℕ) => t x+pt (d x)+j*(1+M3B.ECPolyDefs.triple (d x))
  let go := fun (x : α) (j : ℕ) => cp x 2+d x+j*gsize (d x) (e x)
  have C {j : α → ℕ} (h : PolyT j) : PolyT fun x => cp x (j x) := PolyT.add (PolyT.add ht (ptP hd)) (PolyT.mul h (PolyT.add (PolyT.const 1) (trP hd)))
  have T {j : α → ℕ} (h : PolyT j) : PolyT fun x => go x (j x) := PolyT.add (PolyT.add (C (PolyT.const 2)) hd) (PolyT.mul h (sizeP hd he))
  have A (j : ℕ) : WordP fun x => word (K x) (cp x j+1) (d x) := wordP hK hd (PolyT.add (C (PolyT.const j)) (PolyT.const 1))
  have G (j : ℕ) : WordP fun x => word (K x) (go x j) (d x) := wordP hK hd (T (PolyT.const j))
  have L : WordP fun x => word (K x) (cp x 2) (d x) := wordP hK hd (C (PolyT.const 2))
  let args := fun (x : α) (j : ℕ) => match j with
    | 0 => (pub (K x) (p x-1),(P x).2.1,(Q x).2.1)
    | 1 => (word (K x) (go x 0) (d x),word (K x) (cp x 0+1) (d x),pub (K x) 0)
    | 2 => (pub (K x) 1,(P x).2.2,(Q x).2.2)
    | 3 => (word (K x) (go x 2) (d x),word (K x) (cp x 1+1) (d x),pub (K x) 0)
    | 4 => (pub (K x) (p x-1),(P x).2.2,(Q x).2.2)
    | 5 => (word (K x) (go x 4) (d x),word (K x) (cp x 0+1) (d x),pub (K x) 0)
    | 6 => ((P x).2.1,(P x).2.1,pub (K x) 0)
    | 7 => (pub (K x) 3,word (K x) (go x 6) (d x),pub (K x) (c x))
    | 8 => (word (K x) (go x 7) (d x),word (K x) (cp x 1+1) (d x),pub (K x) 0)
    | 9 => (word (K x) (cp x 2) (d x),word (K x) (cp x 2) (d x),pub (K x) 0)
    | 10 => (pub (K x) (p x-1),(P x).2.1,word (K x) (go x 9) (d x))
    | 11 => (pub (K x) (p x-1),(Q x).2.1,word (K x) (go x 10) (d x))
    | 12 => (pub (K x) (p x-1),word (K x) (go x 11) (d x),(P x).2.1)
    | 13 => (word (K x) (cp x 2) (d x),word (K x) (go x 12) (d x),pub (K x) 0)
    | _ => (pub (K x) (p x-1),(P x).2.2,word (K x) (go x 13) (d x))
  have HA {j : α → ℕ} (hj : PolyT j) : ArgP fun x => args x (j x) := by
    apply argsCases 14 (F:=args) hj
    · intro l hl; interval_cases l
      · exact wp3 (pubP hK) hP.2.1 hQ.2.1
      · exact wp3 (G 0) (A 0) (pubP hK)
      · exact wp3 (pubP hK) hP.2.2 hQ.2.2
      · exact wp3 (G 2) (A 1) (pubP hK)
      · exact wp3 (pubP hK) hP.2.2 hQ.2.2
      · exact wp3 (G 4) (A 0) (pubP hK)
      · exact wp3 hP.2.1 hP.2.1 (pubP hK)
      · exact wp3 (pubP hK) (G 6) (pubP hK)
      · exact wp3 (G 7) (A 1) (pubP hK)
      · exact wp3 L L (pubP hK)
      · exact wp3 (pubP hK) hP.2.1 (G 9)
      · exact wp3 (pubP hK) hQ.2.1 (G 10)
      · exact wp3 (pubP hK) (G 11) hP.2.1
      · exact wp3 L (G 12) (pubP hK)
      · exact wp3 (pubP hK) hP.2.2 (G 13)
    · intro x l hl; obtain ⟨k,rfl⟩ : ∃ k, l=k+14 := ⟨_,(Nat.sub_add_cancel hl).symm⟩; rfl
  have O := ptwP hK hd ht
  unfold addN; dsimp only
  refine catP (catP (pboundP hK hd ht) (catP (cpP (PolyT.const 2) (fun h => bndP hK hd (PolyT.add (C h) (PolyT.const 1)))) (cpP (PolyT.const 15) (fun h => gboundP hK hd (T h)))))
    (catP (cpP (PolyT.const 15) (fun h => ghP hK hd he (T h) (HA h))) (catP ?_ (catP ?_ (catP ?_ (catP ?_ (catP ?_ ?_))))))
  · exact row5P hd (C (PolyT.const 0)) (G 0) (A 0) (G 1) (pubP hK)
  · exact row5P hd (C (PolyT.const 1)) (G 2) (A 1) (G 3) (pubP hK)
  · exact row9P hd hP.1 hQ.1 (C (PolyT.const 0)) (C (PolyT.const 1)) L (G 5) (G 8) (pubP hK) (pubP hK)
  · exact row9P (PolyT.const 1) hP.1 hQ.1 (C (PolyT.const 0)) (C (PolyT.const 1)) (fun _ => ht) (fun _ => hQ.1) (pubP hK) (pubP hK) (pubP hK)
  · exact row9P hd hP.1 hQ.1 (C (PolyT.const 0)) (C (PolyT.const 1)) O.2.1 hQ.2.1 hP.2.1 (pubP hK) (G 11)
  · exact row9P hd hP.1 hQ.1 (C (PolyT.const 0)) (C (PolyT.const 1)) O.2.2 hQ.2.2 hP.2.2 (pubP hK) (G 14)

private theorem selectP {K a b pos neg : α → ℕ} (hk : PolyT K) (ha : PolyT a) (hb : PolyT b) (hp : PolyT pos) (hn : PolyT neg) : WordP fun x => select (K x) (a x) (b x) (pos x) (neg x) := by
  intro j hj
  have A := PolyT.testBit ha hj; have B := PolyT.testBit hb hj
  let ff := fun x => if (a x).testBit (j x) then (if (b x).testBit (j x) then K x else neg x) else (if (b x).testBit (j x) then pos x else K x)
  have F : PolyT ff := PolyT.ite' (PolyT.decide_eq_true A) (PolyT.ite' (PolyT.decide_eq_true B) hk hn) (PolyT.ite' (PolyT.decide_eq_true B) hp hk)
  apply F.congr; intro x; dsimp [ff,select]; cases (a x).testBit (j x) <;> cases (b x).testBit (j x) <;> rfl
private theorem bankP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => bankSize (d x) (e x) :=
  PolyT.add (PolyT.add (ptP hd) (PolyT.mul (PolyT.const 7) (runP hd he))) (PolyT.mul (PolyT.const 7) (auxP hd))
private theorem slotSizeP {d e w : α → ℕ} (hd : PolyT d) (he : PolyT e) (hw : PolyT w) : PolyT fun x => slotSize (d x) (e x) (w x) :=
  PolyT.add (PolyT.add (PolyT.add (bankP hd he) hd) (PolyT.add hd (PolyT.const 1))) (PolyT.mul (PolyT.const 3) hw)
private theorem slotP {K p d e w t T b : α → ℕ} {cs seed : α → List ℕ} (hK : PolyT K) (hd : PolyT d) (he : PolyT e) (ht : PolyT t) (hS : PolyT seed) (hb : PolyT b) :
    Eff fun x => slotN (K x) (p x) (d x) (e x) (w x) (t x) (T x) (cs x) (seed x) (b x) := by
  let r := fun (x : α) (i : ℕ) => t x+pt (d x)+i*run (d x) (e x)
  let yo := fun x => t x+1+M3B.ECPolyDefs.triple (d x)
  let diff := fun x => t x+bankSize (d x) (e x)
  have HR {j : α → ℕ} (hj : PolyT j) : PolyT fun x => r x (j x) := PolyT.add (PolyT.add ht (ptP hd)) (PolyT.mul hj (runP hd he))
  have HY : PolyT yo := PolyT.add (PolyT.add ht (PolyT.const 1)) (trP hd)
  have D : PolyT diff := PolyT.add ht (bankP hd he)
  let X := fun x => word (K x) (t x+1) (d x); let Y := fun x => word (K x) (yo x) (d x)
  let g := fun x i => word (K x) (r x i) (d x); let u := fun x i => pub (K x) ((cs x).getD i 0)
  let pick := fun x l => select (K x) ((seed x).getD (4*b x+l) 0) ((seed x).getD (4*b x+2+l) 0) (yo x) (t x)
  have Xp : WordP X := wordP hK hd (PolyT.add ht (PolyT.const 1)); have Yp : WordP Y := wordP hK hd HY
  have G (j : ℕ) : WordP fun x => g x j := wordP hK hd (HR (PolyT.const j))
  have PP (j : ℕ) : WordP fun x => pick x j := by
    let u := PolyT.mul (PolyT.const 4) hb
    intro l hl
    exact selectP hK (PolyT.getD hS (PolyT.add u (PolyT.const j)) (PolyT.const 0)) (PolyT.getD hS (PolyT.add (PolyT.add u (PolyT.const 2)) (PolyT.const j)) (PolyT.const 0)) HY ht hl
  let args := fun x (i : ℕ) => match i with
    | 0 => (u x 1,X x,Y x) | 1 => (pub (K x) 1,g x 0,u x 3) | 2 => (g x 1,Y x,pub (K x) 0)
    | 3 => (pub (K x) 1,X x,u x 2) | 4 => (g x 3,X x,u x 4) | 5 => (g x 4,X x,u x 5) | _ => (pick x 0,X x,pick x 1)
  have HA {j : α → ℕ} (hj : PolyT j) : ArgP fun x => args x (j x) := by
    apply argsCases 6 (F:=args) hj
    · intro l hl; interval_cases l
      · exact wp3 (pubP hK) Xp Yp
      · exact wp3 (pubP hK) (G 0) (pubP hK)
      · exact wp3 (G 1) Yp (pubP hK)
      · exact wp3 (pubP hK) Xp (pubP hK)
      · exact wp3 (G 3) Xp (pubP hK)
      · exact wp3 (G 4) Xp (pubP hK)
      · exact wp3 (PP 0) Xp (PP 1)
    · intro x l hl; obtain ⟨k,rfl⟩ : ∃ k, l=k+6 := ⟨_,(Nat.sub_add_cancel hl).symm⟩; rfl
  unfold slotN; dsimp only
  refine catP (rowP (PolyT.const 1) (PolyT.const 1) (fun _ _ => hK)) (catP (catP (pboundP hK hd ht) (cpP (PolyT.const 7) (fun h => gboundP hK hd (HR h))))
    (catP ?_ (catP (cpP (PolyT.const 7) (fun h => hashP hK hd he (HR h) (PolyT.add (HR (PolyT.const 7)) (PolyT.mul h (auxP hd))) (HA h).1 (HA h).2.1 (HA h).2.2))
      (catP (eqP hd (G 2) (G 5)) (colP (PolyT.add hd (PolyT.const 1)) (G 6) (wordP hK hd D) (pubP hK) (fun hj => PolyT.add (PolyT.add D hd) hj))))))
  apply rowP (PolyT.const 1) (PolyT.const 2); intro i j hi hj; apply regP; exact PolyT.ite' (PolyT.decide_eq hj (PolyT.const 0)) HY ht
private theorem busOffP {d e w i j : α → ℕ} (hd : PolyT d) (he : PolyT e) (hw : PolyT w) (hi : PolyT i) (hj : PolyT j) : PolyT fun x => busOff (d x) (e x) (w x) (i x) (j x) :=
  PolyT.add (PolyT.add (PolyT.add (PolyT.add (PolyT.mul hi (slotSizeP hd he hw)) (bankP hd he)) hd) (PolyT.add hd (PolyT.const 1))) (PolyT.mul hj hw)
private theorem busP {K d e w T i : α → ℕ} (hK : PolyT K) (hd : PolyT d) (he : PolyT e) (hw : PolyT w) (hi : PolyT i) :
    Eff fun x => busN (K x) (d x) (e x) (w x) (T x) (i x) := by
  let t := PolyT.mul hi (slotSizeP hd he hw)
  have B (j : ℕ) : WordP fun x => word (K x) (busOff (d x) (e x) (w x) (i x) j) (w x) := wordP hK hw (busOffP hd he hw hi (PolyT.const j))
  unfold busN; dsimp only
  refine catP (rowP hw (PolyT.const 2) ?_) (colP hw (wordP hK hd (PolyT.add (PolyT.add t (ptP hd)) (PolyT.mul (PolyT.const 6) (runP hd he)))) (B 0) (B 1) (B 2))
  intro j l hj hl; simp only [apply_ite Prod.fst]; exact PolyT.ite' (PolyT.decide_eq hl (PolyT.const 0)) (PolyT.add (PolyT.add t (PolyT.const 1)) (trP hd)) (B 0 hj)

private theorem itePoint {C : α → Prop} [DecidablePred C] {a b : α → XYZ} (hc : PolyT fun x => decide (C x)) (ha : PointP a) (hb : PointP b) : PointP fun x => if C x then a x else b x := by
  refine ⟨?_,fun hi => ?_,fun hi => ?_⟩
  · apply (PolyT.ite' hc ha.1 hb.1).congr; intro x; split <;> simp_all
  · apply (PolyT.ite' hc (ha.2.1 hi) (hb.2.1 hi)).congr; intro x; split <;> simp_all
  · apply (PolyT.ite' hc (ha.2.2 hi) (hb.2.2 hi)).congr; intro x; split <;> simp_all
private theorem condP {C : α → Prop} [DecidablePred C] {a b : α → N} (hc : PolyT fun x => decide (C x)) (ha : Eff a) (hb : Eff b) : Eff fun x => if C x then a x else b x := by
  refine ⟨?_,?_,fun hi => ?_,fun hi => ?_⟩
  · apply (PolyT.ite' hc ha.g hb.g).congr; intro x; split <;> simp_all
  · apply (PolyT.ite' hc ha.e hb.e).congr; intro x; split <;> simp_all
  · apply (PolyT.ite' hc (ha.o hi) (hb.o hi)).congr; intro x; split <;> simp_all
  · apply (PolyT.ite' hc (ha.s hi) (hb.s hi)).congr; intro x; split <;> simp_all
private theorem mapSizeP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => mapSize (d x) (e x) := PolyT.add (ptP hd) (PolyT.mul (PolyT.const 4) (sizeP hd he))
private theorem addSizeP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => addSize (d x) (e x) := PolyT.add (PolyT.add (PolyT.add (ptP hd) (PolyT.mul (PolyT.const 2) (PolyT.add (PolyT.const 1) (trP hd)))) hd) (PolyT.mul (PolyT.const 15) (sizeP hd he))
private theorem netP {cs seed point : α → List ℕ} {pre : α → W} {m k T : α → ℕ}
    (hcs : PolyT cs) (hs : PolyT seed) (hp : PolyT pre) (hm : PolyT m) (hk : PolyT k) :
    Eff fun x => net (cs x) (seed x) (point x) (pre x) (m x) (k x) (T x) := by
  let p := fun x => (cs x).getD 0 0
  let d := fun x => bitLen (p x)+1
  let e := fun x => wires (d x)
  let w := fun x => max (d x) (k x)
  let t := fun x i => i*slotSize (d x) (e x) (w x)
  let ch := fun x s => t x (4*m x)+s*chainSize (d x) (e x) (m x)
  let K := fun x => ch x 2+pt (d x)
  have D : PolyT d := PolyT.add (w4_M5Evaluator.clog2_poly (PolyT.getD hcs (PolyT.const 0) (PolyT.const 0))) (PolyT.const 1)
  have E : PolyT e := wiresP D; have Wd : PolyT w := maxP D hk
  have Tt {j : α → ℕ} (h : PolyT j) : PolyT fun x => t x (j x) := PolyT.mul h (slotSizeP D E Wd)
  let h2 := PolyT.mul (PolyT.const 2) hm; let h4 := PolyT.mul (PolyT.const 4) hm; let h1 := PolyT.add h2 (PolyT.const 1)
  have Ch (s : ℕ) : PolyT fun x => ch x s := PolyT.add (Tt h4) (PolyT.mul (PolyT.const s) (PolyT.add (PolyT.mul h1 (mapSizeP D E)) (PolyT.mul h2 (addSizeP D E))))
  have H : PolyT K := PolyT.add (Ch 2) (ptP D)
  let factor := fun (x : α) (i : ℕ) => (pin (K x) false,(ptw (K x) (d x) (t x i)).2)
  have Fact {i : α → ℕ} (h : PolyT i) : PointP fun x => factor x (i x) := ⟨H,(ptwP H D (Tt h)).2⟩
  let mp := fun x s i => ch x s+i*mapSize (d x) (e x)
  let ad := fun x s i => mp x s (2*m x+1)+i*addSize (d x) (e x)
  let acc := fun x s i => if i=0 then mp x s 0 else ad x s (i-1)
  have Mp (s : ℕ) {i : α → ℕ} (h : PolyT i) : PolyT fun x => mp x s (i x) := PolyT.add (Ch s) (PolyT.mul h (mapSizeP D E))
  have Ad (s : ℕ) {i : α → ℕ} (h : PolyT i) : PolyT fun x => ad x s (i x) := PolyT.add (Mp s h1) (PolyT.mul h (addSizeP D E))
  have Ac (s : ℕ) {i : α → ℕ} (h : PolyT i) : PolyT fun x => acc x s (i x) := PolyT.ite' (PolyT.decide_eq h (PolyT.const 0)) (Mp s (PolyT.const 0)) (Ad s (PolyT.sub h (PolyT.const 1)))
  let init := fun (x : α) (s : ℕ) => if s=1 then (pin (K x) true,pub (K x) 0,pub (K x) 0) else (pin (K x) (decide ((point x).getD 0 0=1)),pub (K x) ((point x).getD 1 0),pub (K x) ((point x).getD 2 0))
  have Init (s : ℕ) : PointP fun x => init x s := by
    by_cases hh : s=1 <;> simp only [init,hh,reduceIte] <;> exact ⟨H,pubP H,pubP H⟩
  let c4 := fun x => 1296*(cs x).getD 4 0 % p x
  let chain := fun x s => cat (copies (2*m x+1) fun i => mapN (K x) (p x) (d x) (e x) (mp x s i) (if i=0 then init x s else factor x (2*(i-1)+s)))
    (cat (copies (2*m x) fun i => addN (K x) (p x) (d x) (e x) (ad x s i) (c4 x) (ptw (K x) (d x) (acc x s i)) (ptw (K x) (d x) (mp x s (i+1))))
      (eqs (pt (d x)) (word (K x) (acc x s (2*m x)) (pt (d x))) (word (K x) (ch x 2) (pt (d x)))))
  have Chain (s : ℕ) : Eff fun x => chain x s := by
    refine catP (cpP h1 (fun {i} h => mapP H D E (Mp s h) ?_)) (catP (cpP h2 (fun h => addNP H D E (Ad s h) (ptwP H D (Ac s h)) (ptwP H D (Mp s (PolyT.add h (PolyT.const 1)))))) (eqP (ptP D) (wordP H (ptP D) (Ac s h2)) (wordP H (ptP D) (Ch 2))))
    exact itePoint (PolyT.decide_eq h (PolyT.const 0)) (Init s) (Fact (PolyT.add (PolyT.mul (PolyT.const 2) (PolyT.sub h (PolyT.const 1))) (PolyT.const s)))
  let b := PolyT.sub D (PolyT.const 1); let three := PolyT.mul (PolyT.const 3) b
  unfold net; dsimp only
  refine catP (rowP (PolyT.add H (PolyT.const 1)) (PolyT.const 1) (fun hi _ => hi))
    (catP (cpP h4 (fun hi => slotP H D E (Tt hi) hs (PolyT.div hi (PolyT.const 4)))) (catP (Chain 0) (catP (Chain 1) (catP (cpP h4 (fun hi => busP H D E Wd hi)) ?_))))
  refine condP (PolyT.decide_le (PolyT.length hp) (PolyT.mul h4 three)) (rowP (PolyT.length hp) (PolyT.const 1) ?_) (rowP (PolyT.const 1) (PolyT.const 1) (fun _ _ => H))
  intro j l hj hl
  let s := PolyT.div hj (PolyT.mul h2 three); let i := PolyT.mod (PolyT.div hj three) h2
  let h := PolyT.mod (PolyT.div hj b) (PolyT.const 3); let ff := Fact (PolyT.add (PolyT.mul (PolyT.const 2) i) s)
  simp only [apply_ite Prod.fst]
  exact PolyT.ite' (PolyT.decide_eq h (PolyT.const 0)) H (PolyT.ite' (PolyT.decide_eq h (PolyT.const 1)) (ff.2.1 (PolyT.mod hj b)) (ff.2.2 (PolyT.mod hj b)))

open w4_MulParams w4_M5GraphBounds
private theorem lenU {β : Type} [Enc β] {F : α → List β} (h : PolyT F) : Unary fun x => (F x).length :=
  (PolyT.unary_min_length (PolyT.length h) h).congr fun x => by simp
private theorem domU {a b : α → ℕ} (ha : PolyT a) (hb : Unary b) (h : ∀ x, a x ≤ b x) : Unary a :=
  (PolyT.unary_min_length ha hb).congr fun x => by simp [min_eq_left (h x)]
private theorem constU (n : ℕ) : Unary (fun _ : α => n) := PolyT.const _
private theorem wireU {d : α → ℕ} (u : Unary d) (l : ∀ x, 1 ≤ d x) : Unary fun x => wires (d x) := by
  apply domU (wiresP (asP u)) (unary_mul (constU 1100) (addU u (constU 1)))
  intro x; rw [S8H.PointAddresses.wires_eq (l x)]; exact (graph_edge_bound (l x)).le
private theorem vertU {d : α → ℕ} (u : Unary d) (l : ∀ x, 1 ≤ d x) : Unary fun x => vertexCount (d x) := by
  apply domU (w4_M5Evaluator.vertexCount_poly (asP u)) (unary_mul (constU 256) (addU u (constU 1)))
  intro x; have h := l x; have := J_lt_linear h; have := n0_upper h; have := L_le_half_J h
  have := L1_le_L (d x); have := L2_le_L (d x); change vertexCount _ ≤ 256*(d x+1); rw [vertexCount_eq h]; omega
private theorem maxU {a b : α → ℕ} (ha : Unary a) (hb : Unary b) : Unary fun x => max (a x) (b x) :=
  domU (maxP (asP ha) (asP hb)) (addU ha hb) (fun x => max_le (Nat.le_add_right ..) (Nat.le_add_left ..))
private abbrev Cost (A : α → N) := (Unary fun x => ng (A x)) ∧ (Unary fun x => ne (A x))
private theorem catU {a b : α → N} (A : Cost a) (B : Cost b) : Cost fun x => cat (a x) (b x) :=
  ⟨addU A.1 B.1,addU A.2 B.2⟩
private theorem cpU {n : α → ℕ} {f : α → ℕ → N} (hn : Unary n) (h : Cost fun x => f x 0) : Cost fun x => copies (n x) (f x) :=
  ⟨unary_mul hn h.1,unary_mul hn h.2⟩
private theorem rowU {n m : α → ℕ} {f : α → ℕ → ℕ → Bit} {q : α → ℕ → (ℕ → Bool) → Bool}
    (hn : Unary n) (hm : Unary m) : Cost fun x => rows (n x) (m x) (f x) (q x) := ⟨hn,unary_mul hn hm⟩
private theorem eqU {n : α → ℕ} {a b : α → Word} (hn : Unary n) : Cost fun x => eqs (n x) (a x) (b x) := ⟨hn,unary_mul hn (constU 2)⟩
private theorem colU {n : α → ℕ} {v : α → Bool} {a b z c : α → Word} (hn : Unary n) : Cost fun x => col (n x) (v x) (a x) (b x) (z x) (c x) := ⟨hn,unary_mul hn (constU 5)⟩
private theorem prodU {K d off : α → ℕ} {a b z : α → Word} (hd : Unary d) (hp : ∀ x, 1 ≤ d x) :
    Cost fun x => M3B.ECPolyDefs.prod (K x) (d x) (off x) (a x) (b x) (z x) := by
  unfold M3B.ECPolyDefs.prod; dsimp only; apply catU _ (eqU (unary_mul (constU 4) hd))
  exact ⟨vertU hd hp,addU (wireU hd hp) (wireU hd hp)⟩

private theorem hashU {K p d e r ax : α → ℕ} {a b z : α → Word} (hd : Unary d) (hp : ∀ x, 1 ≤ d x) :
    Cost fun x => M3B.ECPolyDefs.hash (K x) (p x) (d x) (e x) (r x) (ax x) (a x) (b x) (z x) := by
  unfold M3B.ECPolyDefs.hash; dsimp only
  exact catU (catU (prodU hd hp) (prodU hd hp)) (catU (colU (unary_mul (constU 2) hd)) (catU (colU (addU hd (constU 1))) (colU (addU hd (constU 1)))))
private theorem bndU {K p d t : α → ℕ} (hd : Unary d) : Cost fun x => bnd (K x) (p x) (d x) (t x) := ⟨addU hd (constU 1),unary_mul (addU hd (constU 1)) (constU 5)⟩
private theorem gboundU {K p d t : α → ℕ} (hd : Unary d) : Cost fun x => gbound (K x) (p x) (d x) (t x) := by unfold gbound; exact catU (bndU hd) (bndU hd)
private theorem pboundU {K p d t : α → ℕ} (hd : Unary d) : Cost fun x => pbound (K x) (p x) (d x) (t x) := by unfold pbound; exact catU (bndU hd) (bndU hd)

private theorem ghU {K p d e t : α → ℕ} {a : α → Word × Word × Word} (hd : Unary d) (hp : ∀ x, 1 ≤ d x) :
    Cost fun x => ghash (K x) (p x) (d x) (e x) (t x) (a x) := hashU hd hp
private theorem mapU {K p d e t : α → ℕ} {q : α → XYZ} (hd : Unary d) (hp : ∀ x, 1 ≤ d x) :
    Cost fun x => mapN (K x) (p x) (d x) (e x) (t x) (q x) := by
  unfold mapN; dsimp only
  exact catU (catU (pboundU hd) (cpU (constU 4) (gboundU hd)))
    (catU (cpU (constU 4) (ghU hd hp)) (catU (eqU (constU 1)) (catU (rowU hd (constU 3)) (rowU hd (constU 3)))))
private theorem addNU {K p d e t c : α → ℕ} {u v : α → XYZ} (hd : Unary d) (hp : ∀ x, 1 ≤ d x) :
    Cost fun x => addN (K x) (p x) (d x) (e x) (t x) (c x) (u x) (v x) := by
  unfold addN; dsimp only
  exact catU (catU (pboundU hd) (catU (cpU (constU 2) (bndU hd)) (cpU (constU 15) (gboundU hd))))
    (catU (cpU (constU 15) (ghU hd hp)) (catU (rowU hd (constU 5)) (catU (rowU hd (constU 5))
      (catU (rowU hd (constU 9)) (catU (rowU (constU 1) (constU 9)) (catU (rowU hd (constU 9)) (rowU hd (constU 9))))))))
private theorem slotU {K p d e w t T i : α → ℕ} {cs ss : α → List ℕ} (hd : Unary d) (hp : ∀ x, 1 ≤ d x) :
    Cost fun x => slotN (K x) (p x) (d x) (e x) (w x) (t x) (T x) (cs x) (ss x) (i x) := by
  unfold slotN; dsimp only
  exact catU (rowU (constU 1) (constU 1)) (catU (catU (pboundU hd) (cpU (constU 7) (gboundU hd)))
    (catU (rowU (constU 1) (constU 2)) (catU (cpU (constU 7) (hashU hd hp))
      (catU (eqU hd) (colU (addU hd (constU 1)))))))
private theorem busU {K d e w T i : α → ℕ} (hw : Unary w) :
    Cost fun x => busN (K x) (d x) (e x) (w x) (T x) (i x) := by
  unfold busN; dsimp only; exact catU (rowU hw (constU 2)) (colU hw)
private theorem iteU {P : α → Prop} [DecidablePred P] {f g : α → ℕ} (h : PolyT fun x => decide (P x)) (a : Unary f) (b : Unary g) :
    Unary fun x => if P x then f x else g x := by
  apply (PolyT.ite' h a b).congr; intro x; by_cases hh : P x <;> simp [hh]
private theorem condU {P : α → Prop} [DecidablePred P] {f g : α → N} (h : PolyT fun x => decide (P x)) (a : Cost f) (b : Cost g) :
    Cost fun x => if P x then f x else g x := by
  constructor
  · simpa only [apply_ite ng] using iteU h a.1 b.1
  · simpa only [apply_ite ne] using iteU h a.2 b.2

private theorem netU {cs ss point : α → List ℕ} {pr : α → W} {m k T : α → ℕ}
    (hcs : PolyT cs) (hr : PolyT pr) (hm : Unary m) (hk : Unary k) :
    Cost fun x => net (cs x) (ss x) (point x) (pr x) (m x) (k x) (T x) := by
  let p := fun x => (cs x).getD 0 0
  let d := fun x => bitLen (p x)+1
  let e := fun x => wires (d x)
  let w := fun x => max (d x) (k x)
  have hd : Unary d := addU (clogU (PolyT.getD hcs (PolyT.const 0) (PolyT.const 0))) (constU 1)
  have hpos (x) : 1 ≤ d x := Nat.succ_pos _
  have he : Unary e := wireU hd hpos
  have hw : Unary w := maxU hd hk
  have htr : Unary fun x => M3B.ECPolyDefs.triple (d x) := addU (unary_mul (constU 3) hd) (constU 1)
  have hpt : Unary fun x => pt (d x) := addU (constU 1) (unary_mul (constU 2) htr)
  have haux : Unary fun x => aux (d x) := addU (unary_mul (constU 2) hd) (unary_mul (constU 3) (addU hd (constU 1)))
  have hrun : Unary fun x => run (d x) (e x) := addU (addU (addU (unary_mul (constU 2) htr) hd) (unary_mul (constU 2) (addU (unary_mul (constU 2) hd) he))) (constU 1)
  have hg := addU hrun haux
  have hmap := addU hpt (unary_mul (constU 4) hg)
  have hadd := addU (addU (addU hpt (unary_mul (constU 2) (addU (constU 1) htr))) hd) (unary_mul (constU 15) hg)
  have h2 := unary_mul (constU 2) hm
  have hc := addU (unary_mul (addU h2 (constU 1)) hmap) (unary_mul h2 hadd)
  have hbank := addU (addU hpt (unary_mul (constU 7) hrun)) (unary_mul (constU 7) haux)
  have hs := addU (addU (addU hbank hd) (addU hd (constU 1))) (unary_mul (constU 3) hw)
  have h4 := unary_mul (constU 4) hm
  have hK := addU (addU (unary_mul h4 hs) (unary_mul (constU 2) hc)) hpt
  have hpre := lenU hr
  have ok := PolyT.decide_le (PolyT.length hr) (PolyT.mul (asP h4) (PolyT.mul (PolyT.const 3) (PolyT.sub (asP hd) (PolyT.const 1))))
  unfold net; dsimp only
  refine catU (rowU (addU hK (constU 1)) (constU 1)) (catU (cpU h4 (slotU hd hpos)) (catU ?_ (catU ?_ (catU (cpU h4 (busU hw)) ?_))))
  · exact catU (cpU (addU h2 (constU 1)) (mapU hd hpos)) (catU (cpU h2 (addNU hd hpos)) (eqU hpt))
  · exact catU (cpU (addU h2 (constU 1)) (mapU hd hpos)) (catU (cpU h2 (addNU hd hpos)) (eqU hpt))
  · exact condU ok (rowU hpre (constU 1)) (rowU (constU 1) (constU 1))

private theorem netBudgets : (Unary fun w => ng (compiled w)) ∧ (Unary fun w => ne (compiled w)) := by
  have hf : PolyT frames := parseP PolyT.id'
  let frame := fun (i : ℕ) (w : W) => (frames w).getD i []
  have F (i : ℕ) : PolyT (frame i) := PolyT.getD hf (PolyT.const i) (PolyT.const [])
  have D (i : ℕ) := decodeP (F i)
  have M : Unary fun w => (w5_M6Sort.decode (frame 3 w)).length/4 := domU (PolyT.div (PolyT.length (D 3)) (PolyT.const 4)) (lenU (D 3)) (fun _ => Nat.div_le_self ..)
  have K := clogU (PolyT.mul (PolyT.const 2) (PolyT.getD (D 2) (PolyT.const 1) (PolyT.const 0)))
  exact netU (D 0) (F 6) M K

private theorem dimBudgets : PolyT frames ∧ PolyT dimensions ∧
    (Unary fun w => (dimensions w).1) ∧ (Unary fun w => (dimensions w).2.1) ∧
    (Unary fun w => (dimensions w).2.2.1) ∧ (Unary fun w => (dimensions w).2.2.2.2.1) ∧
    (Unary fun w => (dimensions w).2.2.2.2.2) := by
  let fs := frames
  let ns := fun (j : ℕ) (w : W) => w5_M6Sort.decode ((fs w).getD j [])
  let num := fun (j i : ℕ) (w : W) => (ns j w).getD i 0
  let m := fun w => (ns 3 w).length/4
  let k := fun w => Nat.clog 2 (2*num 2 1 w)
  have F : PolyT fs := parseP PolyT.id'
  have N (j : ℕ) : PolyT (ns j) := decodeP (PolyT.getD F (PolyT.const j) (PolyT.const []))
  have V (j i : ℕ) : PolyT (num j i) := PolyT.getD (N j) (PolyT.const i) (PolyT.const 0)
  have M : Unary m := by
    apply (PolyT.unary_min_length (PolyT.div (PolyT.length (N 3)) (PolyT.const 4)) (N 3)).congr
    intro x; dsimp only; rw [min_eq_left (Nat.div_le_self ..)]
  have B := clogU (V 0 0)
  have K : Unary k := clogU (PolyT.mul (PolyT.const 2) (V 2 1))
  have C (c : ℕ) : Unary (fun _ : W => c) := PolyT.const _
  have L := addU (unary_mul (C 8) M) (C 3)
  have P := addU (addU (C 2) (unary_mul (unary_mul (C 4) M) K)) (unary_mul (addU (unary_mul (C 8) M) (C 2))
    (clogU (PolyT.add (PolyT.mul (asP (unary_mul (C 4) M)) (V 2 0)) (PolyT.const 2))))
  exact ⟨F,PolyT.prodMk (asP B) (PolyT.prodMk (asP M) (PolyT.prodMk (asP K)
    (PolyT.prodMk (V 2 1) (PolyT.prodMk (asP P) (asP L))))),B,M,K,P,L⟩

private theorem compP {f : α → W} (hf : PolyT f) : Eff fun x => compiled (f x) := by
  let frame := fun i (x : α) => (frames (f x)).getD i []
  have F (i : ℕ) : PolyT (frame i) := PolyT.getD (parseP hf) (PolyT.const i) (PolyT.const [])
  have D (i : ℕ) := decodeP (F i)
  exact netP (D 0) (D 3) (F 6) (PolyT.div (PolyT.length (D 3)) (PolyT.const 4)) (w4_M5Evaluator.clog2_poly (PolyT.mul (PolyT.const 2) (PolyT.getD (D 2) (PolyT.const 1) (PolyT.const 0))))
private theorem succP {f : α → W} {i : α → ℕ} (hf : PolyT f) (hi : PolyT i) : PolyT fun x => succWire (compiled (f x)) (i x) := by
  let A := fun x => compiled (f x)
  have u : Unary fun x => ne (A x) := PolyT.comp (f:=fun w => List.replicate (ne (compiled w)) ()) netBudgets.2 hf
  have s := (compP hf).s hi
  have ext : PolyT fun z : α × ℕ => signal (A z.1) z.2 := (compP (PolyT.comp hf (PolyT.fst PolyT.id'))).s (PolyT.snd PolyT.id')
  have hL := PolyT.filter (f:=fun x j => decide (signal (A x) j=signal (A x) (i x))) (PolyT.decide_eq ext (PolyT.comp s (PolyT.fst PolyT.id'))) (PolyT.range u)
  exact PolyT.getD hL (PolyT.mod (PolyT.add (PolyT.idxOf hi hL) (PolyT.const 1)) (PolyT.length hL)) hi

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
set_option maxHeartbeats 800000 in
theorem solution : PolyT ecBuild := by
  obtain ⟨_,dims,bU,mU,kU,pU,lU⟩ := dimBudgets
  obtain ⟨gU,nU⟩ := netBudgets
  let b := fun w : W => (dimensions w).1; let m := fun w : W => (dimensions w).2.1; let k := fun w : W => (dimensions w).2.2.1
  let g := fun w => ng (compiled w); let n := fun w => ne (compiled w)
  let lu := fun w => g w+n w; let nG := fun w => lu w+4*m w; let nV := fun w => nG w+n w
  let nE := fun w => 3*n w+4*m w*k w
  let src := fun w i => if i<n w then gate (compiled w) i else if i<3*n w then g w+(i-n w)%n w else lu w+(i-3*n w)/k w
  let dst := fun w i => nG w+(if i<n w then i else if i<2*n w then i-n w else if i<3*n w then succWire (compiled w) (i-2*n w) else
    busOff (b w+1) (wires (b w+1)) (max (b w+1) (k w)) ((i-3*n w)/k w) 1+(i-3*n w)%k w)
  have Ulu : Unary lu := addU gU nU; have Ug : Unary nG := addU Ulu (unary_mul (constU 4) mU)
  have V : Unary nV := addU Ug nU; have E : Unary nE := addU (unary_mul (constU 3) nU) (unary_mul (unary_mul (constU 4) mU) kU)
  let proj : W × ℕ → W := Prod.fst
  have hproj : PolyT proj := PolyT.fst PolyT.id'; have i : PolyT (Prod.snd (α:=W) (β:=ℕ)) := PolyT.snd PolyT.id'
  have G : PolyT fun x => g (proj x) := PolyT.comp (asP gU) hproj; have Np : PolyT fun x => n (proj x) := PolyT.comp (asP nU) hproj
  have K : PolyT fun x => k (proj x) := PolyT.comp (asP kU) hproj; have B : PolyT fun x => b (proj x)+1 := PolyT.add (PolyT.comp (asP bU) hproj) (PolyT.const 1)
  let th := PolyT.mul (PolyT.const 3) Np; let tw := PolyT.mul (PolyT.const 2) Np; let sub := PolyT.sub i th
  let cl := PolyT.decide_lt i Np; let c3 := PolyT.decide_lt i th
  have S : PolyT fun z : W × ℕ => src z.1 z.2 := PolyT.ite' cl ((compP hproj).o i) (PolyT.ite' c3 (PolyT.add G (PolyT.mod (PolyT.sub i Np) Np)) (PolyT.add (PolyT.add G Np) (PolyT.div sub K)))
  have D : PolyT fun z : W × ℕ => dst z.1 z.2 := PolyT.add (PolyT.comp (asP Ug) hproj) (PolyT.ite' cl i (PolyT.ite' (PolyT.decide_lt i tw) (PolyT.sub i Np) (PolyT.ite' c3 (succP hproj (PolyT.sub i tw)) (PolyT.add (busOffP B (wiresP B) (maxP B K) (PolyT.div sub K) (PolyT.const 1)) (PolyT.mod sub K)))))
  have Packet := S8H.WirePacket.packet_poly (nv:=nV) (ne:=nE) (src:=src) (dst:=dst) (asP V) (asP E) (addU V E) (addU E E) S D
  have Mask := PolyT.map (f:=fun w j => decide (lu w ≤ j ∧ j<nG w)) (by
    exact PolyT.decide_and (PolyT.decide_le (PolyT.comp (asP Ulu) hproj) i) (PolyT.decide_lt i (PolyT.comp (asP Ug) hproj))) (PolyT.range (addU V E))
  have code {f : W → ℕ} (h : PolyT f) := w5_M6Sort.cw_poly h
  let size := PolyT.mul (PolyT.mul (PolyT.const 100000000) (asP mU)) (asP bU)
  have cons {a b : W → W} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => true :: ((Encoding.frame (a x)) ++ b x) :=
    P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const _) (PolyT.append ((DetDLP_W1_Queries.frame_poly ha).congr fun x => DetDLP_W1_Queries.frame_correct _) hb)
  exact cons PolyT.id' (cons Packet (cons (code (asP bU)) (cons (code (asP mU)) (cons (code (asP kU)) (cons (code size) (cons (code (asP pU)) (cons (code (asP lU)) (cons Mask (PolyT.const [false])))))))))
