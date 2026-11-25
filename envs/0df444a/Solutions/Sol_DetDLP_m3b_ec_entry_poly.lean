-- Prove2me | solution 1 for DetDLP.m3b_ec_entry_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T23:57:03.327335+00:00
-- url     : https://prove2.me/submissions/ec1c9bb3-6468-4eb3-9d9a-5411e09c0a75

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
open w4_MulParams w4_M5GraphBounds
private theorem lenU {β : Type} [Enc β] {F : α → List β} (h : PolyT F) : Unary fun x => (F x).length :=
  (PolyT.unary_min_length (PolyT.length h) h).congr fun x => by simp
private theorem domU {a b : α → ℕ} (ha : PolyT a) (hb : Unary b) (h : ∀ x, a x ≤ b x) : Unary a :=
  (PolyT.unary_min_length ha hb).congr fun x => by simp [min_eq_left (h x)]
private theorem constU (n : ℕ) : Unary (fun _ : α => n) := PolyT.const _
private theorem wireU {d : α → ℕ} (u : Unary d) (l : ∀ x, 1 ≤ d x) : Unary fun x => wires (d x) := by
  apply domU (wiresP (asP u)) (unary_mul (constU 1100) (addU u (constU 1)))
  intro x; rw [S8H.PointAddresses.wires_eq (l x)]; exact (graph_edge_bound (l x)).le
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


private structure Eval (a : α → N) : Prop where
  g : PolyT fun x => ng (a x)
  c : ∀ {i : α → ℕ} {l : α → W}, PolyT i → PolyT l → PolyT fun x => check (a x) (i x) (l x)
private theorem catC {a b : α → N} (A : Eval a) (B : Eval b) : Eval fun x => cat (a x) (b x) :=
  ⟨PolyT.add A.g B.g,fun {i} {l} hi hl => (PolyT.ite' (PolyT.decide_lt hi A.g) (A.c hi hl) (B.c (PolyT.sub hi A.g) hl)).congr fun x => by
    change (if i x < ng (a x) then _ else _) = (if i x < ng (a x) then check (a x) (i x) else check (b x) (i x-ng (a x))) (l x)
    by_cases h : i x < ng (a x) <;> simp only [h,reduceIte]⟩
private theorem cpC {n : α → ℕ} {F : α → ℕ → N} (hn : PolyT n) (h : ∀ {i : α → ℕ}, PolyT i → Eval (fun x => F x (i x))) : Eval fun x => copies (n x) (F x) := by
  have g := (h (PolyT.const 0)).g; exact ⟨PolyT.mul hn g,fun hi hl => (h (PolyT.div hi g)).c (PolyT.mod hi g) hl⟩
private abbrev BW (r : α → Word) := ∀ {j : α → ℕ}, PolyT j → PolyT fun x => (r x (j x)).2
private abbrev BP (r : α → XYZ) := (PolyT fun x => (r x).1.2) ∧ BW (fun x => (r x).2.1) ∧ BW (fun x => (r x).2.2)
private abbrev BA (r : α → Word × Word × Word) := BW (fun x => (r x).1) ∧ BW (fun x => (r x).2.1) ∧ BW (fun x => (r x).2.2)
private theorem pubC {K n : α → ℕ} (h : PolyT n) : BW fun x => pub (K x) (n x) := fun hj => PolyT.prodMk (PolyT.testBit h hj) (PolyT.testBit h hj)
private theorem wordC {K t n : α → ℕ} (h : PolyT n) : BW fun x => word (K x) (t x) (n x) := by
  intro j hj; simp only [word,apply_ite Prod.snd]; exact PolyT.ite' (PolyT.decide_lt hj h) (PolyT.const (false,true)) (PolyT.const (false,false))
private theorem regC {r : α → ℕ} : PolyT fun x => (reg (r x)).2 := PolyT.const _
private theorem pinC {K : α → ℕ} {v : α → Bool} (h : PolyT v) : PolyT fun x => (pin (K x) (v x)).2 := PolyT.prodMk h h
private theorem ptwC {K d t : α → ℕ} (h : PolyT d) : BP fun x => ptw (K x) (d x) (t x) := ⟨regC,wordC h,wordC h⟩
private theorem rdC {r : α → Bit} {v : α → Bool} (h : PolyT fun x => (r x).2) (hv : PolyT v) : PolyT fun x => rd (r x) (v x) := PolyT.ite' (PolyT.decide_eq_true hv) (PolyT.snd h) (PolyT.fst h)
private abbrev Values (v : α → ℕ → Bool) := ∀ (j : ℕ), PolyT fun x => v x j
private theorem rowC {n m : α → ℕ} {r : α → ℕ → ℕ → Bit} {t : α → ℕ → (ℕ → Bool) → Bool} (hn : PolyT n)
    (hr : ∀ {i : α → ℕ}, PolyT i → ∀ j, PolyT fun x => (r x (i x) j).2)
    (ht : ∀ {i : α → ℕ} {v : α → ℕ → Bool}, PolyT i → Values v → PolyT fun x => t x (i x) (v x)) : Eval fun x => rows (n x) (m x) (r x) (t x) := by
  refine ⟨hn,fun {i} {l} hi hl => ?_⟩; exact ht hi (fun j => rdC (hr hi j) (PolyT.getD hl (PolyT.const j) (PolyT.const false)))
private theorem eqC {n : α → ℕ} {a b : α → Word} (hn : PolyT n) (ha : BW a) (hb : BW b) : Eval fun x => eqs (n x) (a x) (b x) := by
  unfold eqs; apply rowC hn
  · intro i hi j; by_cases h : j=0 <;> simp only [h,reduceIte]; exact ha hi; exact hb hi
  · intro i v hi hv; exact PolyT.beq' (hv 0) (hv 1)
private theorem colC {n : α → ℕ} {v : α → Bool} {a b z c : α → Word} (hn : PolyT n) (hv : PolyT v) (ha : BW a) (hb : BW b) (hz : BW z) (hc : BW c) : Eval fun x => col (n x) (v x) (a x) (b x) (z x) (c x) := by
  unfold col; dsimp only; apply rowC hn
  · intro i hi j; rcases j with _|_|_|_|j; exact ha hi; exact hb hi; exact hz hi; exact hc hi
    exact hc (PolyT.ite' (PolyT.decide_eq hi (PolyT.const 0)) (PolyT.sub hn (PolyT.const 1)) (PolyT.sub hi (PolyT.const 1)))
  · intro i f hi h; let carry := PolyT.ite' (PolyT.decide_eq hi (PolyT.const 0)) hv (h 4)
    apply PolyT.decide_and (PolyT.decide_eq (PolyT.add (PolyT.add (PolyT.toNat' (h 0)) (PolyT.toNat' (h 1))) (PolyT.toNat' carry)) (PolyT.add (PolyT.toNat' (h 2)) (PolyT.mul (PolyT.const 2) (PolyT.toNat' (h 3)))))
    apply (PolyT.or' (PolyT.decide_ne (PolyT.add hi (PolyT.const 1)) hn) (PolyT.decide_eq_false (h 3))).congr; intro x; simp [imp_iff_not_or]

private theorem mulC {d i : α → ℕ} {l : α → W} (hd : Unary d) (pos : ∀ x, 1 ≤ d x) (hi : PolyT i) (hl : PolyT l) :
    PolyT fun x => let ps := (List.range (wires (d x))).filter fun j => decide (w4_M5EdgeNat.srcNat (d x) j=i x ∨ w4_M5EdgeNat.dstNat (d x) j=i x)
                   let ls := ps.filter fun j => decide (w4_M5EdgeNat.srcNat (d x) j=i x)
                   let rs := ps.filter fun j => decide (w4_M5EdgeNat.srcNat (d x) j≠i x)
                   w4_M5Dispatch.evalNat (List.replicate (d x) ()) (i x) (ps.map fun j => (l x).getD ((ls++rs).idxOf j) false) := by
  let F := PolyT.fst (PolyT.id' (α:=α × ℕ)); let J := PolyT.snd (PolyT.id' (α:=α × ℕ))
  have D := PolyT.comp (asP hd) F; have I := PolyT.comp hi F
  have src := w4_M5EdgeNat.srcNat_poly D J; have dst := w4_M5EdgeNat.dstNat_poly D J
  have L := PolyT.decide_eq src I; have R := PolyT.decide_eq dst I
  have ps := PolyT.filter (f:=fun x j => decide (w4_M5EdgeNat.srcNat (d x) j=i x ∨ w4_M5EdgeNat.dstNat (d x) j=i x)) (PolyT.decide_or L R) (PolyT.range (wireU hd pos))
  have ls := PolyT.filter (f:=fun x j => decide (w4_M5EdgeNat.srcNat (d x) j=i x)) L ps
  have rs := PolyT.filter (f:=fun x j => decide (w4_M5EdgeNat.srcNat (d x) j≠i x)) (PolyT.decide_ne src I) ps
  exact w4_M5Dispatch.evalNat_poly hd hi (PolyT.map (PolyT.getD (PolyT.comp hl F) (PolyT.idxOf J (PolyT.comp (PolyT.append ls rs) F)) (PolyT.const false)) ps)
private theorem prodC {K d t : α → ℕ} {a b z : α → Word} (hd : Unary d) (pos : ∀ x, 1 ≤ d x) (ha : BW a) (hb : BW b) (hz : BW z) : Eval fun x => M3B.ECPolyDefs.prod (K x) (d x) (t x) (a x) (b x) (z x) := by
  unfold M3B.ECPolyDefs.prod; dsimp only; apply catC
  · exact ⟨w4_M5Evaluator.vertexCount_poly (asP hd),fun hi hl => mulC hd pos hi hl⟩
  · let D := asP hd; let two := PolyT.mul (PolyT.const 2) D
    apply eqC (PolyT.mul (PolyT.const 4) D)
    · intro _ _; exact PolyT.const (false,true)
    · intro i hi; simp only [apply_ite Prod.snd]
      exact PolyT.ite' (PolyT.decide_lt hi D) (ha hi) (PolyT.ite' (PolyT.decide_lt hi two) (hb (PolyT.sub hi D)) (hz (PolyT.sub hi two)))
private theorem bndC {K p d t : α → ℕ} (hp : PolyT p) (hd : PolyT d) : Eval fun x => bnd (K x) (p x) (d x) (t x) := by
  unfold bnd; exact colC (PolyT.add hd (PolyT.const 1)) (PolyT.const true) (wordC hd) (wordC hd) (pubC hp) (fun _ => regC)
private theorem pboundC {K p d t : α → ℕ} (hp : PolyT p) (hd : PolyT d) : Eval fun x => pbound (K x) (p x) (d x) (t x) := by unfold pbound; exact catC (bndC hp hd) (bndC hp hd)
private theorem gboundC {K p d t : α → ℕ} (hp : PolyT p) (hd : PolyT d) : Eval fun x => gbound (K x) (p x) (d x) (t x) := by unfold gbound; exact catC (bndC hp hd) (bndC hp hd)
private theorem hashC {K p d e r ax : α → ℕ} {a b z : α → Word} (hp : PolyT p) (hd : Unary d) (pos : ∀ x, 1 ≤ d x) (ha : BW a) (hb : BW b) (hz : BW z) : Eval fun x => M3B.ECPolyDefs.hash (K x) (p x) (d x) (e x) (r x) (ax x) (a x) (b x) (z x) := by
  let D := asP hd; let two := PolyT.mul (PolyT.const 2) D; let one := PolyT.add D (PolyT.const 1)
  unfold M3B.ECPolyDefs.hash; dsimp only
  exact catC (catC (prodC hd pos ha hb (wordC two)) (prodC hd pos (wordC D) (pubC hp) (wordC two)))
    (catC (colC two (PolyT.const false) (wordC two) (wordC D) (wordC two) (fun _ => regC))
      (catC (colC one (PolyT.const false) (wordC D) hz (wordC one) (fun _ => regC)) (colC one (PolyT.const false) (wordC D) (fun hj => PolyT.prodMk (PolyT.const false) (PolyT.testBit hp hj)) (wordC one) (fun _ => regC))))
private theorem ghC {K p d e t : α → ℕ} {args : α → Word × Word × Word} (hp : PolyT p) (hd : Unary d) (pos : ∀ x, 1 ≤ d x) (h : BA args) : Eval fun x => ghash (K x) (p x) (d x) (e x) (t x) (args x) := hashC hp hd pos h.1 h.2.1 h.2.2

private theorem argsCases (n : ℕ) {F : α → ℕ → Word × Word × Word} {i : α → ℕ} (hi : PolyT i)
    (atJ : ∀ j ≤ n, BA fun x => F x j) (last : ∀ x j, n ≤ j → F x j = F x n) : BA fun x => F x (i x) := by
  refine ⟨fun {b} hb => ?_,fun {b} hb => ?_,fun {b} hb => ?_⟩
  · apply boundedCases n (f:=fun x j => ((F x j).1 (b x)).2) hi
    · exact fun j hj => (atJ j hj).1 hb
    · intro x j hj; rw [last x j hj]
  · apply boundedCases n (f:=fun x j => ((F x j).2.1 (b x)).2) hi
    · exact fun j hj => (atJ j hj).2.1 hb
    · intro x j hj; rw [last x j hj]
  · apply boundedCases n (f:=fun x j => ((F x j).2.2 (b x)).2) hi
    · exact fun j hj => (atJ j hj).2.2 hb
    · intro x j hj; rw [last x j hj]
private theorem wp3 {f a b : α → Word} (hf : BW f) (ha : BW a) (hb : BW b) : BA fun x => (f x,a x,b x) := ⟨hf,ha,hb⟩


private theorem cmpC {n : α → ℕ} {r : α → Bit} {a b : α → Word} (hn : PolyT n) (hr : PolyT fun x => (r x).2) (ha : BW a) (hb : BW b) :
    Eval fun x => rows (n x) 3 (fun i j => match j with | 0 => r x | 1 => a x i | _ => b x i) (fun _ v => v 1 == (!v 0 && v 2)) := by
  apply rowC hn
  · intro i hi l; rcases l with _|_|l; exact hr; exact ha hi; exact hb hi
  · intro i v hi h; exact PolyT.beq' (h 1) (PolyT.and' (PolyT.not' (h 0)) (h 2))
private theorem mapC {K p d e t : α → ℕ} {q : α → XYZ}
    (hp : PolyT p) (hd : Unary d) (pos : ∀ x, 1 ≤ d x) (hq : BP q) :
    Eval fun x => mapN (K x) (p x) (d x) (e x) (t x) (q x) := by
  let go := fun (x : α) (j : ℕ) => t x + pt (d x) + j * gsize (d x) (e x)
  have R (j : ℕ) : BW (fun x => word (K x) (go x j) (d x)) := wordC (asP hd)
  have O := ptwC (K:=K) (t:=t) (asP hd)
  unfold mapN; dsimp only
  refine catC (catC (pboundC hp (asP hd)) (cpC (PolyT.const 4) (fun _ => gboundC hp (asP hd))))
    (catC (cpC (PolyT.const 4) (fun {j} hj => ghC hp hd pos ?_))
    (catC (eqC (PolyT.const 1) (fun _ => regC) (fun _ => hq.1)) (catC ?_ ?_)))
  · apply argsCases 3 (F:=fun x l => match l with
      | 0 => (pub (K x) (36%p x),(q x).2.1,pub (K x) 0)
      | 1 => (pub (K x) 0,(q x).2.1,pub (K x) 0)
      | 2 => (pub (K x) (2%p x),(q x).2.2,word (K x) (go x 1) (d x))
      | _ => (pub (K x) (108%p x),word (K x) (go x 2) (d x),pub (K x) 0)) hj
    · intro l hl; interval_cases l
      · exact wp3 (pubC (PolyT.mod (PolyT.const 36) hp)) hq.2.1 (pubC (PolyT.const 0))
      · exact wp3 (pubC (PolyT.const 0)) hq.2.1 (pubC (PolyT.const 0))
      · exact wp3 (pubC (PolyT.mod (PolyT.const 2) hp)) hq.2.2 (R 1)
      · exact wp3 (pubC (PolyT.mod (PolyT.const 108) hp)) (R 2) (pubC (PolyT.const 0))
    · intro x l hl; obtain ⟨j,rfl⟩ : ∃ j, l=j+3 := ⟨l-3,by omega⟩; rfl
  · exact cmpC (asP hd) hq.1 O.2.1 (R 0)
  · exact cmpC (asP hd) hq.1 O.2.2 (R 3)

private theorem row5C {n : α → ℕ}  {f0 : α → Bit} {w0 w1 w2 w3 : α → Word}
    (hn : PolyT n) (F0 : PolyT fun x => (f0 x).2)
    (W0 : BW w0) (W1 : BW w1) (W2 : BW w2) (W3 : BW w3) :
    Eval fun x => rows (n x) 5 (fun k j => match j with | 0 => f0 x | 1 => w0 x k | 2 => w1 x k | 3 => w2 x k | _ => w3 x k) (fun _ v => if v 0 then !v 1 && !v 2 else v 3 == v 4) := by
  apply rowC hn
  · intro i hi j; rcases j with _|_|_|_|j
    · exact F0
    · exact W0 hi
    · exact W1 hi
    · exact W2 hi
    · exact W3 hi
  · intro i v hi h; exact PolyT.ite' (PolyT.decide_eq_true (h 0)) (PolyT.and' (PolyT.not' (h 1)) (PolyT.not' (h 2))) (PolyT.beq' (h 3) (h 4))

private theorem row9C {n : α → ℕ} (slope : Bool) {f0 f1 f2 f3 : α → Bit} {w0 w1 w2 w3 w4 : α → Word}
    (hn : PolyT n) (F0 : PolyT fun x => (f0 x).2) (F1 : PolyT fun x => (f1 x).2) (F2 : PolyT fun x => (f2 x).2) (F3 : PolyT fun x => (f3 x).2)
    (W0 : BW w0) (W1 : BW w1) (W2 : BW w2) (W3 : BW w3) (W4 : BW w4) :
    Eval fun x => rows (n x) 9 (fun k j => match j with | 0 => f0 x | 1 => f1 x | 2 => f2 x | 3 => f3 x | 4 => w0 x k | 5 => w1 x k | 6 => w2 x k | 7 => w3 x k | _ => w4 x k) (fun _ v => v 4 == (if slope then (if !v 0 && !v 1 && !v 2 then v 5 else if !v 0 && !v 1 && v 2 && !v 3 then v 6 else v 7) else if v 0 then v 5 else if v 1 then v 6 else if v 2 && v 3 then v 7 else v 8)) := by
  apply rowC hn
  · intro i hi j; rcases j with _|_|_|_|_|_|_|_|j
    · exact F0
    · exact F1
    · exact F2
    · exact F3
    · exact W0 hi
    · exact W1 hi
    · exact W2 hi
    · exact W3 hi
    · exact W4 hi
  · intro i v hi h; apply PolyT.beq' (h 4); cases slope <;> simp only [Bool.false_eq_true,reduceIte]
    · exact PolyT.ite' (PolyT.decide_eq_true (h 0)) (h 5) (PolyT.ite' (PolyT.decide_eq_true (h 1)) (h 6) (PolyT.ite' (PolyT.decide_eq_true (PolyT.and' (h 2) (h 3))) (h 7) (h 8)))
    · let f := PolyT.and' (PolyT.not' (h 0)) (PolyT.not' (h 1))
      exact PolyT.ite' (PolyT.decide_eq_true (PolyT.and' f (PolyT.not' (h 2)))) (h 5) (PolyT.ite' (PolyT.decide_eq_true (PolyT.and' (PolyT.and' f (h 2)) (PolyT.not' (h 3)))) (h 6) (h 7))

private theorem addNC {K p d e t c : α → ℕ} {P Q : α → XYZ} (hc : PolyT c) (hp : PolyT p) (hd : Unary d) (pos : ∀ x, 1 ≤ d x) (hP : BP P) (hQ : BP Q) : Eval fun x => addN (K x) (p x) (d x) (e x) (t x) (c x) (P x) (Q x) := by
  let cp := fun (x : α) (j : ℕ) => t x+pt (d x)+j*(1+M3B.ECPolyDefs.triple (d x))
  let go := fun (x : α) (j : ℕ) => cp x 2+d x+j*gsize (d x) (e x)
  have A (j : ℕ) : BW fun x => word (K x) (cp x j+1) (d x) := wordC (asP hd)
  have G (j : ℕ) : BW fun x => word (K x) (go x j) (d x) := wordC (asP hd)
  have L : BW fun x => word (K x) (cp x 2) (d x) := wordC (asP hd)
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
  have HA {j : α → ℕ} (hj : PolyT j) : BA fun x => args x (j x) := by
    apply argsCases 14 (F:=args) hj
    · intro l hl; interval_cases l
      · exact wp3 (pubC (PolyT.sub hp (PolyT.const 1))) hP.2.1 hQ.2.1
      · exact wp3 (G 0) (A 0) (pubC (PolyT.const 0))
      · exact wp3 (pubC (PolyT.const 1)) hP.2.2 hQ.2.2
      · exact wp3 (G 2) (A 1) (pubC (PolyT.const 0))
      · exact wp3 (pubC (PolyT.sub hp (PolyT.const 1))) hP.2.2 hQ.2.2
      · exact wp3 (G 4) (A 0) (pubC (PolyT.const 0))
      · exact wp3 hP.2.1 hP.2.1 (pubC (PolyT.const 0))
      · exact wp3 (pubC (PolyT.const 3)) (G 6) (pubC hc)
      · exact wp3 (G 7) (A 1) (pubC (PolyT.const 0))
      · exact wp3 L L (pubC (PolyT.const 0))
      · exact wp3 (pubC (PolyT.sub hp (PolyT.const 1))) hP.2.1 (G 9)
      · exact wp3 (pubC (PolyT.sub hp (PolyT.const 1))) hQ.2.1 (G 10)
      · exact wp3 (pubC (PolyT.sub hp (PolyT.const 1))) (G 11) hP.2.1
      · exact wp3 L (G 12) (pubC (PolyT.const 0))
      · exact wp3 (pubC (PolyT.sub hp (PolyT.const 1))) hP.2.2 (G 13)
    · intro x l hl; obtain ⟨k,rfl⟩ : ∃ k, l=k+14 := ⟨_,(Nat.sub_add_cancel hl).symm⟩; rfl
  have O := ptwC (K:=K) (t:=t) (asP hd)
  unfold addN; dsimp only
  refine catC (catC (pboundC hp (asP hd)) (catC (cpC (PolyT.const 2) (fun _ => bndC hp (asP hd))) (cpC (PolyT.const 15) (fun _ => gboundC hp (asP hd)))))
    (catC (cpC (PolyT.const 15) (fun h => ghC hp hd pos (HA h))) (catC ?_ (catC ?_ (catC ?_ (catC ?_ (catC ?_ ?_))))))
  · exact row5C (asP hd) regC (G 0) (A 0) (G 1) (pubC (PolyT.const 1))
  · exact row5C (asP hd) regC (G 2) (A 1) (G 3) (pubC (PolyT.const 1))
  · exact row9C true (asP hd) hP.1 hQ.1 regC regC L (G 5) (G 8) (pubC (PolyT.const 0)) (pubC (PolyT.const 0))
  · exact row9C false (PolyT.const 1) hP.1 hQ.1 regC regC (fun _ => regC) (fun _ => hQ.1) (pubC (PolyT.const 0)) (pubC (PolyT.const 1)) (pubC (PolyT.const 0))
  · exact row9C false (asP hd) hP.1 hQ.1 regC regC O.2.1 hQ.2.1 hP.2.1 (pubC (PolyT.const 0)) (G 11)
  · exact row9C false (asP hd) hP.1 hQ.1 regC regC O.2.2 hQ.2.2 hP.2.2 (pubC (PolyT.const 0)) (G 14)

private theorem selectC {K a b pos neg : α → ℕ} (ha : PolyT a) (hb : PolyT b) : BW fun x => select (K x) (a x) (b x) (pos x) (neg x) := by
  intro j hj; let A := PolyT.testBit ha hj; let B := PolyT.testBit hb hj
  let F := PolyT.ite' (PolyT.decide_eq_true A) (PolyT.ite' (PolyT.decide_eq_true B) (PolyT.const (true,true)) (PolyT.const (false,true))) (PolyT.ite' (PolyT.decide_eq_true B) (PolyT.const (false,true)) (PolyT.const (false,false)))
  apply F.congr; intro x; dsimp only [select]; cases (a x).testBit (j x) <;> cases (b x).testBit (j x) <;> rfl
private theorem slotC {K p d e w t T b : α → ℕ} {cs seed : α → List ℕ} (hp : PolyT p) (hd : Unary d) (pos : ∀ x, 1 ≤ d x) (hT : PolyT T) (hcs : PolyT cs) (hS : PolyT seed) (hb : PolyT b) :
    Eval fun x => slotN (K x) (p x) (d x) (e x) (w x) (t x) (T x) (cs x) (seed x) (b x) := by
  let r := fun (x : α) (i : ℕ) => t x+pt (d x)+i*run (d x) (e x)
  let yo := fun x => t x+1+M3B.ECPolyDefs.triple (d x)
  let diff := fun x => t x+bankSize (d x) (e x)
  let X := fun x => word (K x) (t x+1) (d x); let Y := fun x => word (K x) (yo x) (d x)
  let g := fun x i => word (K x) (r x i) (d x); let u := fun x i => pub (K x) ((cs x).getD i 0)
  let pick := fun x l => select (K x) ((seed x).getD (4*b x+l) 0) ((seed x).getD (4*b x+2+l) 0) (yo x) (t x)
  have Xp : BW X := wordC (asP hd); have Yp : BW Y := wordC (asP hd)
  have G (j : ℕ) : BW fun x => g x j := wordC (asP hd)
  have U (j : ℕ) : BW fun x => u x j := pubC (PolyT.getD hcs (PolyT.const j) (PolyT.const 0))
  have PP (j : ℕ) : BW fun x => pick x j := by
    intro i hi; let u := PolyT.mul (PolyT.const 4) hb
    exact selectC (PolyT.getD hS (PolyT.add u (PolyT.const j)) (PolyT.const 0)) (PolyT.getD hS (PolyT.add (PolyT.add u (PolyT.const 2)) (PolyT.const j)) (PolyT.const 0)) hi
  let args := fun x (i : ℕ) => match i with
    | 0 => (u x 1,X x,Y x) | 1 => (pub (K x) 1,g x 0,u x 3) | 2 => (g x 1,Y x,pub (K x) 0)
    | 3 => (pub (K x) 1,X x,u x 2) | 4 => (g x 3,X x,u x 4) | 5 => (g x 4,X x,u x 5) | _ => (pick x 0,X x,pick x 1)
  have HA {j : α → ℕ} (hj : PolyT j) : BA fun x => args x (j x) := by
    apply argsCases 6 (F:=args) hj
    · intro l hl; interval_cases l
      · exact wp3 (U 1) Xp Yp
      · exact wp3 (pubC (PolyT.const 1)) (G 0) (U 3)
      · exact wp3 (G 1) Yp (pubC (PolyT.const 0))
      · exact wp3 (pubC (PolyT.const 1)) Xp (U 2)
      · exact wp3 (G 3) Xp (U 4)
      · exact wp3 (G 4) Xp (U 5)
      · exact wp3 (PP 0) Xp (PP 1)
    · intro x l hl; obtain ⟨k,rfl⟩ : ∃ k, l=k+6 := ⟨_,(Nat.sub_add_cancel hl).symm⟩; rfl
  unfold slotN; dsimp only
  refine catC (rowC (PolyT.const 1) (fun _ _ => regC) (fun _ hv => PolyT.not' (hv 0))) (catC (catC (pboundC hp (asP hd)) (cpC (PolyT.const 7) (fun _ => gboundC hp (asP hd))))
    (catC ?_ (catC (cpC (PolyT.const 7) (fun hi => hashC hp hd pos (HA hi).1 (HA hi).2.1 (HA hi).2.2))
      (catC (eqC (asP hd) (G 2) (G 5)) (colC (PolyT.add (asP hd) (PolyT.const 1)) (PolyT.const true) (G 6) (wordC (asP hd)) (pubC hT) (fun _ => regC))))))
  exact rowC (PolyT.const 1) (fun _ _ => regC) (fun _ hv => PolyT.beq' (hv 1) (PolyT.not' (hv 0)))

private theorem busC {K d e w T i : α → ℕ} (hd : PolyT d) (hw : PolyT w) (hT : PolyT T) : Eval fun x => busN (K x) (d x) (e x) (w x) (T x) (i x) := by
  unfold busN; dsimp only
  refine catC (rowC hw ?_ ?_) (colC hw (PolyT.const false) (wordC hd) (wordC hw) (wordC hw) (wordC hw))
  · intro i hi j; by_cases hj : j=0
    · simp only [hj,reduceIte]; exact PolyT.const (false,true)
    · simp only [hj,reduceIte]; exact wordC hw hi
  · intro i v hi h; exact PolyT.beq' (h 1) (PolyT.and' (h 0) (PolyT.testBit hT hi))
private theorem itePoint {C : α → Prop} [DecidablePred C] {a b : α → XYZ} (hc : PolyT fun x => decide (C x)) (ha : BP a) (hb : BP b) : BP fun x => if C x then a x else b x := by
  refine ⟨?_,fun hi => ?_,fun hi => ?_⟩
  · apply (PolyT.ite' hc ha.1 hb.1).congr; intro x; split <;> simp_all
  · apply (PolyT.ite' hc (ha.2.1 hi) (hb.2.1 hi)).congr; intro x; split <;> simp_all
  · apply (PolyT.ite' hc (ha.2.2 hi) (hb.2.2 hi)).congr; intro x; split <;> simp_all
private theorem condP {C : α → Prop} [DecidablePred C] {a b : α → N} (hc : PolyT fun x => decide (C x)) (ha : Eval a) (hb : Eval b) : Eval fun x => if C x then a x else b x := by
  refine ⟨?_,fun hi hl => ?_⟩
  · apply (PolyT.ite' hc ha.g hb.g).congr; intro x; split <;> simp_all
  · apply (PolyT.ite' hc (ha.c hi hl) (hb.c hi hl)).congr; intro x; split <;> simp_all
private theorem trP {d : α → ℕ} (h : PolyT d) : PolyT fun x => M3B.ECPolyDefs.triple (d x) := PolyT.add (PolyT.mul (PolyT.const 3) h) (PolyT.const 1)
private theorem ptP {d : α → ℕ} (h : PolyT d) : PolyT fun x => pt (d x) := PolyT.add (PolyT.const 1) (PolyT.mul (PolyT.const 2) (trP h))
private theorem runP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => run (d x) (e x) :=
  PolyT.add (PolyT.add (PolyT.add (PolyT.mul (PolyT.const 2) (trP hd)) hd) (PolyT.mul (PolyT.const 2) (PolyT.add (PolyT.mul (PolyT.const 2) hd) he))) (PolyT.const 1)
private theorem auxP {d : α → ℕ} (hd : PolyT d) : PolyT fun x => aux (d x) :=
  PolyT.add (PolyT.mul (PolyT.const 2) hd) (PolyT.mul (PolyT.const 3) (PolyT.add hd (PolyT.const 1)))
private theorem sizeP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => gsize (d x) (e x) := PolyT.add (runP hd he) (auxP hd)
private theorem bankP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => bankSize (d x) (e x) :=
  PolyT.add (PolyT.add (ptP hd) (PolyT.mul (PolyT.const 7) (runP hd he))) (PolyT.mul (PolyT.const 7) (auxP hd))
private theorem slotSizeP {d e w : α → ℕ} (hd : PolyT d) (he : PolyT e) (hw : PolyT w) : PolyT fun x => slotSize (d x) (e x) (w x) :=
  PolyT.add (PolyT.add (PolyT.add (bankP hd he) hd) (PolyT.add hd (PolyT.const 1))) (PolyT.mul (PolyT.const 3) hw)
private theorem mapSizeP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => mapSize (d x) (e x) := PolyT.add (ptP hd) (PolyT.mul (PolyT.const 4) (sizeP hd he))
private theorem addSizeP {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) : PolyT fun x => addSize (d x) (e x) := PolyT.add (PolyT.add (PolyT.add (ptP hd) (PolyT.mul (PolyT.const 2) (PolyT.add (PolyT.const 1) (trP hd)))) hd) (PolyT.mul (PolyT.const 15) (sizeP hd he))
private theorem netC {cs seed point : α → List ℕ} {pre : α → W} {m k T : α → ℕ}
    (hcs : PolyT cs) (hs : PolyT seed) (hq : PolyT point) (hT : PolyT T) (hp : PolyT pre) (hm : PolyT m) (hk : PolyT k) :
    Eval fun x => net (cs x) (seed x) (point x) (pre x) (m x) (k x) (T x) := by
  let p := fun x => (cs x).getD 0 0
  let d := fun x => bitLen (p x)+1
  let e := fun x => wires (d x)
  let w := fun x => max (d x) (k x)
  let t := fun x i => i*slotSize (d x) (e x) (w x)
  let ch := fun x s => t x (4*m x)+s*chainSize (d x) (e x) (m x)
  let K := fun x => ch x 2+pt (d x)
  have P : PolyT p := PolyT.getD hcs (PolyT.const 0) (PolyT.const 0)
  have U : Unary d := addU (clogU P) (constU 1)
  have D := asP U; have pos (x) : 1 ≤ d x := Nat.succ_pos _
  have Wd : PolyT w := maxP D hk
  let h2 := PolyT.mul (PolyT.const 2) hm; let h4 := PolyT.mul (PolyT.const 4) hm; let h1 := PolyT.add h2 (PolyT.const 1)
  have E : PolyT e := wiresP D
  have Ss := slotSizeP D E Wd
  have H : PolyT K := PolyT.add (PolyT.add (PolyT.mul h4 Ss) (PolyT.mul (PolyT.const 2) (PolyT.add (PolyT.mul h1 (mapSizeP D E)) (PolyT.mul h2 (addSizeP D E))))) (ptP D)
  let factor := fun (x : α) (i : ℕ) => (pin (K x) false,(ptw (K x) (d x) (t x i)).2)
  have Fact (i : α → ℕ) : BP fun x => factor x (i x) := ⟨pinC (PolyT.const false),(ptwC (K:=K) (t:=fun x => t x (i x)) D).2⟩
  let mp := fun x s i => ch x s+i*mapSize (d x) (e x)
  let ad := fun x s i => mp x s (2*m x+1)+i*addSize (d x) (e x)
  let acc := fun x s i => if i=0 then mp x s 0 else ad x s (i-1)
  let init := fun (x : α) (s : ℕ) => if s=1 then (pin (K x) true,pub (K x) 0,pub (K x) 0) else (pin (K x) (decide ((point x).getD 0 0=1)),pub (K x) ((point x).getD 1 0),pub (K x) ((point x).getD 2 0))
  have Init (s : ℕ) : BP fun x => init x s := by
    by_cases hh : s=1 <;> simp only [init,hh,reduceIte]
    · exact ⟨pinC (PolyT.const true),pubC (PolyT.const 0),pubC (PolyT.const 0)⟩
    · exact ⟨pinC (PolyT.decide_eq (PolyT.getD hq (PolyT.const 0) (PolyT.const 0)) (PolyT.const 1)),pubC (PolyT.getD hq (PolyT.const 1) (PolyT.const 0)),pubC (PolyT.getD hq (PolyT.const 2) (PolyT.const 0))⟩
  let c4 := fun x => 1296*(cs x).getD 4 0 % p x
  let chain := fun x s => cat (copies (2*m x+1) fun i => mapN (K x) (p x) (d x) (e x) (mp x s i) (if i=0 then init x s else factor x (2*(i-1)+s)))
    (cat (copies (2*m x) fun i => addN (K x) (p x) (d x) (e x) (ad x s i) (c4 x) (ptw (K x) (d x) (acc x s i)) (ptw (K x) (d x) (mp x s (i+1))))
      (eqs (pt (d x)) (word (K x) (acc x s (2*m x)) (pt (d x))) (word (K x) (ch x 2) (pt (d x)))))
  have C4 : PolyT c4 := PolyT.mod (PolyT.mul (PolyT.const 1296) (PolyT.getD hcs (PolyT.const 4) (PolyT.const 0))) P
  have Chain (s : ℕ) : Eval fun x => chain x s := by
    refine catC (cpC h1 (fun {i} hi => mapC P U pos ?_)) (catC (cpC h2 (fun _ => addNC C4 P U pos (ptwC D) (ptwC D))) (eqC (ptP D) (wordC (ptP D)) (wordC (ptP D))))
    exact itePoint (PolyT.decide_eq hi (PolyT.const 0)) (Init s) (Fact _)
  let b := PolyT.sub D (PolyT.const 1); let three := PolyT.mul (PolyT.const 3) b
  unfold net; dsimp only
  refine catC (rowC (PolyT.add H (PolyT.const 1)) (fun _ _ => regC) (fun _ _ => PolyT.const true))
    (catC (cpC h4 (fun hi => slotC P U pos hT hcs hs (PolyT.div hi (PolyT.const 4)))) (catC (Chain 0) (catC (Chain 1) (catC (cpC h4 (fun _ => busC D Wd hT)) ?_))))
  refine condP (PolyT.decide_le (PolyT.length hp) (PolyT.mul h4 three)) (rowC (PolyT.length hp) ?_ ?_) (rowC (PolyT.const 1) (fun _ _ => pinC (PolyT.const false)) (fun _ _ => PolyT.const false))
  · intro j hj l
    let h := PolyT.mod (PolyT.div hj b) (PolyT.const 3)
    let ix := (fun x => 2*(j x/(3*(d x-1))%(2*m x))+(j x/(2*m x*(3*(d x-1)))))
    simp only [apply_ite Prod.snd]; exact PolyT.ite' (PolyT.decide_eq h (PolyT.const 0)) (PolyT.const (false,false)) (PolyT.ite' (PolyT.decide_eq h (PolyT.const 1)) ((Fact ix).2.1 (PolyT.mod hj b)) ((Fact ix).2.2 (PolyT.mod hj b)))
  · intro j v hj hv; exact PolyT.beq' (hv 0) (PolyT.getD hp hj (PolyT.const false))

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

private theorem compC {f : α → W} (hf : PolyT f) : Eval fun x => compiled (f x) := by
  let frame := fun i (x : α) => (frames (f x)).getD i []
  have F (i : ℕ) : PolyT (frame i) := PolyT.getD (parseP hf) (PolyT.const i) (PolyT.const [])
  have D (i : ℕ) := decodeP (F i)
  exact netC (D 0) (D 3) (D 1) (PolyT.getD (D 2) (PolyT.const 1) (PolyT.const 0)) (F 6) (PolyT.div (PolyT.length (D 3)) (PolyT.const 4)) (w4_M5Evaluator.clog2_poly (PolyT.mul (PolyT.const 2) (PolyT.getD (D 2) (PolyT.const 1) (PolyT.const 0))))

private theorem lookupP {fs : α → List W} {T i h : α → ℕ} (hf : PolyT fs) (ht : PolyT T) (hi : PolyT i) (hh : PolyT h) :
    PolyT fun x => lookup (fs x) (T x) (i x) (h x) := by
  let frame := fun (j : ℕ) x => (fs x).getD j []
  have fr (j : ℕ) : PolyT (frame j) := PolyT.getD hf (PolyT.const j) (PolyT.const [])
  let B := fun x => (frames (frame 4 x)).map frames
  have bp : PolyT B := PolyT.map (f:=fun _ w => frames w) (parseP (PolyT.snd PolyT.id')) (parseP (fr 4))
  let block := fun x => (B x).getD (i x) []
  have bl : PolyT block := PolyT.getD bp hi (PolyT.const [])
  have labs := decodeP (fr 5); have seed := decodeP (fr 3); have p := PolyT.getD (decodeP (fr 0)) (PolyT.const 0) (PolyT.const 0)
  have off := PolyT.sum (PolyT.map (f:=fun (_ : α) (l : List W) => l.length) (PolyT.length (PolyT.snd PolyT.id')) (PolyT.take hi bp))
  let X := PolyT.fst (PolyT.id' (α:=α × ℕ)); let J := PolyT.snd (PolyT.id' (α:=α × ℕ))
  have pt := decodeP (PolyT.getD (PolyT.comp bl X) J (PolyT.const []))
  let val := fun j => PolyT.getD pt (PolyT.const j) (PolyT.const 0)
  let s := PolyT.mod (val 2) (PolyT.const 2); let ix := PolyT.add (PolyT.mul (PolyT.const 4) (PolyT.comp hi X)) (PolyT.mul (PolyT.const 2) s)
  let a := PolyT.getD (PolyT.comp seed X) ix (PolyT.const 0); let b := PolyT.getD (PolyT.comp seed X) (PolyT.add ix (PolyT.const 1)) (PolyT.const 0)
  let tt := PolyT.comp ht X
  have addr := PolyT.ite' (PolyT.decide_eq (val 0) (PolyT.const 1)) (PolyT.mul (PolyT.const 2) tt) (PolyT.add (PolyT.mod (PolyT.add (PolyT.mul a (val 1)) b) (PolyT.comp p X)) (PolyT.mul s tt))
  unfold lookup; dsimp only; simp only [← List.head?_filter]
  apply PolyT.optionMap (f:=fun x j => (w5_M6Sort.decode (frame 5 x)).getD ((((B x).take (i x)).map List.length).sum+j) 0)
  · exact PolyT.getD (PolyT.comp (g:=Prod.fst) labs X) (PolyT.add (PolyT.comp (g:=Prod.fst) off X) J) (PolyT.const 0)
  · apply PolyT.head?; apply PolyT.filter (hl:=PolyT.range (lenU bl)); exact PolyT.decide_eq addr (PolyT.comp hh X)

private theorem mulLen (a b : ℕ) : len (a*b) ≤ len a + len b := by
  have h : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
    rw [Nat.size_le,pow_add]; exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)
  simp only [len_nat]; omega
private theorem prodP {α : Type} [Enc α] {f : α → List ℕ} (hf : PolyT f) : PolyT fun x => (f x).prod := by
  obtain ⟨_,t,ht,_,_,hlen⟩ := hf.elim
  simp only [List.prod_eq_foldl]
  exact PolyT.foldl_add (g := fun _ a b => a*b) hf (PolyT.const 1) (PolyT.mul (PolyT.fst (PolyT.snd PolyT.id')) (PolyT.snd (PolyT.snd PolyT.id')))
    ⟨t,ht,fun x a b hb => (mulLen a b).trans (Nat.add_le_add_left ((len_le_of_mem hb).trans (hlen x)) (len a))⟩

private theorem chooseNatP {α : Type} [Enc α] {a j : α → ℕ} (ha : PolyT a) (hj : Unary j) : PolyT fun x => (a x).choose (j x) := by
  have r := PolyT.range hj
  have h1 : PolyT fun x => ((List.range (j x)).map (fun k => a x-k)).prod := prodP (PolyT.map (PolyT.sub (PolyT.comp ha (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id')) r)
  have h2 : PolyT fun x => ((List.range (j x)).map (fun k => k+1)).prod := prodP (PolyT.map (f:=fun _ k => k+1) (PolyT.add (PolyT.snd PolyT.id') (PolyT.const 1)) r)
  apply (PolyT.div h1 h2).congr; intro x

  have f (n k : ℕ) : ((List.range k).map (fun j => n-j)).prod = n.descFactorial k := by
    induction k with | zero => rfl | succ k ih => simp [List.range_succ,ih,Nat.descFactorial_succ,Nat.mul_comm]
  have g (k : ℕ) : ((List.range k).map (fun j => j+1)).prod = k.factorial := by
    induction k with | zero => rfl | succ k ih => simp [List.range_succ,ih,Nat.factorial_succ,Nat.mul_comm]
  rw [f,g,Nat.descFactorial_eq_factorial_mul_choose,Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]


private theorem signedResidueP {z j p : α → ℕ} {neg : α → Bool} (hz : PolyT z) (hj : Unary j) (hp : Unary p) (hn : PolyT neg) :
    PolyT fun x => (Ring.choose (if neg x then -(z x:ℤ) else (z x:ℤ)) (j x) % (2^(p x):ℤ)).toNat := by
  let jj := asP hj; let M := fun x => 2^(p x)
  have hm : PolyT M := PolyT.pow_unary (PolyT.const 2) hp
  let A := fun x => (z x+j x-1).choose (j x)
  let B := fun x => (z x).choose (j x)
  have ha : PolyT A := chooseNatP (PolyT.sub (PolyT.add hz jj) (PolyT.const 1)) hj
  have hb : PolyT B := chooseNatP hz hj
  let u := fun x => A x % M x
  have hu : PolyT u := PolyT.mod ha hm
  let f := fun x => if neg x then (if j x%2=0 then u x else (M x-u x)%M x) else B x%M x
  have H : PolyT f := PolyT.ite' (PolyT.decide_eq_true hn) (PolyT.ite' (PolyT.decide_eq (PolyT.mod jj (PolyT.const 2)) (PolyT.const 0)) hu (PolyT.mod (PolyT.sub hm hu) hm)) (PolyT.mod hb hm)
  have residue (a m : ℕ) (hm : 0 < m) : (m-a%m)%m = (-(a:ℤ) % (m:ℤ)).toNat := by
    rw [Int.neg_emod]; push_cast
    simp only [Int.natCast_dvd_natCast,abs_of_nonneg (Int.natCast_nonneg m),← Int.natCast_mod]
    by_cases h : m ∣ a
    · simp [h,Nat.mod_eq_zero_of_dvd h]
    · rw [if_neg h,Nat.mod_eq_of_lt (by have := Nat.pos_of_ne_zero (fun he => h (Nat.dvd_of_mod_eq_zero he)); omega : m-a%m < m)]; omega
  apply H.congr; intro x; dsimp [f,u,A,B,M]
  cases h : neg x
  · simp only [Bool.false_eq_true,reduceIte,Ring.choose_natCast]
    change _ = (((z x).choose (j x):ℤ) % ((2 ^ p x:ℕ):ℤ)).toNat
    rw [← Int.natCast_mod,Int.toNat_natCast]
  · simp only [reduceIte]
    by_cases h0 : z x=0 ∧ j x=0
    · obtain ⟨hz0,hj0⟩ := h0; rw [hz0,hj0]; simp
      change _ = (((1:ℕ):ℤ) % ((2 ^ p x:ℕ):ℤ)).toNat
      rw [← Int.natCast_mod,Int.toNat_natCast]
    · have hu : 1 ≤ z x+j x := by omega
      have cast : (((z x+j x-1):ℕ):ℤ) = (z x:ℤ)+(j x:ℤ)-1 := by omega
      rw [Ring.choose_neg,Units.smul_def,Int.coe_negOnePow_natCast,zsmul_eq_mul,neg_one_pow_eq_ite,← cast,Ring.choose_natCast]
      simp only [Nat.even_iff]
      by_cases even : j x%2=0
      · simp only [even,reduceIte,Int.cast_one,one_mul]
        change _ = ((((z x+j x-1).choose (j x)):ℤ) % ((2 ^ p x:ℕ):ℤ)).toNat
        rw [← Int.natCast_mod,Int.toNat_natCast]
      · simpa [even,← Int.natCast_pow] using residue ((z x+j x-1).choose (j x)) (2^p x) (Nat.two_pow_pos _)

private theorem coeffListP {z p n : α → ℕ} {q : α → Bool} (hz : PolyT z) (hp : Unary p) (hn : Unary n) (hq : PolyT q) :
    PolyT fun x => encodeNatListBin ((List.range (n x)).map fun j => (Ring.choose (if q x then (z x:ℤ) else -(z x:ℤ)) j % (2^(p x):ℤ)).toNat) := by
  apply w5_M6Sort.encode_poly
  let pr := PolyT.fst (PolyT.id' (α:=α × ℕ)); let jj := PolyT.snd (PolyT.id' (α:=α × ℕ))
  have pp : Unary fun x : α × ℕ => p x.1 := PolyT.comp (f:=fun x => List.replicate (p x) ()) hp pr
  have nn : Unary fun x : α × ℕ => n x.1 := PolyT.comp (f:=fun x => List.replicate (n x) ()) hn pr
  have bounded : Unary fun x : α × ℕ => min x.2 (n x.1) := by simpa only [List.length_replicate] using PolyT.unary_min_length jj nn
  have hh := signedResidueP (PolyT.comp (g:=Prod.fst) hz pr) bounded pp (PolyT.not' (PolyT.comp (g:=Prod.fst) hq pr))
  apply (PolyT.map (f:=fun x j => (Ring.choose (if !(q x) then -(z x:ℤ) else (z x:ℤ)) (min j (n x)) % (2^(p x):ℤ)).toNat) hh (PolyT.range hn)).congr
  intro x; apply List.map_congr_left; intro j hj; rw [min_eq_left (List.mem_range.mp hj).le]; cases q x <;> rfl

private theorem optionCaseP {β γ : Type} [Enc β] [Enc γ] {o : α → Option β} {d : α → γ} {f : α → β → γ}
    (ho : PolyT o) (hd : PolyT d) (hf : PolyT fun z : α × β => f z.1 z.2) :
    PolyT fun x => match o x with | none => d x | some z => f x z := by
  exact (PolyT.optionElim (o:=o) (d:=d) (f:=f) ho hd hf).congr (fun x => by cases o x <;> rfl)
open DetDLP_W1_Queries (second third)
set_option maxHeartbeats 1600000 in
theorem solution : PolyT ecEntry := by
  let w := first; let v := fun q => PolyT.bval (second q); let l := third
  let n := fun q => ne (compiled (w q)); let g := fun q => ng (compiled (w q)); let lo := fun q => g q+n q
  let dims := fun q => dimensions (w q); let m := fun q => (dims q).2.1; let prec := fun q => (dims q).2.2.2.2.1; let len := fun q => (dims q).2.2.2.2.2
  let i := fun q => v q-lo q; let th := fun q => (dims q).2.2.2.1
  let scan := fun q => lookup (frames (w q)) (th q) (i q/4) (PolyT.bval (l q))
  let ind := fun q (ok : Bool) => encodeNatListBin ((List.range (len q)).map fun j => if ok && j=0 then 1 else 0)
  have Wp : PolyT w := first_poly PolyT.id'
  have V : PolyT v := PolyT.bval' (first_poly (more_poly PolyT.id')); have L : PolyT l := first_poly (more_poly (more_poly PolyT.id'))
  have B := compC Wp
  have Np : PolyT n := PolyT.comp (f:=fun w => ne (compiled w)) (asP netBudgets.2) Wp
  have G : PolyT g := B.g; let Lo := PolyT.add G Np; let I := PolyT.sub V Lo
  have Ds : PolyT dims := PolyT.comp (g:=w) dimBudgets.2.1 Wp
  let M := PolyT.fst (PolyT.snd Ds); let T := PolyT.fst (PolyT.snd (PolyT.snd (PolyT.snd Ds)))
  have Nu : Unary len := PolyT.comp (f:=fun x => List.replicate (dimensions x).2.2.2.2.2 ()) dimBudgets.2.2.2.2.2.2 Wp
  have Pu : Unary prec := PolyT.comp (f:=fun x => List.replicate (dimensions x).2.2.2.2.1 ()) dimBudgets.2.2.2.2.2.1 Wp
  have Ind {a : W → Bool} (h : PolyT a) : PolyT fun q => ind q (a q) := by
    apply w5_M6Sort.encode_poly; apply PolyT.map (hl:=PolyT.range Nu)
    let J := PolyT.snd (PolyT.id' (α:=W × ℕ))
    exact PolyT.ite' (PolyT.decide_eq_true (PolyT.and' (PolyT.comp h (PolyT.fst PolyT.id')) (PolyT.decide_eq J (PolyT.const 0)))) (PolyT.const 1) (PolyT.const 0)
  have read : PolyT scan := lookupP (parseP Wp) T (PolyT.div I (PolyT.const 4)) (PolyT.bval' L)
  have P : PolyT fun z : W × ℕ => encodeNatListBin ((List.range (len z.1)).map fun j =>
      (Ring.choose (if i z.1%2=1 then (z.2:ℤ) else -(z.2:ℤ)) j % (2^(prec z.1):ℤ)).toNat) := by
    let X := PolyT.fst (PolyT.id' (α:=W × ℕ))
    have uP : Unary fun z : W × ℕ => prec z.1 := PolyT.comp (f:=fun x => List.replicate (prec x) ()) Pu X
    have uN : Unary fun z : W × ℕ => len z.1 := PolyT.comp (f:=fun x => List.replicate (len x) ()) Nu X
    have hs : PolyT fun z : W × ℕ => decide (i z.1%2=1) := PolyT.decide_eq (PolyT.mod (PolyT.comp (f:=i) I X) (PolyT.const 2)) (PolyT.const 1)
    have hh := coeffListP (z:=Prod.snd (α:=W)) (p:=fun z => prec z.1) (n:=fun z => len z.1) (q:=fun z => decide (i z.1%2=1)) (PolyT.snd PolyT.id') uP uN hs
    simpa only [decide_eq_true_eq] using hh
  let coeff := fun (q : W) (z : ℕ) => encodeNatListBin ((List.range (len q)).map fun j => (Ring.choose (if i q%2=1 then (z:ℤ) else -(z:ℤ)) j % (2^(prec q):ℤ)).toNat)
  let branch := fun (q : W) => match scan q with | none => ind q false | some z => coeff q z
  have hb : PolyT branch := by
    apply (optionCaseP (o:=scan) (d:=fun q => ind q false) (f:=coeff) read (Ind (PolyT.const false)) P).congr
    intro q; dsimp only [branch]; cases hs : scan q <;> rfl
  let X := PolyT.snd (PolyT.id' (α:=W × Bool))
  have eq := PolyT.or' (PolyT.all (f:=fun _ b => b == true) (PolyT.beq' X (PolyT.const true)) L) (PolyT.all (f:=fun _ b => b == false) (PolyT.beq' X (PolyT.const false)) L)
  let mask := fun q => lo q ≤ v q ∧ v q < lo q+4*m q
  have maskP : PolyT fun q => decide (mask q) := PolyT.decide_and (PolyT.decide_le Lo V) (PolyT.decide_lt V (PolyT.add Lo (PolyT.mul (PolyT.const 4) M)))
  have hB := PolyT.ite' (c:=mask) maskP hb (Ind eq)
  have hg := PolyT.ite' (c:=fun q => v q < g q) (PolyT.decide_lt V G) (Ind (B.c V L)) hB
  exact hg
