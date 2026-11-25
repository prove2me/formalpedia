-- Prove2me | solution 1 for DetDLP.m3d_ec_trace_protocol
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T01:12:09.345721+00:00
-- url     : https://prove2.me/submissions/65051651-c9d1-4479-9843-952a27663f43

import Definitions.Def_DetDLP_M3D_ECFastDefs
import Definitions.Def_DetDLP_W3C_NewtonPoly
import Definitions.Def_DetDLP_W3C_Stage2Trace

set_option autoImplicit false
namespace DetDLP.M3D.Fast.ECRun
open Groundwork ECStep ECQueryOps ECQueries BlockLookup NineOracleLoop DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.Computation

private def frameStep (n : ℕ) (c : List W × W) (_ : Bool) : List W × W :=
  if c.2.headD false = true then ((first c.2 |>.take n) :: c.1, (more c.2).take n) else c
private theorem frameLen (a : W) : a.length ≤ (Encoding.frame a).length := by
  induction a with | nil => simp | cons b a ih => change a.length+1 ≤ (Encoding.frame a).length+1+1; omega
private theorem run (xs : List W) (acc : List W) (fuel : W) (n : ℕ) (hn : (Encoding.encodeList id xs).length ≤ n)
    (hf : xs.length ≤ fuel.length) : (fuel.foldl (frameStep n) (acc,Encoding.encodeList id xs)).1 = xs.reverse ++ acc := by
  induction xs generalizing acc fuel with
  | nil => induction fuel <;> simp_all [Encoding.encodeList,frameStep,List.foldl]
  | cons a xs ih => cases fuel with
    | nil => simp at hf
    | cons b fuel =>
      have ha := frameLen a
      have h := hn; simp only [Encoding.encodeList,id_eq,List.length_cons,List.length_append] at h
      simp only [List.foldl_cons,frameStep,show (Encoding.encodeList id (a::xs)).headD false = true from rfl,if_true,first_cons,more_cons,id_eq,List.take_of_length_le (show a.length ≤ n by omega),List.take_of_length_le (show (Encoding.encodeList id xs).length ≤ n by omega)]
      simpa using ih (a::acc) fuel (by omega) (by simpa using hf)
@[simp] theorem decodeFrames_correct (xs : List W) : decodeFrames (Encoding.encodeList id xs) = xs := by
  have h : xs.length ≤ (Encoding.encodeList id xs).length := by induction xs <;> simp_all [Encoding.encodeList]; omega
  change (((Encoding.encodeList id xs).foldl (frameStep _) ([],Encoding.encodeList id xs)).1).reverse = xs
  simp [run _ _ _ _ le_rfl h]


def fields (ph j : ℕ) (i o p k r f a : Wd) : List Wd := [countWord ph,i,o,p,k,countWord j,r,f,a]

private theorem parseAux (x xs acc : Wd) : ∀ fuel : Wd, x.length ≤ fuel.length →
    fuel.foldl advance (acc,Encoding.frame x ++ xs) = (x.reverse ++ acc,false :: xs) := by
  induction x generalizing acc with
  | nil => intro fuel _; induction fuel <;> simp_all [Encoding.frame,advance,List.foldl]
  | cons b x ih => intro fuel hf; cases fuel with
    | nil => simp at hf
    | cons k fuel => simpa [Encoding.frame,advance,List.foldl,List.append_assoc] using ih (b::acc) fuel (by simpa using hf)

theorem parsePair (x a : Wd) : parse (true :: pairWord x a) = (x.reverse,false :: a) := by
  have e : pairWord x a = Encoding.frame x ++ a := congrArg (· ++ a) (frame_correct x)
  have h : x.length ≤ (Encoding.frame x).length := by
    clear e
    induction x with
    | nil => decide
    | cons b x ih => change x.length+1 ≤ (Encoding.frame x).length+1+1; omega
  simp only [parse,e,List.tail_cons]; rw [parseAux]; simp; simp; omega

theorem entry {i : Wd} (hi : i.headD true = true) (a : Wd) : ecStep (pairWord i a) =
    send 0 (packState 0 0 i [] [] [] [] [] []) (DetDLP_M3D_orderQuery i) := by
  simp only [ecStep,first,parsePair,List.reverse_reverse,hi,if_true]

theorem packed (ph j : ℕ) (i o p k r f a ans : Wd) :
    ecStep (pairWord (packState ph j i o p k r f a) ans) = round (fields ph j i o p k r f a) ans := by
  simp [ecStep,first,more,parsePair,packState,fields]

variable {call : Wd → Wd → Prop} {st ans out : Wd} {fuel lim : ℕ}

/-- A calling transition consumes exactly one unit of fuel. -/
theorem prepend {slot : Fin 9} {st' q a : Wd}
    (h : ecStep (pairWord st ans) = send slot st' q) (hcall : call (tag9 slot q) a)
    (hin : (pairWord st ans).length ≤ lim) (hq : (pairWord st' (tag9 slot q)).length ≤ lim)
    (ha : a.length ≤ lim) (next : LoopRuns ecStep call fuel st' a out lim) :
    LoopRuns ecStep call (fuel+1) st ans out lim := Or.inr ⟨_,_,_,h,hin,hq,ha,hcall,next⟩

theorem widen (h : LoopRuns ecStep call fuel st ans out lim) {n : ℕ} (hn : lim ≤ n) :
    LoopRuns ecStep call fuel st ans out n := by
  induction fuel generalizing st ans with
  | zero => exact False.elim h
  | succ k ih =>
    rcases h with ⟨he,hi,ho⟩ | ⟨s,q,a,he,hi,hq,ha,hc,ht⟩
    · exact Or.inl ⟨he,hi.trans hn,ho.trans hn⟩
    · exact Or.inr ⟨s,q,a,he,hi.trans hn,hq.trans hn,ha.trans hn,hc,ih ht⟩

theorem callNext {slot : Fin 9} {st' q a : Wd} (h : ecStep (pairWord st ans) = send slot st' q)
    (hc : call (tag9 slot q) a) (next : Runs call fuel st' a out) : Runs call (fuel+1) st ans out := by
  obtain ⟨n,ht⟩ := next
  exact ⟨max (max n a.length) (max (pairWord st ans).length (pairWord st' (tag9 slot q)).length),
    prepend h hc (by omega) (by omega) (by omega) (widen ht (by omega))⟩

theorem halt (h : ecStep (pairWord st ans) = true :: out) : Runs call 1 st ans out :=
  ⟨max (pairWord st ans).length out.length,Or.inl ⟨h,le_max_left _ _,le_max_right _ _⟩⟩

theorem smallRun {i o y : Wd} (hi : i.headD true = true) (hd : DetDLP_M3D_dispatch i o = false)
    (ho : call (tag9 0 (DetDLP_M3D_orderQuery i)) o) (hy : call (tag9 1 i) y) : Runs call 3 i [] y := by
  apply callNext (entry hi []) ho
  apply callNext (st' := packState 1 0 i o [] [] [] [] []) _ hy
  · apply halt; rw [packed]; rfl
  · rw [packed]; change (if DetDLP_M3D_dispatch i o then _ else _) = _; rw [hd]; rfl

namespace Context
variable (c : Context)
/-- Order, preparation, enumeration, and the initial generator update. -/
theorem launch (head : c.i.headD true = true) (large : DetDLP_M3D_dispatch c.i c.o = true)
    (order : call (tag9 0 (DetDLP_M3D_orderQuery c.i)) c.o)
    (prep : call (tag9 2 (curveWord c.i)) c.p) (enumerate : call (tag9 3 c.p) c.k)
    {r : Wd} (gen : call (tag9 8 c.genQ) r) (next : Runs call fuel (c.state 4 0 []) r out) :
    Runs call (fuel+4) c.i [] out := by
  apply callNext (entry head []) order
  apply callNext (st' := packState 2 0 c.i c.o [] [] [] [] []) _ prep
  · apply callNext (st' := packState 3 0 c.i c.o c.p [] [] [] []) _ enumerate
    · apply callNext _ gen next; rw [packed]; rfl
    · rw [packed]; rfl
  · rw [packed]; change (if DetDLP_M3D_dispatch c.i c.o then _ else _) = _; rw [large]; rfl

/-- Each coordinate takes two calls: decomposition, then HNF update. The last
    update enters the root builder without asking for a nonexistent coordinate. -/
theorem initLoop (r u : ℕ → Wd) (dec : ∀ j < c.size, call (tag9 5 (c.decQ j)) (u j))
    (upd : ∀ j < c.size, call (tag9 8 (c.updQ j (r j) (u j))) (r (j+1)))
    {root : Wd} (build : call (tag9 6 (c.query (r c.size) [])) root)
    (next : Runs call fuel (c.state 8 0 (r c.size)) root out) :
    Runs call (fuel+2*c.size+1) (c.state 4 0 []) (r 0) out := by
  have pass (d j : ℕ) (hd : j+1+d=c.size) :
      Runs call (fuel+2*d+2) (c.state 6 j (r j)) (u j) out := by
    induction d generalizing j with
    | zero =>
      have hj : j+1=c.size := by omega
      apply callNext (st' := c.state 7 j (r j)) _ (upd j (by omega))
      · apply callNext _ build next; rw [packed]
        change (if PolyT.bval (countWord j)+1 < c.size then _ else _) = _
        rw [decode_count,if_neg (by omega),← hj]; rfl
      · rw [packed]; change send 8 (c.state 7 (PolyT.bval (countWord j)) (r j))
          (c.updQ (PolyT.bval (countWord j)) (r j) (u j)) = _; rw [decode_count]
    | succ d ih =>
      have hj : j+1<c.size := by omega
      rw [show fuel+2*(d+1)+2 = (fuel+2*d+2)+1+1 by omega]
      apply callNext (st' := c.state 7 j (r j)) _ (upd j (by omega))
      · apply callNext _ (dec (j+1) hj) (ih (j+1) (by omega)); rw [packed]
        change (if PolyT.bval (countWord j)+1 < c.size then _ else _) = _
        rw [decode_count,if_pos hj,show idx (fields 7 j c.i c.o c.p c.k (r j) [] []) = j from decode_count j]
        rfl
      · rw [packed]; change send 8 (c.state 7 (PolyT.bval (countWord j)) (r j))
          (c.updQ (PolyT.bval (countWord j)) (r j) (u j)) = _; rw [decode_count]
  have hN : 0 < c.size := by dsimp [size]; omega
  rw [show fuel+2*c.size+1=(fuel+2*(c.size-1)+2)+1 by omega]
  apply callNext _ (dec 0 hN) (pass (c.size-1) 0 (by omega)); rw [packed]; rfl

/-- Coupled initialization: the same HNF witnesses certify both the mathematical
    trace and the words threaded through the actual sequence of controller calls. -/
theorem initTraceRun {M N : ℕ} [NeZero M] (rows : List (w3_Row M N)) (hrows : rows.length=c.size+1)
    (P : w3_Rep M N → Prop) (u : ℕ → Wd) (dec : ∀ j < c.size, call (tag9 5 (c.decQ j)) (u j))
    (gen : ∃ t, w3_update (rows[0]'(by omega)) (w3_full M N) t ∧ P t ∧ call (tag9 8 c.genQ) (repWord t))
    (step : ∀ j (hj : j < c.size) s, P s → ∃ t, w3_update (rows[j+1]'(by omega)) s t ∧ P t ∧
      call (tag9 8 (c.updQ j (repWord s) (u j))) (repWord t)) :
    ∃ t, w3_InitTrace rows (w3_full M N) t ∧ P t ∧ ∀ {root out : Wd} {fuel : ℕ},
      call (tag9 6 (c.query (repWord t) [])) root → Runs call fuel (c.state 8 0 (repWord t)) root out →
      ∃ first, call (tag9 8 c.genQ) first ∧ Runs call (fuel+2*c.size+1) (c.state 4 0 []) first out := by
  classical
  obtain ⟨t0,hg,h0,hc⟩ := gen
  let R : ℕ → {t : w3_Rep M N // P t} := Nat.rec ⟨t0,h0⟩ (fun j s =>
    if hj : j<c.size then ⟨(step j hj s.1 s.2).choose,(step j hj s.1 s.2).choose_spec.2.1⟩ else s)
  have each (j : ℕ) (hj : j<c.size) : w3_update (rows[j+1]'(by omega)) (R j).1 (R (j+1)).1 ∧
      call (tag9 8 (c.updQ j (repWord (R j).1) (u j))) (repWord (R (j+1)).1) := by
    have he : (R (j+1)).1 = (step j hj (R j).1 (R j).2).choose := by simp [R,hj]
    have h := (step j hj (R j).1 (R j).2).choose_spec
    rw [he]; exact ⟨h.1,h.2.2⟩
  have tr (d j : ℕ) (hd : j+d=c.size) : w3_InitTrace (rows.drop (j+1)) (R j).1 (R c.size).1 := by
    induction d generalizing j with
    | zero => have he : j=c.size := by omega
              subst j; rw [List.drop_eq_nil_of_le (by omega)]; exact .nil _
    | succ d ih => rw [List.drop_eq_getElem_cons (show j+1<rows.length by omega)]
                   exact .cons (each j (by omega)).1 (ih (j+1) (by omega))
  refine ⟨(R c.size).1,?_,(R c.size).2,?_⟩
  · have e := List.drop_eq_getElem_cons (show 0<rows.length by omega)
    rw [List.drop_zero] at e
    exact e.symm ▸ (w3_InitTrace.cons hg (tr c.size 0 (by omega)))
  · intro root out fuel build next
    exact ⟨_,hc,c.initLoop (fun j => repWord (R j).1) u dec (fun j hj => (each j hj).2) build next⟩

end Context
end DetDLP.M3D.Fast.ECRun
namespace DetDLP.M3D.Fast.ECRun
open Groundwork ECStep ECQueryOps ECQueries BlockLookup NineOracleLoop DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace Context
variable (c : Context)
theorem massBit_eq {q : w3_Query} {C : ℕ} (net : w3_Net q C) {w : Wd}
    (hm : c.blocks.length = q.m) (hM : c.modulus = q.M)
    (hw : EncodesTruncPoly (w3_precision q) (w3_len q) w (BTNContract net.G net.T)) :
    c.massBit (w3_packet net) w = decide (0 < w3_mass q) := by
  unfold massBit; rw [hm,hM,w3_packet,encodeTerminalBTNInstance,decodeFrames_correct]
  change W3C.NewtonPoly.massPosWord q.m q.M (PolyT.bval (countWord (w3_precision q))) w = _
  rw [decode_count]; exact W3C.NewtonPoly.massPosWord_correct net hw

variable {call : Wd → Wd → Prop} {fuel : ℕ} {out r packet result : Wd}

theorem contractRoot (hc : call (tag9 7 packet) result)
    (next : Runs call fuel (c.state 9 1 r [] packet) result out) :
    Runs call (fuel+1) (c.state 8 0 r) packet out := by
  apply callNext _ hc next; rw [packed]; rfl

theorem zeroRun (hc : call (tag9 7 packet) result) (hz : c.massBit packet result = false) :
    Runs call 2 (c.state 8 0 r) packet (countWord ((W3C.NewtonPoly.repLabels r).getD (c.blocks.flatten.length+1) 0)) := by
  apply c.contractRoot hc; apply halt; rw [packed]
  change (if c.massBit packet result then _ else _) = _; rw [hz]; rfl

theorem zeroTarget {M N : ℕ} [NeZero M] {q : w3_Query} {C : ℕ} (net : w3_Net q C)
    (t : w3_Rep M N) (j : Fin N) (hj : j.val = c.blocks.flatten.length+1)
    (hm : c.blocks.length=q.m) (hM : c.modulus=q.M) (hz : w3_mass q=0)
    (hc : call (tag9 7 (w3_packet net)) result)
    (hw : EncodesTruncPoly (w3_precision q) (w3_len q) result (BTNContract net.G net.T)) :
    Runs call 2 (c.state 8 0 (encodeCosetRep (fun i => (t.1 i).val) t.2)) (w3_packet net) (countWord (t.1 j).val) := by
  have h := c.zeroRun (r := encodeCosetRep (fun i => (t.1 i).val) t.2) hc
    (by rw [c.massBit_eq net hm hM hw,hz]; decide)
  rw [W3C.NewtonPoly.repLabels_correct,← hj] at h
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos j.isLt,Option.getD_some] using h

/-- Interpret a pending send before choosing the phase whose answer triggered it. -/
private def Pending (call : Wd → Wd → Prop) (n : ℕ) (instr out : Wd) : Prop :=
  ∃ (slot : Fin 9) (st q a : Wd), instr = send slot st q ∧ call (tag9 slot q) a ∧ Runs call n st a out

private theorem consume {instr st ans : Wd} (he : ecStep (pairWord st ans) = instr)
    (pending : Pending call fuel instr out) : Runs call (fuel+1) st ans out := by
  obtain ⟨j,s,q,a,eq,hcall,hn⟩ := pending
  exact callNext (he.trans eq) hcall hn

private abbrev pick (r f : Wd) := if f.length < c.depth then
    send 6 (c.state 8 3 r f) (c.query r (f++[false]))
  else send 8 (c.state 10 0 r) (c.cutQ r f)

private theorem pathLen (mass : Wd → ℤ) (j : ℕ) : (DetDLP_W3C_PrefixSearch mass j).length=j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [DetDLP_W3C_PrefixSearch,ih]

/-- A positive root consumes two rounds, two per bit, and one to restart
    after the HNF answer. No mass query is issued at a completed leaf. -/
theorem positiveRun (mass : Wd → ℤ) (pk val : ℕ → Wd)
    (hc : call (tag9 7 packet) result) (hp : c.massBit packet result = true)
    (build : ∀ j < c.depth, call (tag9 6 (c.query r (DetDLP_W3C_PrefixSearch mass j ++ [false]))) (pk j))
    (eval : ∀ j < c.depth, call (tag9 7 (pk j)) (val j))
    (bit : ∀ j < c.depth, c.massBit (pk j) (val j) = decide (0 < mass (DetDLP_W3C_PrefixSearch mass j ++ [false])))
    {r' root' : Wd} (cut : call (tag9 8 (c.cutQ r (DetDLP_W3C_PrefixSearch mass c.depth))) r')
    (root : call (tag9 6 (c.query r' [])) root') (next : Runs call fuel (c.state 8 0 r') root' out) :
    Runs call (fuel+2*c.depth+3) (c.state 8 0 r) packet out := by
  let path := DetDLP_W3C_PrefixSearch mass
  have descend (d j : ℕ) (hd : j+d=c.depth) : Pending call (fuel+2*d+1) (c.pick r (path j)) out := by
    induction d generalizing j with
    | zero =>
      have hj : j=c.depth := by omega
      subst j; rw [pick,if_neg (by rw [pathLen]; omega)]
      refine ⟨8,_,_,r',rfl,cut,?_⟩
      apply callNext _ root next; rw [packed]; rfl
    | succ d ih =>
      have hj : j<c.depth := by omega
      rw [pick,if_pos (by simpa only [path,pathLen] using hj)]
      refine ⟨6,_,_,pk j,rfl,build j hj,?_⟩
      rw [show fuel+2*(d+1)+1=(fuel+2*d+1)+1+1 by omega]
      apply callNext (st' := c.state 9 3 r (path j) (pk j)) _ (eval j hj)
      · apply consume _ (ih (j+1) (by omega)); rw [packed]
        change c.pick r (path j ++ [!c.massBit (pk j) (val j)]) = c.pick r (path (j+1))
        rw [bit j hj]; by_cases h : 0 < mass (DetDLP_W3C_PrefixSearch mass j ++ [false])
        · simp [path,DetDLP_W3C_PrefixSearch,h,not_le.mpr h]
        · simp [path,DetDLP_W3C_PrefixSearch,h,le_of_not_gt h]
      · rw [packed]; rfl
  apply c.contractRoot hc; apply consume _ (descend c.depth 0 (by omega)); rw [packed]
  change (if c.massBit packet result then _ else _) = _; rw [hp]; rfl

/-- The full-depth prefix selects the same violated row that is sent to HNF. -/
theorem positiveCut {q : w3_Query} (s : w3_Rep q.M q.FB.totalCoords) (hy : q.y=s.1)
    (fixed : ∀ X Y, (q.code X Y).length=c.depth) (inj : Function.Injective (Function.uncurry q.code))
    (hM : 2 ≤ q.M) (hm : c.blocks.length=q.m) (hmod : c.modulus=q.M) (pos : 0<w3c_massAt q [])
    (hc : call (tag9 7 packet) result) (hpos : c.massBit packet result=true)
    (pkt ans : Wd → Wd) (child : ∀ f, f.length<c.depth →
      call (tag9 6 (c.query (repWord s) (f++[false]))) (pkt f) ∧ call (tag9 7 (pkt f)) (ans f) ∧
      ∃ (C : ℕ) (net : w3_Net {q with pre := f++[false], input := c.query (repWord s) (f++[false])} C),
        pkt f=w3_packet net ∧
        EncodesTruncPoly (w3_precision q) (w3_len q) (ans f) (BTNContract net.G net.T))
    (update : ∀ X Y, q.FB.tupleVal Y=q.FB.tupleVal X+q.P → ¬w3_holds (w3_shiftRow q.FB q.M X Y) s.1 →
      ∃ t, w3_update (w3_shiftRow q.FB q.M X Y) s t ∧ 2*Nat.card (w3_coset t) ≤ Nat.card (w3_coset s) ∧
        call (tag9 8 (c.cutQ (repWord s) (q.code X Y))) (repWord t)) :
    ∃ t, w3_cut q.FB q.M q.P s t ∧ ∀ {root' fuel out}, call (tag9 6 (c.query (repWord t) [])) root' →
      Runs call fuel (c.state 8 0 (repWord t)) root' out →
      Runs call (fuel+2*c.depth+3) (c.state 8 0 (repWord s)) packet out := by
  let path := DetDLP_W3C_PrefixSearch (w3c_massAt q)
  obtain ⟨_,_,⟨X,Y⟩,⟨he,hg,hw,hbad⟩,_⟩ := w3c_descent q fixed inj hM pos
  rw [hy] at hw hbad
  obtain ⟨t,hu,half,hr⟩ := update X Y hg hbad
  refine ⟨t,⟨X,Y,hg,hw,hbad,hu,half⟩,?_⟩
  intro root' fuel out root next
  have hh (j : ℕ) (hj : j<c.depth) := child (path j) (by simpa only [path,pathLen] using hj)
  apply c.positiveRun (w3c_massAt q) (fun j => pkt (path j)) (fun j => ans (path j)) hc hpos
    (fun j hj => (hh j hj).1) (fun j hj => (hh j hj).2.1) _ _ root next
  · intro j hj; obtain ⟨_,net,eq,hw⟩ := (hh j hj).2.2
    rw [eq]; exact c.massBit_eq net hm hmod hw
  · simpa only [he] using hr

/-- The coset measure bounds the *execution*, not just the mathematical trace.
    Each cut restarts on the very representative returned by the HNF call. -/
theorem cutLoop {q : w3_Query} (z : w3_Label q.M q.FB.totalCoords)
    (pkt : w3_Rep q.M q.FB.totalCoords → Wd) (target : Fin q.FB.totalCoords)
    (stop : ∀ t, W3C.Stage2Trace.Invariant z t → w3_mass (W3C.Stage2Trace.root q t)=0 →
      Runs call 2 (c.state 8 0 (repWord t)) (pkt t) (countWord (t.1 target).val))
    (cut : ∀ s, W3C.Stage2Trace.Invariant z s → 0 < w3_mass (W3C.Stage2Trace.root q s) →
      ∃ t, w3_cut q.FB q.M q.P s t ∧ W3C.Stage2Trace.Invariant z t ∧ ∀ {n out},
        Runs call n (c.state 8 0 (repWord t)) (pkt t) out →
        Runs call (n+2*c.depth+3) (c.state 8 0 (repWord s)) (pkt s) out)
    (k : ℕ) (s : w3_Rep q.M q.FB.totalCoords) (inv : W3C.Stage2Trace.Invariant z s)
    (cap : Nat.card (w3_coset s) ≤ 2^k) :
    ∃ n t, n ≤ k ∧ w3_Cuts q.FB q.M q.P n s t ∧ w3_mass (W3C.Stage2Trace.root q t)=0 ∧
      Runs call (2+n*(2*c.depth+3)) (c.state 8 0 (repWord s)) (pkt s) (countWord (t.1 target).val) := by
  induction k generalizing s with
  | zero =>
    by_cases hz : w3_mass (W3C.Stage2Trace.root q s)=0
    · exact ⟨0,s,le_rfl,.nil s,hz,by simpa using stop s inv hz⟩
    · have nn := w3c_mass_nonneg (W3C.Stage2Trace.root q s)
      obtain ⟨t,⟨_,_,_,_,_,_,half⟩,ht,_⟩ := cut s inv (by omega)
      have := (W3C.Stage2Trace.card_bounds ht.2).1; simp only [pow_zero] at cap; omega
  | succ k ih =>
    by_cases hz : w3_mass (W3C.Stage2Trace.root q s)=0
    · exact ⟨0,s,Nat.zero_le _,.nil s,hz,by simpa using stop s inv hz⟩
    · have nn := w3c_mass_nonneg (W3C.Stage2Trace.root q s)
      obtain ⟨t,hcut,ht,run⟩ := cut s inv (by omega)
      have ⟨_,_,_,_,_,_,half⟩ := hcut; rw [pow_succ] at cap
      obtain ⟨n,u,hn,hu,hz,hr⟩ := ih t ht (by omega)
      exact ⟨n+1,u,by omega,.cons hcut hu,hz,by simpa [Nat.succ_mul,Nat.add_assoc] using run hr⟩

/-- Glue the initial order/plan calls to the HNF row trace, including the
    root builder call for the representative that actually reached phase 8. -/
theorem startRun {q : w3_Query} (z : w3_Label q.M q.FB.totalCoords)
    (U : Fin q.FB.totalCoords → q.FB.BlockTuple) (pkt : w3_Rep q.M q.FB.totalCoords → Wd)
    (size : q.FB.totalCoords=c.size) (head : c.i.headD true=true) (large : DetDLP_M3D_dispatch c.i c.o=true)
    (order : call (tag9 0 (DetDLP_M3D_orderQuery c.i)) c.o)
    (plan : call (tag9 2 (curveWord c.i)) c.p) (enumerate : call (tag9 3 c.p) c.k)
    (u : ℕ → Wd) (dec : ∀ j < c.size, call (tag9 5 (c.decQ j)) (u j))
    (gen : ∃ t, w3_update ((w3_initRows q.FB q.M U)[0]'(by simp [w3_initRows]))
        (w3_full q.M q.FB.totalCoords) t ∧ W3C.Stage2Trace.Invariant z t ∧ call (tag9 8 c.genQ) (repWord t))
    (step : ∀ j (hj : j<c.size) s, W3C.Stage2Trace.Invariant z s → ∃ t,
      w3_update ((w3_initRows q.FB q.M U)[j+1]'(by
        simpa only [w3_initRows,List.length_cons,List.length_map,List.length_finRange,Nat.succ_lt_succ_iff,size] using hj)) s t ∧
      W3C.Stage2Trace.Invariant z t ∧ call (tag9 8 (c.updQ j (repWord s) (u j))) (repWord t))
    (root : ∀ t, W3C.Stage2Trace.Invariant z t → call (tag9 6 (c.query (repWord t) [])) (pkt t)) :
    ∃ s, w3_InitTrace (w3_initRows q.FB q.M U) (w3_full q.M q.FB.totalCoords) s ∧
      W3C.Stage2Trace.Invariant z s ∧ ∀ {n out}, Runs call n (c.state 8 0 (repWord s)) (pkt s) out →
        Runs call (n+2*c.size+5) c.i [] out := by
  obtain ⟨s,hs,hi,next⟩ := c.initTraceRun (w3_initRows q.FB q.M U) (by simp [w3_initRows,size])
    (W3C.Stage2Trace.Invariant z) u dec gen step
  refine ⟨s,hs,hi,?_⟩; intro n out hr
  obtain ⟨_,hg,rest⟩ := next (root s hi) hr
  exact c.launch head large order plan enumerate hg rest

/-- Compose the initialized run and all halving cuts. The scan-free branch
    returns the target label of the representative in its outcome certificate. -/
theorem largeOutcome {q : w3_Query} (z : w3_Label q.M q.FB.totalCoords)
    (U : Fin q.FB.totalCoords → q.FB.BlockTuple) (pkt : w3_Rep q.M q.FB.totalCoords → Wd)
    (start : ∃ s, w3_InitTrace (w3_initRows q.FB q.M U) (w3_full q.M q.FB.totalCoords) s ∧
      W3C.Stage2Trace.Invariant z s ∧ ∀ {n out}, Runs call n (c.state 8 0 (repWord s)) (pkt s) out →
        Runs call (n+2*c.size+5) c.i [] out)
    (stop : ∀ t, W3C.Stage2Trace.Invariant z t → w3_mass (W3C.Stage2Trace.root q t)=0 →
      Runs call 2 (c.state 8 0 (repWord t)) (pkt t) (countWord (t.1 q.FB.targetCoord).val))
    (cut : ∀ s, W3C.Stage2Trace.Invariant z s → 0 < w3_mass (W3C.Stage2Trace.root q s) →
      ∃ t, w3_cut q.FB q.M q.P s t ∧ W3C.Stage2Trace.Invariant z t ∧ ∀ {n out},
        Runs call n (c.state 8 0 (repWord t)) (pkt t) out →
        Runs call (n+2*c.depth+3) (c.state 8 0 (repWord s)) (pkt s) out) :
    ∃ y n, w3_Outcome q.FB q.M q.P U y ∧ n ≤ Nat.clog 2 (q.M^q.FB.totalCoords) ∧
      Runs call (2+n*(2*c.depth+3)+2*c.size+5) c.i [] (countWord (y q.FB.targetCoord).val) := by
  obtain ⟨s,init,hi,run⟩ := start
  obtain ⟨n,t,hn,cuts,zero,trace⟩ := c.cutLoop z pkt q.FB.targetCoord stop cut _ s hi
    ((W3C.Stage2Trace.card_bounds hi.2).2.trans (Nat.le_pow_clog (by decide : 1<2) _))
  exact ⟨t.1,n,⟨s,t,n,init,cuts,hn,rfl,w3c_zero_pass (W3C.Stage2Trace.root q t) rfl zero⟩,hn,run trace⟩

end Context
end DetDLP.M3D.Fast.ECRun
namespace DetDLP.M3D.Fast.ECRun.Assembly
open ECStep NineOracleLoop W3C.Stage2Trace M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
section Trace
variable (c : Context) (q : w3_Query) (z : w3_Label q.M q.FB.totalCoords)
local notation "Rep" => w3_Rep q.M q.FB.totalCoords
local notation "rwrd" => Context.repWord
theorem concludeTrace {call : Wd → Wd → Prop} (U : Fin q.FB.totalCoords → q.FB.BlockTuple)
    (hm : c.blocks.length=q.m) (hmod : c.modulus=q.M) (hM : 2 ≤ q.M)
    (target : q.FB.targetCoord.val=c.blocks.flatten.length+1)
    (fixed : ∀ X Y, (q.code X Y).length=c.depth) (inj : Function.Injective (Function.uncurry q.code))
    (packets results : Rep → Wd → Wd)
    (terminal : ∀ (s : Rep) f, f.length ≤ c.depth →
      call (tag9 6 (c.query (rwrd s) f)) (packets s f) ∧ call (tag9 7 (packets s f)) (results s f) ∧
      ∃ (C : ℕ) (net : w3_Net (request c q s f) C), packets s f=w3_packet net ∧
        EncodesTruncPoly (w3_precision q) (w3_len q) (results s f) (BTNContract net.G net.T))
    (start : ∃ s, w3_InitTrace (w3_initRows q.FB q.M U) (w3_full q.M q.FB.totalCoords) s ∧
      Invariant z s ∧ ∀ {n out}, Runs call n (c.state 8 0 (rwrd s)) (packets s []) out →
        Runs call (n+2*c.size+5) c.i [] out)
    (update : ∀ (s : Rep), Invariant z s → ∀ X Y, q.FB.tupleVal Y=q.FB.tupleVal X+q.P →
      ¬w3_holds (w3_shiftRow q.FB q.M X Y) s.1 → ∃ t,
        w3_update (w3_shiftRow q.FB q.M X Y) s t ∧ 2*Nat.card (w3_coset t) ≤ Nat.card (w3_coset s) ∧
        call (tag9 8 (c.cutQ (rwrd s) (q.code X Y))) (rwrd t))
    (pass : w3_pass q.FB q.M q.P z) :
    ∃ y n, w3_Outcome q.FB q.M q.P U y ∧ n ≤ Nat.clog 2 (q.M^q.FB.totalCoords) ∧
      Runs call (2+n*(2*c.depth+3)+2*c.size+5) c.i [] (countWord (y q.FB.targetCoord).val) := by
  apply c.largeOutcome z U (fun s => packets s []) start
  · intro t _ hz
    obtain ⟨_,hc,C,net,he,hw⟩ := terminal t [] (Nat.zero_le _)
    rw [he] at hc ⊢
    exact c.zeroTarget net t q.FB.targetCoord target hm hmod hz hc hw
  · intro s hs hp
    obtain ⟨_,hc,C,net,he,hw⟩ := terminal s [] (Nat.zero_le _)
    have hbit : c.massBit (packets s []) (results s []) = true := by
      rw [he,c.massBit_eq net hm hmod hw]; exact decide_eq_true hp
    obtain ⟨t,hcut,next⟩ := c.positiveCut (q := root q s) s rfl fixed inj hM hm hmod hp hc hbit
      (fun f => packets s (f++[false])) (fun f => results s (f++[false]))
      (fun f hf => terminal s (f++[false]) (by simp; omega)) (update s hs)
    obtain ⟨X,Y,shift,_,_,hu,_⟩ := id hcut
    have ht := preserve hs.2 (pass X Y shift) hu
    exact ⟨t,hcut,ht,fun nextRun => next (terminal t [] (Nat.zero_le _)).1 nextRun⟩

end Trace
end DetDLP.M3D.Fast.ECRun.Assembly
open DetDLP DetDLP.M3D.Fast DetDLP.M3D.Fast.ECRun DetDLP.M3D.Fast.ECQueries DetDLP.M3D.Fast.ECRun.Context DetDLP.M3D.Fast.ECRun.Assembly DetDLP.M3D.Fast.NineOracleLoop DetDLP.M3D.Fast.Stage2Trace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    (∀ (call : ECRun.Wd → ECRun.Wd → Prop) (i o y : ECRun.Wd), i.headD true = true → DetDLP_M3D_dispatch i o = false →
     call (tag9 0 (DetDLP_M3D_orderQuery i)) o → call (tag9 1 i) y → Runs call 3 i [] y) ∧
    (∀ (c : Context) (q : w3_Query) (z : w3_Label q.M q.FB.totalCoords) (call : ECRun.Wd → ECRun.Wd → Prop)
    (U : Fin q.FB.totalCoords → q.FB.BlockTuple)
    (size : q.FB.totalCoords=c.size) (head : c.i.headD true=true) (large : DetDLP_M3D_dispatch c.i c.o=true)
    (order : call (tag9 0 (DetDLP_M3D_orderQuery c.i)) c.o)
    (plan : call (tag9 2 (curveWord c.i)) c.p) (enumerate : call (tag9 3 c.p) c.k)
    (u : ℕ → ECRun.Wd) (dec : ∀ j < c.size, call (tag9 5 (c.decQ j)) (u j))
    (gen : ∃ t, w3_update ((w3_initRows q.FB q.M U)[0]'(by simp [w3_initRows]))
        (w3_full q.M q.FB.totalCoords) t ∧ Stage2Trace.Invariant z t ∧ call (tag9 8 c.genQ) (repWord t))
    (step : ∀ j (hj : j<c.size) s, Stage2Trace.Invariant z s → ∃ t,
      w3_update ((w3_initRows q.FB q.M U)[j+1]'(by
        simpa only [w3_initRows,List.length_cons,List.length_map,List.length_finRange,Nat.succ_lt_succ_iff,size] using hj)) s t ∧
      Stage2Trace.Invariant z t ∧ call (tag9 8 (c.updQ j (repWord s) (u j))) (repWord t))
    (hm : c.blocks.length=q.m) (hmod : c.modulus=q.M) (hM : 2 ≤ q.M)
    (target : q.FB.targetCoord.val=c.blocks.flatten.length+1)
    (fixed : ∀ X Y, (q.code X Y).length=c.depth) (inj : Function.Injective (Function.uncurry q.code))
    (packets results : (w3_Rep q.M q.FB.totalCoords) → ECRun.Wd → ECRun.Wd)
    (terminal : ∀ (s : (w3_Rep q.M q.FB.totalCoords)) f, f.length ≤ c.depth →
      call (tag9 6 (c.query (repWord s) f)) (packets s f) ∧ call (tag9 7 (packets s f)) (results s f) ∧
      ∃ (C : ℕ) (net : w3_Net (request c q s f) C), packets s f=w3_packet net ∧
        EncodesTruncPoly (w3_precision q) (w3_len q) (results s f) (BTNContract net.G net.T))
    (update : ∀ (s : (w3_Rep q.M q.FB.totalCoords)), Invariant z s → ∀ X Y, q.FB.tupleVal Y=q.FB.tupleVal X+q.P →
      ¬w3_holds (w3_shiftRow q.FB q.M X Y) s.1 → ∃ t,
        w3_update (w3_shiftRow q.FB q.M X Y) s t ∧ 2*Nat.card (w3_coset t) ≤ Nat.card (w3_coset s) ∧
        call (tag9 8 (c.cutQ (repWord s) (q.code X Y))) (repWord t))
    (pass : w3_pass q.FB q.M q.P z),
    ∃ y n, w3_Outcome q.FB q.M q.P U y ∧ n ≤ Nat.clog 2 (q.M^q.FB.totalCoords) ∧
      Runs call (2+n*(2*c.depth+3)+2*c.size+5) c.i [] (countWord (y q.FB.targetCoord).val)) := by 
  constructor
  · intro call i o y; exact smallRun
  · intro c q z call U size head large order plan enumerate u dec gen step hm hmod hM target fixed inj pkt val terminal update pass
    apply concludeTrace c q z U hm hmod hM target fixed inj pkt val terminal _ update pass
    exact c.startRun z U (fun s => pkt s []) size head large order plan enumerate u dec gen step
      (fun s _ => (terminal s [] (Nat.zero_le _)).1)
