-- Prove2me | solution 1 for DetDLP.m89_four_call_word_composition_v2
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T18:59:28.834698+00:00
-- url     : https://prove2.me/submissions/ad58ae42-5342-45e9-b54b-604a6766c3e9

import Definitions.Def_DetDLP_M89_CompileSpace
import Definitions.Def_DetDLP_M89_MachineComp

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
namespace DetDLP.FC
noncomputable section
abbrev Tape := Turing.Tape (Option Bool)
abbrev Stmt := Turing.TM0.Stmt (Option Bool)
def act (t : Tape) : Stmt → Tape
  | .write s => t.write s
  | .move d => t.move d
structure Code (I : Type) where
  Q : Type
  finiteQ : Fintype Q
  start : Q
  scan : Q → I
  next : Q → Option Bool → Option Q × Stmt
attribute [instance] Code.finiteQ
variable {I : Type} [DecidableEq I]
abbrev Bank (I : Type) := I → Tape
def exec (P : Code I) : Option P.Q × Bank I → Option (Option P.Q × Bank I)
  | (none,_) => none
  | (some q,t) => let i := P.scan q; let r := P.next q (t i).head
                   some (r.1, Function.update t i (act (t i) r.2))
abbrev Run (P : Code I) (n : ℕ) (t u : Bank I) := Computation.Trace (exec P) n (some P.start,t) (none,u)
def seq (P R : Code I) : Code I where
  Q := P.Q ⊕ R.Q
  finiteQ := inferInstance
  start := .inl P.start
  scan := Sum.elim P.scan R.scan
  next := Sum.elim (fun q s => let r := P.next q s; (some (r.1.elim (.inr R.start) Sum.inl),r.2))
    (fun q s => let r := R.next q s; (r.1.map Sum.inr,r.2))
infixr:62 " ;; " => seq
private theorem sim {P R : Code I} (f : Option P.Q → Option R.Q)
    (g : P.Q → R.Q) (hg : ∀ q, f (some q) = some (g q))
    (hscan : ∀ q, R.scan (g q) = P.scan q)
    (hnext : ∀ q s, R.next (g q) s = (f (P.next q s).1,(P.next q s).2))
    {s e : Option P.Q × Bank I} {n : ℕ} (h : Computation.Trace (exec P) n s e) :
    Computation.Trace (exec R) n (f s.1,s.2) (f e.1,e.2) := by
  apply MachineComposition.Trace.map (fun c => (f c.1,c.2)) _ h
  rintro ⟨_|q,t⟩ b hb
  · simp [exec] at hb
  · simp [exec] at hb; subst b; simp [hg,exec,hscan,hnext]
theorem seq_run {P R : Code I} {t u v : Bank I} {n m : ℕ} (h : Run P n t u) (h' : Run R m u v) : Run (P ;; R) (n+m) t v := by
  let f := fun q : Option P.Q => some (q.elim (.inr R.start) Sum.inl)
  exact MachineComposition.Trace.append (sim (R:=P ;; R) f Sum.inl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) h)
    (sim (R:=P ;; R) (Option.map Sum.inr) Sum.inr (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) h')

def machine [Fintype I] (P : Code I) (input : I) : PrimitiveMachine where
  tapeCount := Fintype.card I
  inputTape := Fintype.equivFin I input
  stateCount := Fintype.card P.Q + 1
  start := (Fintype.equivFin P.Q P.start).castSucc
  scan := Fin.lastCases (Fintype.equivFin I input) (fun j => Fintype.equivFin I (P.scan ((Fintype.equivFin P.Q).symm j)))
  transition := Fin.lastCases (fun _ => .inl true) (fun j s => let r := P.next ((Fintype.equivFin P.Q).symm j) s
    .inr (r.1.elim (Fin.last _) (fun q => (Fintype.equivFin P.Q q).castSucc),r.2))
def packCfg [Fintype I] (P : Code I) (input : I) (c : Option P.Q × Bank I) : (machine P input).Cfg :=
  ⟨.inr (c.1.elim (Fin.last _) (fun q => (Fintype.equivFin P.Q q).castSucc)),c.2 ∘ (Fintype.equivFin I).symm⟩
theorem packTrace [Fintype I] (P : Code I) (input : I) {c d : Option P.Q × Bank I} {n : ℕ} (h : Computation.Trace (exec P) n c d) :
    Computation.Trace (machine P input).step n (packCfg P input c) (packCfg P input d) := by
  apply MachineComposition.Trace.map _ _ h
  rintro ⟨_|q,t⟩ d hd
  · simp [exec] at hd
  · simp [exec] at hd; subst d
    simp only [PrimitiveMachine.step,packCfg,machine,Option.elim_some,Fin.lastCases_castSucc,Equiv.symm_apply_apply,Function.comp_apply]
    cases hh : (P.next q (t (P.scan q)).head).2 <;> simp [hh,act,Function.update_comp_equiv]

def word (w : List Bool) : Tape := Turing.Tape.mk₁ (w.map some)
def initBank (input : I) (w : List Bool) : Bank I := fun i => if i = input then word w else word []
theorem rawRun [Fintype I] (P : Code I) (input out : I) {x y : List Bool} {t : Bank I} {n : ℕ}
    (h : Run P n (initBank input x) t) (ho : t out = word y) :
    RunsWithin (machine P input) (Fintype.equivFin I out) x y (n+1) ((Fintype.card I : ℝ)*(x.length+2*(n+1)+1)) := by
  let M := machine P input
  let last : M.Cfg := ⟨.inl true,t ∘ (Fintype.equivFin I).symm⟩
  have ht := packTrace P input h
  have hi : packCfg P input (some P.start,initBank input x) = (locatedInit M x).config := by
    unfold packCfg locatedInit PrimitiveMachine.init; congr 1; funext i; obtain ⟨j,rfl⟩ := (Fintype.equivFin I).surjective i
    simp [M,packCfg,machine,locatedInit,PrimitiveMachine.init,initBank,word]
  have he : M.step (packCfg P input (none,t)) = some last := by simp [M,PrimitiveMachine.step,packCfg,machine,last]
  have tr := MachineComposition.Trace.append ht (Computation.Trace.cons he (.refl _))
  rw [hi] at tr
  obtain ⟨d,hd,hd'⟩ := locatedTrace_lift tr
  apply (MachineComposition.runsWithin_iff_final_space ..).mpr
  refine ⟨_,d,hd,⟨true,by rw [hd']⟩,by rw [hd']; simpa [last,word] using ho,by push_cast; rfl,?_⟩
  exact_mod_cast locatedTrace_space_le_of_length hd

-- A linked call only scans tapes in the image of its block embedding.
def call (A : PrimitiveMachine) (j : Fin A.tapeCount ↪ I) : Code I where
  Q := Fin A.stateCount
  finiteQ := inferInstance
  start := A.start
  scan q := j (A.scan q)
  next q s := match A.transition q s with
    | .inl _ => (none,.write s)
    | .inr (q',a) => (some q',a)
private def ctrl {n : ℕ} : Bool ⊕ Fin n → Option (Fin n) := Sum.elim (fun _ => none) some
private theorem call_trace {A : PrimitiveMachine} (j : Fin A.tapeCount ↪ I) {c d : A.Cfg} {n : ℕ}
    (h : Computation.Trace A.step n c d) (t : Bank I) (ht : ∀ i, t (j i) = c.tapes i) :
    ∃ u, Computation.Trace (exec (call A j)) n (ctrl c.state,t) (ctrl d.state,u) ∧
      (∀ i, u (j i) = d.tapes i) ∧ ∀ i, (∀ l, j l ≠ i) → u i = t i := by
  induction h generalizing t with
  | refl => exact ⟨t,.refl _,ht,fun _ _ => rfl⟩
  | @cons n c b d hs _ ih =>
    cases hq : c.state with
    | inl v => simp [PrimitiveMachine.step,hq] at hs
    | inr q =>
      cases hh : A.transition q (c.tapes (A.scan q)).head with
      | inl v =>
        simp [PrimitiveMachine.step,hq,hh] at hs; subst b
        obtain ⟨u,hu,hu',hf⟩ := ih t ht
        rw [← ht] at hh
        exact ⟨u,.cons (by simp [exec,hq,ctrl,call,hh,act]) hu,hu',hf⟩
      | inr qa =>
        obtain ⟨q',a⟩ := qa
        simp [PrimitiveMachine.step,hq,hh] at hs; subst b
        let t' := Function.update t (j (A.scan q)) (act (t (j (A.scan q))) a)
        obtain ⟨u,hu,hu',hf⟩ := ih t' (by
          intro i; by_cases hi : i = A.scan q
          · subst i; cases a <;> simp [t',act,ht]
          · simp [t',hi,ht,Function.update_apply])
        refine ⟨u,.cons (by simp [exec,hq,ctrl,call,ht,hh,t']) hu,hu',?_⟩
        intro i hi; rw [hf i hi]; simp [t',Function.update_of_ne (Ne.symm (hi _))]

theorem call_run {A : PrimitiveMachine} (j : Fin A.tapeCount ↪ I) {o : Fin A.tapeCount} {x y : List Bool} {τ σ : ℝ}
    (h : RunsWithin A o x y τ σ) (t : Bank I) (ht : ∀ i, t (j i) = (A.init x).tapes i) :
    ∃ n u, Run (call A j) n t u ∧ (n : ℝ) ≤ τ ∧ u (j o) = word y ∧ ∀ i, (∀ l, j l ≠ i) → u i = t i := by
  obtain ⟨n,c,tr,⟨v,hv⟩,ho,hn,_⟩ := h
  obtain ⟨u,hu,hu',hf⟩ := call_trace j (locatedTrace_erase tr) t ht
  exact ⟨n,u,by simpa [hv,ctrl,locatedInit,PrimitiveMachine.init,call] using hu,hn,(hu' o).trans ho,hf⟩

-- Cursor represented by its reversed left part and its forward right part.
def cur (l r : List Bool) : Tape := Turing.Tape.mk₂ (l.map some) (r.map some)
@[simp] theorem cur_right (l r : List Bool) (b : Bool) : (cur l (b::r)).move .right = cur (b::l) r := by simp [cur,Turing.Tape.mk₂]
@[simp] theorem cur_left (l r : List Bool) (b : Bool) : (cur (b::l) r).move .left = cur l (b::r) := by rw [← cur_right,Turing.Tape.move_right_left]
@[simp] theorem cur_head (l r : List Bool) (b : Bool) : (cur l (b::r)).head = some b := rfl
@[simp] theorem cur_blank (l : List Bool) : (cur l []).head = none := rfl
@[simp] theorem cur_write (l : List Bool) (b : Bool) : (cur l []).write (some b) = cur l [b] := rfl
@[simp] theorem cur_at_left (r : List Bool) : ((cur [] r).move .left).head = none := rfl

def single (i : I) (a : Stmt) : Code I := ⟨Unit,inferInstance,(),fun _ => i,fun _ _ => (none,a)⟩
def emit (i : I) (b : Bool) := single i (.write (some b)) ;; single i (.move .right)
theorem single_run (t : Bank I) (i : I) (a : Stmt) : Run (single i a) 1 t (Function.update t i (act (t i) a)) := .cons rfl (.refl _)
theorem emit_run (t : Bank I) (i : I) (l : List Bool) (b : Bool) (h : t i = cur l []) :
    Run (emit i b) 2 t (Function.update t i (cur (b::l) [])) := by
  simpa [act,h,emit] using seq_run (single_run t i (.write (some b))) (single_run _ i (.move .right))

def rewind (i : I) : Code I where
  Q := Bool
  finiteQ := inferInstance
  start := false
  scan _ := i
  next q s := if q then if s.isNone then (none,.move .right) else (some false,.write s) else (some true,.move .left)
theorem rewind_run (i : I) (l r : List Bool) (t : Bank I) (h : t i = cur l r) :
    Run (rewind i) (2*l.length+2) t (Function.update t i (word (l.reverse ++ r))) := by
  induction l generalizing r t with
  | nil =>
    apply Computation.Trace.cons (b := (some true,Function.update t i ((cur [] r).move .left))) (by simp [exec,rewind,h,act])
    exact .cons (by simp [exec,rewind,act]; rfl) (.refl _)
  | cons b l ih =>
    let t' := Function.update t i (cur l (b::r))
    have h1 : exec (rewind i) (some false,t) = some (some true,t') := by simp [exec,rewind,act,t',h]
    have h2 : exec (rewind i) (some true,t') = some (some false,t') := by simp [exec,rewind,act,t']; rfl
    unfold Run; change Computation.Trace _ _ (some false,t) _
    simpa [t',Nat.mul_add,List.append_assoc,Nat.add_assoc] using Computation.Trace.cons h1 (.cons h2 (ih (b::r) t' (by simp [t'])))

def scan (i j : I) (fr : Bool) : Code I where
  Q := Option (Fin 4 × Bool)
  finiteQ := inferInstance
  start := none
  scan q := q.elim i (fun _ => j)
  next q s := match q with
    | none => match s with
      | none => (none,.write none)
      | some b => (some (some (if fr then 0 else 2,b)),.move .right)
    | some (q,b) => match q.val with
      | 0 => (some (some (1,b)),.write (some true))
      | 1 => (some (some (2,b)),.move .right)
      | 2 => (some (some (3,b)),.write (some b))
      | _ => (some none,.move .right)
def chunk (fr : Bool) (b : Bool) : List Bool := if fr then [true,b] else [b]
def rate (fr : Bool) : ℕ := if fr then 5 else 3
private theorem scan_bit (i j : I) (hne : i ≠ j) (fr b : Bool) (l r a : List Bool) (t : Bank I)
    (hi : t i = cur l (b::r)) (hj : t j = cur a []) :
    Computation.Trace (exec (scan i j fr)) (rate fr) (some none,t) (some none,
      Function.update (Function.update t i (cur (b::l) r)) j (cur ((chunk fr b).reverse ++ a) [])) := by
  cases fr <;> apply Computation.Trace.of_iterate <;>
    simp [rate,Function.iterate_succ_apply,exec,scan,act,hi,hj,hne,Ne.symm hne,chunk]
private theorem scan_loop (i j : I) (hne : i ≠ j) (fr : Bool) (r l a : List Bool) (t : Bank I)
    (hi : t i = cur l r) (hj : t j = cur a []) :
    ∃ u, Run (scan i j fr) (rate fr*r.length+1) t u ∧ u i = cur (r.reverse ++ l) [] ∧
      u j = cur ((r.flatMap (chunk fr)).reverse ++ a) [] ∧ ∀ z, z ≠ i → z ≠ j → u z = t z := by
  induction r generalizing l a t with
  | nil =>
    refine ⟨t,?_,by simpa using hi,by simpa using hj,fun _ _ _ => rfl⟩
    simp only [List.length_nil,Nat.mul_zero,Nat.zero_add]; apply Computation.Trace.cons (b := (none,t)) _ (.refl _)
    change exec (scan i j fr) (some none,t) = some (none,t)
    have hw : (t i).write none = t i := by rw [← show (t i).head = none by rw [hi,cur_blank],Turing.Tape.write_self]
    simp [exec,scan,show (t i).head = none by rw [hi,cur_blank],act,hw]
  | cons b r ih =>
    let t' := Function.update (Function.update t i (cur (b::l) r)) j (cur ((chunk fr b).reverse ++ a) [])
    obtain ⟨u,h,h1,h2,h3⟩ := ih (b::l) ((chunk fr b).reverse ++ a) t' (by simp [t',hne]) (by simp [t'])
    refine ⟨u,?_,by simpa [List.append_assoc] using h1,by simpa [List.append_assoc] using h2,?_⟩
    · have tr := MachineComposition.Trace.append (scan_bit i j hne fr b l r a t hi hj) h
      simpa [Run,scan,Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,t'] using tr
    · intro z zi zj; simpa [t',zi,zj] using h3 z zi zj

def copy (i j : I) := scan i j false ;; rewind i ;; rewind j
private theorem copy_run (i j : I) (hne : i ≠ j) (w : List Bool) (t : Bank I) (hi : t i = word w) (hj : t j = word []) :
    ∃ u, Run (copy i j) (7*w.length+5) t u ∧ u j = word w ∧ ∀ z, z ≠ j → u z = t z := by
  obtain ⟨u,h,h1,h2,h3⟩ := scan_loop i j hne false w [] [] t hi hj
  have flat (v : List Bool) : v.flatMap (chunk false) = v := by induction v <;> simp_all [chunk]
  simp [flat] at h1 h2
  have s1 := rewind_run i w.reverse [] u h1
  let v := Function.update u i (word w)
  have s1' : Run (rewind i) (2*w.length+2) u v := by simpa [v] using s1
  have s2 := rewind_run j w.reverse [] v (by simp [v,Ne.symm hne,h2])
  let z := Function.update v j (word w)
  have s2' : Run (rewind j) (2*w.length+2) v z := by simpa [z] using s2
  refine ⟨z,?_,by simp [z],?_⟩
  · convert seq_run h (seq_run s1' s2') using 1 <;> simp [copy,rate] <;> omega
  · intro k hk; by_cases hi' : k = i
    · subst k; simp [z,v,hk,hi]
    · simp [z,v,hk,hi',h3 k hi' hk]

def block (i j : I) := emit j true ;; scan i j true ;; emit j false
def atom (w : List Bool) := true :: Encoding.frame w
private theorem frame_eq (w : List Bool) : Encoding.frame w = w.flatMap (chunk true) ++ [false] := by induction w <;> simp_all [Encoding.frame,chunk,List.foldr]
private theorem block_run (i j : I) (hne : i ≠ j) (w acc : List Bool) (t : Bank I) (hi : t i = word w) (hj : t j = cur acc.reverse []) :
    ∃ u, Run (block i j) (5*w.length+5) t u ∧ u j = cur (acc ++ atom w).reverse [] ∧ ∀ z, z ≠ i → z ≠ j → u z = t z := by
  let t' := Function.update t j (cur (true::acc.reverse) [])
  have h := emit_run t j acc.reverse true hj
  obtain ⟨v,hv,_,hvj,hf⟩ := scan_loop i j hne true w [] (true::acc.reverse) t' (by rw [show t' i = t i by simp [t',hne]]; exact hi) (by simp [t'])
  let l := (w.flatMap (chunk true)).reverse ++ true :: acc.reverse
  have he := emit_run v j l false hvj
  refine ⟨Function.update v j (cur (false::l) []),?_,?_,?_⟩
  · convert seq_run h (seq_run hv he) using 1 <;> simp [block,rate] <;> omega
  · simp [l,atom,frame_eq,List.append_assoc]
  · intro z zi zj; simp [zj,hf z zi zj,t']
def framing (x a d dst : I) := block x dst ;; block a dst ;; block d dst ;; emit dst false ;; rewind dst
private theorem framing_run (x a d j : I) (hx : x ≠ j) (ha : a ≠ j) (hd : d ≠ j) (hax : a ≠ x) (hdx : d ≠ x) (hda : d ≠ a)
    (X A D : List Bool) (t : Bank I) (tx : t x = word X) (ta : t a = word A) (td : t d = word D) (tj : t j = word []) :
    let p := Encoding.encodeList id [X,A,D]
    ∃ u, Run (framing x a d j) (5*(X.length+A.length+D.length)+2*p.length+19) t u ∧ u j = word p ∧
      ∀ z, z ≠ x → z ≠ a → z ≠ d → z ≠ j → u z = t z := by
  intro p
  obtain ⟨u,h1,uj,uf⟩ := block_run x j hx X [] t tx tj
  obtain ⟨v,h2,vj,vf⟩ := block_run a j ha A (atom X) u (by rw [uf a hax ha,ta]) (by simpa using uj)
  obtain ⟨s,h3,sj,sf⟩ := block_run d j hd D (atom X ++ atom A) v (by rw [vf d hda hd,uf d hdx hd,td]) vj
  let l := ((atom X ++ atom A) ++ atom D).reverse
  have h4 := emit_run s j l false sj
  have he : false :: l = p.reverse := by simp [l,p,Encoding.encodeList,atom,List.append_assoc]
  rw [he] at h4
  let v' := Function.update s j (cur p.reverse [])
  have h5 := rewind_run j p.reverse [] v' (by simp [v'])
  refine ⟨Function.update v' j (word (p.reverse.reverse ++ [])),?_,by simp,?_⟩
  · convert seq_run h1 (seq_run h2 (seq_run h3 (seq_run h4 h5))) using 1 <;> simp [framing] <;> omega
  · intro z zx za zd zj; simp [v',zj,sf z zd zj,vf z za zj,uf z zx zj]

section Driver
variable (A B D E : PrimitiveMachine)
abbrev Ports := Unit ⊕ Fin A.tapeCount ⊕ Fin B.tapeCount ⊕ Fin D.tapeCount ⊕ Fin E.tapeCount
abbrev src : Ports A B D E := .inl ()
def ja : Fin A.tapeCount ↪ Ports A B D E := ⟨fun i => .inr (.inl i),by simp [Function.Injective]⟩
def jb : Fin B.tapeCount ↪ Ports A B D E := ⟨fun i => .inr (.inr (.inl i)),by simp [Function.Injective]⟩
def jd : Fin D.tapeCount ↪ Ports A B D E := ⟨fun i => .inr (.inr (.inr (.inl i))),by simp [Function.Injective]⟩
def je : Fin E.tapeCount ↪ Ports A B D E := ⟨fun i => .inr (.inr (.inr (.inr (i)))),by simp [Function.Injective]⟩
variable (oa : Fin A.tapeCount) (ob : Fin B.tapeCount) (od : Fin D.tapeCount)
local notation "X0" => src A B D E
local notation "JA" => ja A B D E
local notation "JB" => jb A B D E
local notation "JD" => jd A B D E
local notation "JE" => je A B D E
def driver := copy X0 (JA A.inputTape) ;; copy X0 (JB B.inputTape) ;; call A JA ;; call B JB ;; copy (JB ob) (JD D.inputTape) ;; call D JD ;; framing X0 (JA oa) (JD od) (JE E.inputTape) ;; call E JE
private theorem driver_run (oe : Fin E.tapeCount) {x a b d e : List Bool} {W : ℝ}
    (hA : RunsWithin A oa x a (W+1) (W+1)) (hB : RunsWithin B ob x b (W+1) (W+1))
    (hD : RunsWithin D od b d ((W+1)*(b.length+1)) ((W+1)*(b.length+1)))
    (hE : RunsWithin E oe (Encoding.encodeList id [x,a,d]) e ((W+1)*((Encoding.encodeList id [x,a,d]).length+1)) ((W+1)*((Encoding.encodeList id [x,a,d]).length+1))) :
    let p := Encoding.encodeList id [x,a,d]
    ∃ n t, Run (driver A B D E oa ob od) n (initBank X0 x) t ∧ t (JE oe) = word e ∧
      (n : ℝ) ≤ 14*x.length+7*b.length+5*(x.length+a.length+d.length)+2*p.length+34 + (W+1)*(4+b.length+p.length) := by
  intro p
  let t := initBank X0 x
  obtain ⟨u,h1,ua,uf⟩ := copy_run X0 (JA A.inputTape) (by simp [src,ja]) x t (by simp [t,initBank]) (by simp [t,initBank,src,ja])
  obtain ⟨v,h2,vb,vf⟩ := copy_run X0 (JB B.inputTape) (by simp [src,jb]) x u (by rw [uf]; all_goals simp [t,initBank,src,ja]) (by rw [uf]; all_goals simp [t,initBank,src,ja,jb])
  obtain ⟨na,r,h3,hna,ra,rf⟩ := call_run JA hA v (by
    intro i; rw [vf _ (by simp [ja,jb])]; by_cases hi : i = A.inputTape
    · simpa [hi,PrimitiveMachine.init,word] using ua
    · rw [uf _ (by simpa using hi)]; simp [t,initBank,PrimitiveMachine.init,hi,src,ja,word])
  obtain ⟨nb,s,h4,hnb,sb,sf⟩ := call_run JB hB r (by
    intro i; rw [rf _ (by simp [ja,jb])]; by_cases hi : i = B.inputTape
    · simpa [hi,PrimitiveMachine.init,word] using vb
    · rw [vf _ (by simpa using hi),uf _ (by simp [ja,jb])]; simp [t,initBank,PrimitiveMachine.init,hi,src,jb,word])
  obtain ⟨y,h5,yd,yf⟩ := copy_run (JB ob) (JD D.inputTape) (by simp [jb,jd]) b s sb (by
    rw [sf _ (by simp [jb,jd]),rf _ (by simp [ja,jd]),vf _ (by simp [jb,jd]),uf _ (by simp [ja,jd])]; simp [t,initBank,src,jd])
  obtain ⟨nd,z,h6,hnd,zd,zf⟩ := call_run JD hD y (by
    intro i; by_cases hi : i = D.inputTape
    · simpa [hi,PrimitiveMachine.init,word] using yd
    · rw [yf _ (by simpa using hi),sf _ (by simp [jb,jd]),rf _ (by simp [ja,jd]),vf _ (by simp [jb,jd]),uf _ (by simp [ja,jd])]; simp [t,initBank,PrimitiveMachine.init,hi,src,jd,word])
  have zE (i) : z (JE i) = word [] := by
    rw [zf _ (by simp [je,jd]),yf _ (by simp [je,jd]),sf _ (by simp [je,jb]),rf _ (by simp [je,ja]),vf _ (by simp [je,jb]),uf _ (by simp [je,ja])]; simp [t,initBank,src,je]
  obtain ⟨w,h7,we,wf⟩ := framing_run X0 (JA oa) (JD od) (JE E.inputTape) (by simp [src,je]) (by simp [ja,je]) (by simp [jd,je]) (by simp [src,ja]) (by simp [src,jd]) (by simp [jd,ja]) x a d z (by
    rw [zf _ (by simp [src,jd]),yf _ (by simp [src,jd]),sf _ (by simp [src,jb]),rf _ (by simp [src,ja]),vf _ (by simp [src,jb]),uf _ (by simp [src,ja])]; simp [t,initBank]) (by
    rw [zf _ (by simp [jd,ja]),yf _ (by simp [jd,ja]),sf _ (by simp [jb,ja]),ra]) zd (zE _)
  obtain ⟨ne,f,h8,hne,fe,_⟩ := call_run JE hE w (by
    intro i; by_cases hi : i = E.inputTape
    · simpa [hi,PrimitiveMachine.init,word] using we
    · rw [wf _ (by simp [src,je]) (by simp [je,ja]) (by simp [je,jd]) (by simpa using hi),zE]; simp [PrimitiveMachine.init,hi,word])
  refine ⟨_,f,seq_run h1 (seq_run h2 (seq_run h3 (seq_run h4 (seq_run h5 (seq_run h6 (seq_run h7 h8)))))),fe,?_⟩
  push_cast; dsimp [p]; linarith
end Driver
private def Bounded (t : Turing.Tape (Option Bool)) (n : ℕ) := ∀ j : ℕ, n ≤ j → t.nth (j:ℤ) = none
private theorem atInit (w : List Bool) : Bounded (Turing.Tape.mk₁ (w.map some)) w.length := by
  intro j hj
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.ListBlank.nth_mk,List.getI_eq_default _ (by simpa using hj : (w.map some).length ≤ j)]
  rfl
private theorem one {A : PrimitiveMachine} {a b : A.Cfg} {n : ℕ}
    (ha : ∀ i, Bounded (a.tapes i) n) (hs : A.step a = some b) : ∀ i, Bounded (b.tapes i) (n+1) := by
  cases hq : a.state with
  | inl v => simp [PrimitiveMachine.step,hq] at hs
  | inr q =>
    cases hh : A.transition q (a.tapes (A.scan q)).head with
    | inl v =>
      simp [PrimitiveMachine.step,hq,hh] at hs; subst b; exact fun i j hj => ha i j (by omega)
    | inr qa =>
      obtain ⟨q',action⟩ := qa
      simp [PrimitiveMachine.step,hq,hh] at hs; subst b
      intro i j hj
      by_cases hi : i = A.scan q
      · subst i; simp only [Function.update_self]
        cases action with
        | write s => rw [Turing.Tape.write_nth,if_neg (by omega)]; exact ha _ _ (by omega)
        | move dir => cases dir with
          | left => rw [Turing.Tape.move_left_nth,show (j:ℤ)-1 = ((j-1:ℕ):ℤ) by omega]; exact ha _ _ (by omega)
          | right => rw [Turing.Tape.move_right_nth,show (j:ℤ)+1 = ((j+1:ℕ):ℤ) by omega]; exact ha _ _ (by omega)
      · simpa only [Function.update_of_ne hi] using ha i j (by omega : n ≤ j)
private theorem many {A : PrimitiveMachine} {a b : A.Cfg} {k : ℕ} (h : Computation.Trace A.step k a b) {n : ℕ}
    (ha : ∀ i, Bounded (a.tapes i) n) : ∀ i, Bounded (b.tapes i) (n+k) := by
  induction h generalizing n with
  | refl => simpa using ha
  | cons hs _ ih => simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (one ha hs)

theorem output_length {A : PrimitiveMachine} {o : Fin A.tapeCount} {x y : List Bool} {t s : ℝ}
    (h : RunsWithin A o x y t s) : (y.length : ℝ) ≤ x.length + t := by
  obtain ⟨k,c,tr,_,ho,ht,_⟩ := h
  have h0 (i) : Bounded ((locatedInit A x).config.tapes i) x.length := by
    simp only [locatedInit,PrimitiveMachine.init]; split_ifs
    · exact atInit x
    · exact fun j _ => atInit [] j (by simp)
  have hb := many (locatedTrace_erase tr) h0 o
  rw [ho] at hb
  have hl : y.length ≤ x.length+k := by
    by_contra! hlt
    have he := hb _ (le_refl _)
    simp only [Turing.Tape.mk₁,Turing.Tape.mk₂,Turing.Tape.mk'_nth_nat,Turing.ListBlank.nth_mk] at he
    rw [List.getI_eq_getElem _ (by simpa using hlt)] at he
    simp at he
  have hc : (y.length : ℝ) ≤ x.length + k := by exact_mod_cast hl
  linarith


private theorem input_le_budget {M : PrimitiveMachine} {o : Fin M.tapeCount} {x y : List Bool} {τ σ : ℝ} (h : RunsWithin M o x y τ σ) : (x.length : ℝ) ≤ σ := by
  obtain ⟨n,c,tr,hh,ho,hn,hs⟩ := h
  have hv := hs 0 _ (Nat.zero_le _) (.refl _)
  apply le_trans _ hv
  exact_mod_cast (show x.length ≤ visitedSpace (locatedInit M x) by
    unfold visitedSpace
    apply le_trans _ (Finset.single_le_sum (f := fun i => ((locatedInit M x).upper i - (locatedInit M x).lower i + 1).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ M.inputTape))
    simp [locatedInit]; omega)
private theorem scale_ge_one {b : ℕ} (hb : 1 ≤ b) : 1 ≤ (b : ℝ) / (logSafe b)^((1:ℝ)/4) := by
  have hbr : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hl : logSafe b ≤ (b:ℝ) := by
    apply max_le hbr
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mpr
    rw [Real.rpow_natCast]; apply max_le
    · exact_mod_cast (show 2 ≤ 2^b by exact le_trans (by decide : 2 ≤ 2^1) (Nat.pow_le_pow_right (by decide) hb))
    · exact_mod_cast (show b < 2^b from Nat.lt_two_pow_self).le
  have hg : 1 ≤ logSafe (b:ℝ) := le_max_left _ _
  have hp : (logSafe (b:ℝ))^((1:ℝ)/4) ≤ logSafe b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hg (by norm_num : (1:ℝ)/4 ≤ 1)
  apply (one_le_div (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hg) _)).mpr
  exact hp.trans hl
private theorem absorb (K k b : ℕ) (hb : 1 ≤ b) : (K:ℝ) * (mainSpaceBound k b)^3 ≤ mainSpaceBound (K+3*k) b := by
  let s := (b:ℝ)/(logSafe b)^((1:ℝ)/4)
  have hs : 1 ≤ s := scale_ge_one hb
  have rwW (j : ℕ) : mainSpaceBound j b = (2:ℝ)^((j:ℝ)*s) := by unfold mainSpaceBound s; congr 1; ring
  rw [rwW,rwW,← Real.rpow_mul_natCast (by norm_num)]
  have hK : (K:ℝ) ≤ (2:ℝ)^((K:ℝ)*s) := by
    calc (K:ℝ) ≤ (2:ℝ)^(K:ℝ) := by rw [Real.rpow_natCast]; exact_mod_cast (show K < 2^K from Nat.lt_two_pow_self).le
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α:=ℝ) K])
  calc _ ≤ (2:ℝ)^((K:ℝ)*s) * (2:ℝ)^((k:ℝ)*s*(3:ℕ)) := mul_le_mul_of_nonneg_right hK (by positivity)
       _ = _ := by rw [← Real.rpow_add (by norm_num)]; push_cast; congr 1; ring
private theorem pack_length (x a d : List Bool) : (Encoding.encodeList id [x,a,d]).length = 2*(x.length+a.length+d.length)+7 := by
  have hf (v : List Bool) : (Encoding.frame v).length = 2*v.length+1 := by
    induction v with
    | nil => rfl
    | cons b v ih => change (Encoding.frame v).length+1+1 = 2*(v.length+1)+1; omega
  simp [Encoding.encodeList,hf]; omega

end
end DetDLP.FC
open DetDLP.FC

theorem solution
    (A : PrimitiveMachine) (oa : Fin A.tapeCount) (B : PrimitiveMachine) (ob : Fin B.tapeCount)
    (D : PrimitiveMachine) (od : Fin D.tapeCount) (E : PrimitiveMachine) (oe : Fin E.tapeCount)
    (k : ℕ) : ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (c : ℕ),
      ∀ (p : ℕ), 2 ≤ p → ∀ (x a b d e : List Bool), x.length ≤ bitLen p + 2 →
        let W := mainSpaceBound k (bitLen p)
        let pack := Encoding.encodeList id [x,a,d]
        RunsWithin A oa x a (W+1) (W+1) → RunsWithin B ob x b (W+1) (W+1) →
        RunsWithin D od b d ((W+1)*(b.length+1)) ((W+1)*(b.length+1)) →
        RunsWithin E oe pack e ((W+1)*(pack.length+1)) ((W+1)*(pack.length+1)) →
        RunsWithin M o x e (mainSpaceBound c (bitLen p)) (mainSpaceBound c (bitLen p)) := by
  classical
  let I := Ports A B D E
  let T := Fintype.card I
  let K := 2000*(T+1)
  let P := driver A B D E oa ob od
  refine ⟨machine P (src A B D E),Fintype.equivFin I (je A B D E oe),K+3*k,?_⟩
  intro p hp x a b d e _ W pack hA hB hD hE
  have hW : 1 ≤ W := by
    apply Real.one_le_rpow; norm_num
    have hlog : (0:ℝ) ≤ logSafe (bitLen p) := le_trans zero_le_one (le_max_left _ _)
    positivity
  have hx := input_le_budget hA
  have ha := output_length hA
  have hb := output_length hB
  have hd := output_length hD
  have w2 : W ≤ W^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hW) (zero_le_one.trans hW)]
  have w3 : W^2 ≤ W^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hW) (sq_nonneg W)]
  have hx' : (x.length : ℝ) ≤ 2*W := by linarith
  have ha' : (a.length : ℝ) ≤ 4*W := by linarith
  have hb' : (b.length : ℝ) ≤ 4*W := by linarith
  have hmul : (W+1)*(b.length+1) ≤ (2*W)*(5*W) := by gcongr <;> linarith
  have hd' : (d.length : ℝ) ≤ 14*W^2 := by linarith
  have hpk : (pack.length : ℝ) = 2*(x.length+a.length+d.length)+7 := by exact_mod_cast pack_length x a d
  have hpk' : (pack.length : ℝ) ≤ 47*W^2 := by linarith
  obtain ⟨n,t,hr,ho,hn⟩ := driver_run A B D E oa ob od oe hA hB hD hE
  change (n:ℝ) ≤ 14*x.length+7*b.length+5*(x.length+a.length+d.length)+2*pack.length+34+(W+1)*(4+b.length+pack.length) at hn
  have hmul' : (W+1)*(4+b.length+pack.length) ≤ (2*W)*(55*W^2) := by gcongr <;> linarith
  have hn' : (n:ℝ)+1 ≤ 500*W^3 := by nlinarith only [hn,hmul',hx',ha',hb',hd',hpk',hW,w2,w3]
  have hbound : (K:ℝ)*W^3 ≤ mainSpaceBound (K+3*k) (bitLen p) := absorb K k _ (Nat.clog_pos (by decide) hp)
  have hK : (K:ℝ) = 2000*((T:ℝ)+1) := by simp [K]
  have ht := rawRun P (src A B D E) (je A B D E oe) hr ho
  apply MachineComposition.runsWithin_mono ht
  · apply le_trans hn' (le_trans _ hbound); gcongr; rw [hK]; linarith [Nat.cast_nonneg (α:=ℝ) T]
  · apply le_trans _ hbound
    change (T:ℝ)*(x.length+2*(n+1)+1) ≤ _
    have hw : 0 ≤ W^3 := by positivity
    calc _ ≤ (T:ℝ)*(2000*W^3) := by gcongr; linarith
         _ ≤ _ := by rw [hK]; nlinarith only [hw]

#print axioms solution





