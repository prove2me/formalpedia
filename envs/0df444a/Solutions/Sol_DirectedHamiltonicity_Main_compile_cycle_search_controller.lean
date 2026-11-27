-- Prove2me | solution 1 for DirectedHamiltonicity.Main.compile_cycle_search_controller
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:37:51.404866+00:00
-- url     : https://prove2.me/submissions/e4b00659-8e5e-4de9-962d-9cff519e7019

import Definitions.Def_LogCostRAM_StructuredExecution
import Definitions.Def_DirectedHamiltonicity_CycleController
import Theorems.Thm_TargetedSamplers_Structured_bounded_bit_subroutine

namespace TargetedSamplers.Structured

theorem Exec.post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

theorem Store.write_fits {s : Store} {width v : ℕ} (h : s.Fits width) (d : ℕ) (hv : v.size ≤ width) :
    (s.write d v).Fits width := by
  intro a
  by_cases he : a = d
  · simpa [Store.write, he] using hv
  · simpa [Store.write, he] using h a

@[simp] theorem Store.write_overwrite (s : Store) (a x y : ℕ) : (s.write a x).write a y = s.write a y := by
  simp [Store.write]

def Op.written (τ : Tapes) (s : Store) : Op → ℕ
  | .const _ c => c
  | .add _ a b => s.mem a + s.mem b
  | .sub _ a b => s.mem a - s.mem b
  | .load _ a => s.mem (s.mem a)
  | .store _ b => s.mem b
  | .input _ a => bitVal τ.input[s.mem a]?
  | .coin _ a => bitVal τ.coins[s.mem a]?
  | .output _ => 0

theorem Op.eval_fits (p : Op) (τ : Tapes) {s : Store} {b : ℕ}
    (hi : s.Fits b) (hw : (p.written τ s).size ≤ b) : (p.eval τ s).Fits b := by
  cases p <;> first | exact Store.write_fits hi _ hw | exact hi

structure Result where
  last : Store
  steps : ℕ
  writeWidth : ℕ

/-- Evaluation charges the actual control transfers and records the largest value written. -/
def Fragment.run (τ : Tapes) (s : Store) : Fragment → Result
  | .skip => ⟨s,0,0⟩
  | .op o => ⟨o.eval τ s,1,(o.written τ s).size⟩
  | .seq x y =>
    let p := x.run τ s
    let q := y.run τ p.last
    ⟨q.last,p.steps+q.steps,max p.writeWidth q.writeWidth⟩
  | .branch a b yes no =>
    if s.mem a ≤ s.mem b then
      let p := yes.run τ s
      ⟨p.last,1+p.steps,p.writeWidth⟩
    else
      let p := no.run τ s
      ⟨p.last,1+p.steps+1,p.writeWidth⟩

theorem Fragment.exec (f : Fragment) (τ : Tapes) (s : Store) (b : ℕ)
    (hs : s.Fits b) (hw : (f.run τ s).writeWidth ≤ b) :
    Exec τ (fun st => st.Fits b) f.cmd s (f.run τ s).last (f.run τ s).steps := by
  induction f generalizing s with
  | skip => exact .skip s
  | op o => exact .op s o (o.eval_fits τ hs hw)
  | seq x y ix iy =>
    obtain ⟨hx,hy⟩ := max_le_iff.mp hw
    have first := ix s hs hx
    exact .seq first (iy _ (first.post hs) hy)
  | branch a b y n iy ino =>
    by_cases h : s.mem a ≤ s.mem b
    · simp only [run,h,if_true] at hw ⊢
      exact .yes h (iy s hs hw)
    · simp only [run,h,if_false] at hw ⊢
      exact .no h (ino s hs hw)


end TargetedSamplers.Structured

namespace TargetedSamplers.Structured

@[simp] theorem Cmd.compile_length (c : Cmd) (pc : ℕ) : (c.compile pc).length = c.len := by
  induction c generalizing pc <;> simp_all [compile, len] <;> omega

/-- A block may be embedded between arbitrary instructions. All internal jump labels are absolute. -/
def Contains (P : Program) (pc : ℕ) (code : Program) : Prop :=
  ∃ pre post : Program, pre.length = pc ∧ P = pre ++ code ++ post

theorem Contains.left {P pc x y} (h : Contains P pc (x++y)) : Contains P pc x := by
  obtain ⟨pre,post,hpc,hP⟩ := h
  exact ⟨pre, y++post, hpc, by simpa [List.append_assoc] using hP⟩

theorem Contains.right {P pc x y} (h : Contains P pc (x++y)) : Contains P (pc+x.length) y := by
  obtain ⟨pre,post,hpc,hP⟩ := h
  exact ⟨pre++x, post, by simp [hpc], by simpa [List.append_assoc] using hP⟩

theorem Contains.one {P pc i} (h : Contains P pc [i]) : P[pc]? = some i := by
  obtain ⟨pre,post,hpc,hP⟩ := h
  rw [hP, ← hpc, List.append_assoc, List.getElem?_append_right (by omega)]
  simp

/-- A live, ordinary machine state at the specified instruction, memory and output. -/
structure Located (st : State) (pc : ℕ) (s : Store) : Prop where
  counter : st.pc = pc
  live : st.halted = false
  normal : st.bot = false
  memory : st.mem = s.mem
  output : st.out = s.out

theorem step_op {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]? = some p.instruction) : Located (P.step τ st) (pc+1) (p.eval τ s) := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  cases p <;> constructor <;> simp_all [Op.instruction, Op.eval, Program.step, State.write, Store.write]

theorem step_jle {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (a b dst : ℕ) (hp : P[pc]? = some (.jle a b dst)) :
    Located (P.step τ st) (if s.mem a ≤ s.mem b then dst else pc+1) s := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  constructor <;> simp [Program.step, hc, hh, hb, hm, ho, hp]

theorem step_jump {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (dst : ℕ) (hp : P[pc]? = some (jump dst)) : Located (P.step τ st) dst s := by
  simpa using step_jle τ h 0 0 dst hp

theorem branch_sites {P pc a b y n} (h : Contains P pc ((Cmd.branch a b y n).compile pc)) :
    P[pc]? = some (.jle a b (pc+1+n.len+1)) ∧ Contains P (pc+1) (n.compile (pc+1)) ∧
    P[pc+1+n.len]? = some (jump (pc+1+n.len+1+y.len)) ∧
    Contains P (pc+1+n.len+1) (y.compile (pc+1+n.len+1)) := by
  unfold Cmd.compile at h
  exact ⟨h.left.one, h.right.left, by simpa using h.right.right.left.one, by simpa using h.right.right.right⟩

theorem loop_sites {P pc a b body} (h : Contains P pc ((Cmd.whileGt a b body).compile pc)) :
    P[pc]? = some (.jle a b (pc+1+body.len+1)) ∧ Contains P (pc+1) (body.compile (pc+1)) ∧
    P[pc+1+body.len]? = some (jump pc) := by
  unfold Cmd.compile at h
  exact ⟨h.left.one, h.right.left, by simpa using h.right.right.one⟩


end TargetedSamplers.Structured

namespace TargetedSamplers.Structured

/-- Log-cost of a data instruction with its actual operands. This expression is independent
of the bit widths of registers that the instruction never inspects. -/
def Op.charge (τ : Tapes) (s : Store) : Op → ℕ
  | .const d c => 1+d.size+c.size
  | .add d a b => 1+d.size+a.size+b.size+(s.mem a).size+(s.mem b).size+(s.mem a+s.mem b).size
  | .sub d a b => 1+d.size+a.size+b.size+(s.mem a).size+(s.mem b).size+(s.mem a-s.mem b).size
  | .load d a => 1+d.size+a.size+(s.mem a).size+(s.mem (s.mem a)).size
  | .store a b => 1+a.size+b.size+(s.mem a).size+(s.mem b).size
  | .input d a => 1+d.size+a.size+(s.mem a).size+(bitVal τ.input[s.mem a]?).size
  | .coin d a => 1+d.size+a.size+(s.mem a).size+(bitVal τ.coins[s.mem a]?).size
  | .output a => 1+a.size+(s.mem a).size

def testCharge (s : Store) (a b dst : ℕ) := 1+a.size+b.size+(s.mem a).size+(s.mem b).size+dst.size

/-- Exact bit cost of a loop-free structured block relocated to an absolute program address. -/
def Fragment.charge (τ : Tapes) (s : Store) (pc : ℕ) : Fragment → ℕ
  | .skip => 0
  | .op o => o.charge τ s
  | .seq x y => x.charge τ s pc + y.charge τ (x.run τ s).last (pc+x.cmd.len)
  | .branch a b y n =>
    let yesPC := pc+1+n.cmd.len+1
    testCharge s a b yesPC +
      if s.mem a ≤ s.mem b then y.charge τ s yesPC
      else n.charge τ s (pc+1) + testCharge (n.run τ s).last 0 0 (yesPC+y.cmd.len)

def Travels (P : Program) (τ : Tapes) (s t : State) (steps cost : ℕ) : Prop :=
  (P.step τ)^[steps] s=t ∧ t.work=s.work+cost

theorem Travels.trans {P τ s m t k j a b} (e : Travels P τ s m k a) (f : Travels P τ m t j b) :
    Travels P τ s t (k+j) (a+b) := by
  constructor
  · rw [Nat.add_comm k j,Function.iterate_add_apply,e.1,f.1]
  · rw [f.2,e.2,Nat.add_assoc]

theorem op_travels {P : Program} {τ : Tapes} {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]?=some p.instruction) :
    Travels P τ st (P.step τ st) 1 (p.charge τ s) := by
  refine ⟨rfl,?_⟩
  obtain ⟨hc,live,_,mem,_⟩ := h
  cases p <;> simp_all [Program.step,Op.instruction,Op.charge,Nat.add_assoc]

theorem test_travels {P : Program} {τ : Tapes} {st pc s} (h : Located st pc s)
    (a b dst : ℕ) (hp : P[pc]?=some (.jle a b dst)) :
    Travels P τ st (P.step τ st) 1 (testCharge s a b dst) := by
  refine ⟨rfl,?_⟩
  simp [Program.step,h.counter,h.live,hp,h.memory,testCharge,Nat.add_assoc]

/-- The machine-level accounting matches every executed instruction, including branch jumps,
when unrelated memory cells may hold arbitrarily long words. -/
theorem Fragment.compile_charge (f : Fragment) (P : Program) (τ : Tapes) (pc : ℕ) (st : State)
    (s : Store) (sub : Contains P pc (f.cmd.compile pc)) (loc : Located st pc s) :
    ∃ t, Travels P τ st t (f.run τ s).steps (f.charge τ s pc) ∧
      Located t (pc+f.cmd.len) (f.run τ s).last := by
  induction f generalizing pc st s with
  | skip => exact ⟨st,⟨rfl,by simp [charge]⟩,by simpa [cmd,Cmd.len,run] using loc⟩
  | op o => exact ⟨_,op_travels loc o sub.one,step_op τ loc o sub.one⟩
  | seq x y ix iy =>
    obtain ⟨m,hx,mLoc⟩ := ix pc st s sub.left loc
    obtain ⟨t,hy,stop⟩ := iy (pc+x.cmd.len) m (x.run τ s).last (by simpa using sub.right) mLoc
    exact ⟨t,hx.trans hy,by simpa [cmd,Cmd.len,run,Nat.add_assoc] using stop⟩
  | branch a b yes no iy ino =>
    obtain ⟨ht,hn,hj,hy⟩ := branch_sites sub
    have step := step_jle τ loc a b _ ht
    have cost := test_travels (τ:=τ) loc a b _ ht
    by_cases take : s.mem a ≤ s.mem b
    · rw [if_pos take] at step
      obtain ⟨t,ex,stop⟩ := iy _ _ s hy step
      refine ⟨t,?_,?_⟩
      · simpa only [run,charge,if_pos take] using cost.trans ex
      · simpa [cmd,Cmd.len,run,take,Nat.add_assoc] using stop
    · rw [if_neg take] at step
      obtain ⟨m,ex,ml⟩ := ino _ _ s hn step
      have jump := step_jump τ ml _ hj
      have back := test_travels (τ:=τ) ml 0 0 _ hj
      refine ⟨P.step τ m,?_,?_⟩
      · simpa only [run,charge,if_neg take,Nat.add_assoc] using (cost.trans ex).trans back
      · simpa [cmd,Cmd.len,run,take,Nat.add_assoc] using jump

end TargetedSamplers.Structured

namespace TargetedSamplers.Structured.CallerBank

/-- Polynomial working memory of the outer algorithm. Each logical register has one
dedicated physical address, independent of guest words and virtual input symbols. -/
def addr (i : ℕ) := 67+4*i
def project (s : Store) : Store := ⟨fun i => s.mem (addr i),s.out⟩
def Outside (a : ℕ) := a≠14 ∧ a≠15 ∧ ∀ i, a≠addr i
def Frame (s t : Store) := ∀ a, Outside a → t.mem a=s.mem a

theorem frame_refl (s : Store) : Frame s s := fun _ _ => rfl
theorem frame_trans {s t u : Store} (p : Frame s t) (q : Frame t u) : Frame s u :=
  fun a h => (q a h).trans (p a h)

private theorem inj : Function.Injective addr := by intro a b h;unfold addr at h;omega

private theorem proj_write (s : Store) (a w : ℕ) : project (s.write (addr a) w)=(project s).write a w := by
  unfold project Store.write
  congr 1
  funext i
  simp [Function.update_apply,inj.eq_iff]

private theorem proj_tmp (s : Store) (a w : ℕ) (h : a<67) : project (s.write a w)=project s := by
  unfold project Store.write
  congr 1
  funext i;simp [Function.update_of_ne,show addr i ≠ a by unfold addr;omega]

private theorem frame_write (s : Store) (a w : ℕ) : Frame s (s.write (addr a) w) :=
  fun i h => by simp [Store.write,h.2.2 a]

private theorem frame_tmp (s : Store) (w : ℕ) (a : ℕ) (h : a=14 ∨ a=15) : Frame s (s.write a w) := by
  intro i hi
  rcases h with rfl|rfl
  · simp [Store.write,hi.1]
  · simp [Store.write,hi.2.1]

def indirect (a : ℕ) : Fragment := Structured.sequence [
  .op (.add 14 (addr a) (addr a)),.op (.add 14 14 14),.op (.const 15 67),.op (.add 14 14 15)]

theorem indirect_ok (τ : Tapes) (s : Store) (a : ℕ) :
    let t := (indirect a |>.run τ s).last
    t.mem 14=addr ((project s).mem a) ∧ project t=project s ∧ Frame s t := by
  let z := s.mem (addr a)
  let t0 := s.write 14 (z+z)
  let t1 := t0.write 14 (z+z+(z+z))
  let t2 := t1.write 15 67
  let t3 := t2.write 14 (z+z+(z+z)+67)
  have run : ((indirect a).run τ s).last=t3 := by
    simp [indirect,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,t0,t1,t2,t3,z]
  rw [run]
  have h0 := proj_tmp s 14 (z+z) (by decide)
  have h1 := proj_tmp t0 14 (z+z+(z+z)) (by decide)
  have h2 := proj_tmp t1 15 67 (by decide)
  have h3 := proj_tmp t2 14 (z+z+(z+z)+67) (by decide)
  refine ⟨?_,h3.trans (h2.trans (h1.trans h0)),?_⟩
  · change (t2.write 14 _).mem 14=addr z
    simp [Store.write,addr];omega
  · exact frame_trans (frame_trans (frame_trans (frame_tmp _ _ _ (Or.inl rfl))
      (frame_tmp _ _ _ (Or.inl rfl))) (frame_tmp _ _ _ (Or.inr rfl))) (frame_tmp _ _ _ (Or.inl rfl))

def liftOp : Op → Fragment
  | .const d k => .op (.const (addr d) k)
  | .add d a b => .op (.add (addr d) (addr a) (addr b))
  | .sub d a b => .op (.sub (addr d) (addr a) (addr b))
  | .load d a => .seq (indirect a) (.op (.load (addr d) 14))
  | .store a b => .seq (indirect a) (.op (.store 14 (addr b)))
  | .input d a => .op (.input (addr d) (addr a))
  | .coin d a => .op (.coin (addr d) (addr a))
  | .output a => .op (.output (addr a))

theorem op_ok (o : Op) (τ : Tapes) (s : Store) :
    let t := ((liftOp o).run τ s).last
    project t=o.eval τ (project s) ∧ Frame s t := by
  cases o with
  | load d a =>
    let t := ((indirect a).run τ s).last
    obtain ⟨key,pre,frame⟩ := indirect_ok τ s a
    change t.mem 14=_ at key
    have word (i : ℕ) : t.mem (addr i) = s.mem (addr i) := congrArg (fun z : Store => z.mem i) pre
    change project (t.write (addr d) (t.mem (t.mem 14)))=_ ∧ Frame s (t.write (addr d) (t.mem (t.mem 14)))
    rw [key,word,proj_write,pre]
    exact ⟨rfl,frame_trans frame (frame_write t _ _)⟩
  | store a b =>
    let t := ((indirect a).run τ s).last
    obtain ⟨key,pre,frame⟩ := indirect_ok τ s a
    change t.mem 14=_ at key
    have word (i : ℕ) : t.mem (addr i) = s.mem (addr i) := congrArg (fun z : Store => z.mem i) pre
    change project (t.write (t.mem 14) (t.mem (addr b)))=_ ∧ Frame s (t.write (t.mem 14) (t.mem (addr b)))
    rw [key,word,proj_write,pre];exact ⟨rfl,frame_trans frame (frame_write t _ _)⟩
  | output a => exact ⟨rfl,fun _ _ => rfl⟩
  | _ => exact ⟨proj_write ..,frame_write s _ _⟩

def lift : Cmd → Cmd
  | .skip => .skip
  | .op o => (liftOp o).cmd
  | .seq x y => .seq (lift x) (lift y)
  | .branch a b x y => .branch (addr a) (addr b) (lift x) (lift y)
  | .whileGt a b x => .whileGt (addr a) (addr b) (lift x)

def immutable (s : Store) (z : ℕ) (hz : z<14) (t : Store) (f : Frame s t) : t.mem z=s.mem z :=
  f z ⟨by omega,by omega,fun i => by unfold addr;omega⟩

def capOp : Op → ℕ
  | .const d k => 200+addr d+k
  | .add d a b | .sub d a b => 200+addr d+addr a+addr b
  | .input d a | .coin d a | .load d a => 200+addr d+addr a
  | .store a b => 200+addr a+addr b
  | .output a => 200+addr a

def cap : Cmd → ℕ
  | .skip => 200
  | .op o => capOp o
  | .seq x y => cap x+cap y
  | .branch a b x y => addr a+addr b+cap x+cap y+200
  | .whileGt a b x => addr a+addr b+cap x+200

private theorem small (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

private theorem virtual_width (i : ℕ) : (addr i).size ≤ i.size+8 := by
  apply Nat.size_le.mpr;rw [pow_add]
  have h := Nat.lt_size_self i;have p := Nat.two_pow_pos i.size
  dsimp [addr];norm_num;omega

theorem op_charge (o : Op) (τ : Tapes) (s : Store) (w pc : ℕ)
    (fit : (project s).Fits w) (res : (o.eval τ (project s)).Fits w) :
    (liftOp o).charge τ s pc ≤ 128*(1+w+capOp o) := by
  have read (a : ℕ) : (s.mem (addr a)).size ≤ w := fit a
  have address (a : ℕ) := virtual_width (s.mem (addr a))
  have val (x : ℕ) (low : x ≤ 256) : x.size ≤ 9 := (Nat.size_le_size low).trans (by decide)
  have s14 := val 14 (by decide);have s15 := val 15 (by decide);have s67 := val 67 (by decide)
  cases o with
  | const d k =>
    have s1 := small (addr d);have s2 := small k
    simp [liftOp,Fragment.charge,Op.charge,capOp];omega
  | add d a b | sub d a b =>
    have s1 := small (addr d);have s2 := small (addr a);have s3 := small (addr b)
    have val := res d
    simp [Op.eval,Store.write,project] at val
    simp [liftOp,Fragment.charge,Op.charge,capOp]
    have := read a;have := read b;omega
  | input d a | coin d a =>
    have s1 := small (addr d);have s2 := small (addr a)
    have val := res d
    simp [Op.eval,Store.write,project] at val
    simp [liftOp,Fragment.charge,Op.charge,capOp];have := read a;omega
  | output a =>
    have := small (addr a);have := read a;simp [liftOp,Fragment.charge,Op.charge,capOp];omega
  | load d a | store a d =>
    let x := s.mem (addr a)
    have ea : x+x+(x+x)+67=addr x := by dsimp [addr];omega
    have sx : x.size ≤ w := read a
    have q : (addr x).size ≤ x.size+8 := address a
    have xd := (Nat.size_le_size (show x+x ≤ addr x by unfold addr;omega)).trans q
    have xq := (Nat.size_le_size (show x+x+(x+x) ≤ addr x by unfold addr;omega)).trans q
    have sd := small (addr d);have sa := small (addr a)
    have A (i : ℕ) : addr i≠14 := by unfold addr;omega
    have B (i : ℕ) : addr i≠15 := by unfold addr;omega
    have loadVal := read x;have storeVal := read d
    simp (disch := omega) [liftOp,indirect,Structured.sequence,Fragment.charge,Fragment.run,Op.charge,
      Op.eval,Store.write,Function.update_apply,capOp,←show x=s.mem (addr a) from rfl,ea,A,B]
    omega

end TargetedSamplers.Structured.CallerBank

namespace TargetedSamplers.Structured.CallerBank

private theorem end_fits {τ inv c s t k} (e : Exec τ inv c s t k) (start : inv s) : inv t := by
  induction e with
  | skip | done => exact start
  | op _ _ h => exact h
  | seq _ _ ix iy | again _ _ _ ix iy => exact iy (ix start)
  | yes _ _ ih | no _ _ ih => exact ih start

theorem room {P : Program} {pc : ℕ} {cmd : Cmd} (sub : Contains P pc (cmd.compile pc)) :
    pc+cmd.len ≤ P.length := by
  obtain ⟨pre,post,eq,rfl⟩ := sub;simp [eq]

def unitCost (P : Program) (H w : ℕ) := 128*(5+w+H+P.length.size)

theorem test_bound (P : Program) (H w a b target : ℕ) (s : Store)
    (hf : (project s).Fits w) (ab : addr a+addr b ≤ H) (dest : target ≤ P.length) :
    testCharge s (addr a) (addr b) target ≤ unitCost P H w := by
  have A : (addr a).size ≤ addr a := Nat.size_le.mpr Nat.lt_two_pow_self
  have B : (addr b).size ≤ addr b := Nat.size_le.mpr Nat.lt_two_pow_self
  have wa := hf a;have wb := hf b
  change (s.mem (addr a)).size ≤ w at wa;change (s.mem (addr b)).size ≤ w at wb
  have lab := Nat.size_le_size dest
  dsimp [testCharge,unitCost];omega

theorem jump_bound (P : Program) (H w target : ℕ) (s : Store) (zero : s.mem 0=0)
    (dest : target ≤ P.length) : testCharge s 0 0 target ≤ unitCost P H w := by
  have lab := Nat.size_le_size dest
  simp [testCharge,unitCost,zero];omega

/-- Relocate a bounded-word operation into the caller's private arithmetic bank.
The bound does not require the unrelated guest epoch target have bounded-width cells. -/
theorem exec {τ w c a d k} (ev : Exec τ (fun v => v.Fits w) c a d k) (P : Program) (H : ℕ)
    (pc : ℕ) (st : State) (s : Store) (allow : cap c ≤ H) (sub : Contains P pc ((lift c).compile pc))
    (atPC : Located st pc s) (zero : s.mem 0=0) (fit : a.Fits w) (rep : project s=a) :
    ∃ u t j cost, Travels P τ st u j cost ∧ Located u (pc+(lift c).len) t ∧
      project t=d ∧ Frame s t ∧ cost ≤ k*unitCost P H w := by
  let M := unitCost P H w
  induction ev generalizing pc st s with
  | skip =>
    exact ⟨st,s,0,0,⟨rfl,by simp⟩,by simpa [lift,Cmd.len] using atPC,rep,frame_refl s,by simp⟩
  | op a o res =>
    obtain ⟨u,path,done⟩ := (liftOp o).compile_charge P τ pc st s sub atPC
    obtain ⟨eq,frame⟩ := op_ok o τ s
    have pay := op_charge o τ s w pc (rep.symm ▸ fit) (rep.symm ▸ res)
    exact ⟨u,_,_,_,path,done,eq.trans (congrArg (o.eval τ) rep),frame,by
      simp only [one_mul];dsimp [unitCost];change capOp o ≤ H at allow;omega⟩
  | @seq x y a m t k l xrun yrun ix iy =>
    change cap x+cap y ≤ H at allow
    obtain ⟨u,b,i,f,xh,mid,bRep,bFrame,xc⟩ := ix pc st s (by omega) sub.left atPC zero fit rep
    have bySite : Contains P (pc+(lift x).len) ((lift y).compile (pc+(lift x).len)) := by simpa using sub.right
    obtain ⟨v,d,j,g,yh,done,dRep,dFrame,yc⟩ := iy _ u b (by omega) bySite mid
      ((immutable s 0 (by decide) b bFrame).trans zero) (end_fits xrun fit) bRep
    exact ⟨v,d,_,_,xh.trans yh,by simpa [lift,Cmd.len,Nat.add_assoc] using done,
      dRep,frame_trans bFrame dFrame,by rw [Nat.add_mul];omega⟩
  | @yes a b y n start finish k cmp body ih =>
    change addr a+addr b+cap y+cap n+200 ≤ H at allow
    obtain ⟨ht,_,_,hy⟩ := branch_sites sub
    have h := step_jle τ atPC _ _ _ ht
    have cond : s.mem (addr a) ≤ s.mem (addr b) := by change (project s).mem a ≤ (project s).mem b;rw [rep];exact cmp
    rw [if_pos cond] at h
    obtain ⟨u,t,i,f,yh,done,out,frame,le⟩ := ih _ _ s (by omega) hy h zero fit rep
    have r := room sub
    simp only [lift,Cmd.len] at r
    have fee := test_bound P H w a b _ s (rep.symm ▸ fit) (by omega) (by omega : pc+1+(lift n).len+1 ≤ P.length)
    refine ⟨u,t,_,_,(test_travels (τ:=τ) atPC _ _ _ ht).trans yh,by simpa [lift,Cmd.len,Nat.add_assoc] using done,out,frame,?_⟩
    rw [Nat.add_mul,one_mul];omega
  | @no a b y n start finish k cmp body ih =>
    change addr a+addr b+cap y+cap n+200 ≤ H at allow
    obtain ⟨ht,hn,hj,_⟩ := branch_sites sub
    have h := step_jle τ atPC _ _ _ ht
    have cond : ¬s.mem (addr a) ≤ s.mem (addr b) := by change ¬(project s).mem a ≤ (project s).mem b;rw [rep];exact cmp
    rw [if_neg cond] at h
    obtain ⟨u,t,i,f,nh,mid,out,frame,le⟩ := ih _ _ s (by omega) hn h zero fit rep
    have back := step_jump τ mid _ hj
    have r := room sub;simp only [lift,Cmd.len] at r
    have fee := test_bound P H w a b _ s (rep.symm ▸ fit) (by omega) (by omega : pc+1+(lift n).len+1 ≤ P.length)
    have jump := jump_bound P H w _ t ((immutable s 0 (by decide) t frame).trans zero)
      (by omega : pc+1+(lift n).len+1+(lift y).len ≤ P.length)
    refine ⟨_,t,_,_,((test_travels (τ:=τ) atPC _ _ _ ht).trans nh).trans (test_travels (τ:=τ) mid 0 0 _ hj),
      by simpa [lift,Cmd.len,Nat.add_assoc] using back,out,frame,?_⟩
    simp only [Nat.add_mul,one_mul];omega
  | @done a b body start cmp =>
    change addr a+addr b+cap body+200 ≤ H at allow
    have sites := loop_sites sub
    have cond : s.mem (addr a) ≤ s.mem (addr b) := by change (project s).mem a ≤ (project s).mem b;rw [rep];exact cmp
    have h := step_jle τ atPC _ _ _ sites.1;rw [if_pos cond] at h
    have r := room sub;simp only [lift,Cmd.len] at r
    refine ⟨_,s,_,_,test_travels (τ:=τ) atPC _ _ _ sites.1,by simpa [lift,Cmd.len,Nat.add_assoc] using h,rep,frame_refl s,?_⟩
    simp only [one_mul];exact test_bound P H w _ _ _ s (rep.symm ▸ fit) (by omega) (by omega)
  | @again a b body start m t k l cmp first tail ix iy =>
    have cap0 := allow
    change addr a+addr b+cap body+200 ≤ H at cap0
    obtain ⟨ht,bodySite,jmp⟩ := loop_sites sub
    have h := step_jle τ atPC _ _ _ ht
    have cond : ¬s.mem (addr a) ≤ s.mem (addr b) := by change ¬(project s).mem a ≤ (project s).mem b;rw [rep];exact cmp
    rw [if_neg cond] at h
    obtain ⟨u,z,i,f,bh,mid,zRep,zFrame,bodyCost⟩ := ix _ _ s (by omega) bodySite h zero fit rep
    have restart := step_jump τ mid _ jmp
    have z0 := (immutable s 0 (by decide) z zFrame).trans zero
    obtain ⟨v,last,j,g,lp,done,out,frame,loopCost⟩ := iy pc _ z allow sub restart z0 (end_fits first fit) zRep
    have r := room sub;simp only [lift,Cmd.len] at r
    have fee := test_bound P H w a b _ s (rep.symm ▸ fit) (by omega) (by omega : pc+1+(lift body).len+1 ≤ P.length)
    have jump := jump_bound P H w pc z z0 (by omega)
    refine ⟨v,last,_,_,(((test_travels (τ:=τ) atPC _ _ _ ht).trans bh).trans (test_travels (τ:=τ) mid 0 0 _ jmp)).trans lp,
      done,out,frame_trans zFrame frame,?_⟩
    simp only [Nat.add_mul,one_mul];omega

end TargetedSamplers.Structured.CallerBank

namespace TargetedSamplers.Structured.GuestMemory

abbrev Reg := Fin 32
def loc (r : Reg) := 20+r.val
def tag (a : ℕ) := 64+4*a
def inputCell (a : ℕ) := tag a+2
def callerCell (a : ℕ) := tag a+3
def Valid (s : Store) (epoch : ℕ) := ∀ a, s.mem (tag a) ≤ epoch
structure Base (s : Store) (e : ℕ) : Prop where
  zero : s.mem 0=0
  clock : s.mem 10=e
  valid : Valid s e

end TargetedSamplers.Structured.GuestMemory

namespace DirectedHamiltonicity.Main.CycleReduction.Guest

open TargetedSamplers TargetedSamplers.Structured GuestMemory

structure Preserves (s t : Store) : Prop where
  output : t.out=s.out
  input : ∀ i, t.mem (inputCell i)=s.mem (inputCell i)
  caller : ∀ i, i≠0 → t.mem (callerCell i)=s.mem (callerCell i)

noncomputable def call (Q : Program) := Classical.choose (bounded_bit_subroutine Q)
noncomputable def callFactor (Q : Program) := Classical.choose (Classical.choose_spec (bounded_bit_subroutine Q))
def bits (x : List Bool) (base len e pc T : ℕ) := 1+x.length.size+base.size+len.size+e.size+pc.size+T.size

private theorem accumulates (P : Program) (τ : Tapes) (st : State) (j : ℕ) :
    st.work ≤ ((P.step τ)^[j] st).work := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    apply ih.trans
    let s := (P.step τ)^[j] st
    change s.work ≤ (P.step τ s).work
    by_cases h : s.halted=true
    · simp [Program.step,h]
    · cases fetch : P[s.pc]? with
      | none => simp [Program.step,h,fetch]
      | some i => cases i <;> simp [Program.step,h,fetch] <;> omega

/-- Local observation form of the reusable native bit-subroutine interface. -/
theorem call_runs (Q P : Program) (x : List Bool) (base len e pc T : ℕ) (τ : Tapes)
    (s : Store) (st : State) (v : Bool) (time : Q.RunsIn (runTapes x (CoinWindow.window τ.coins base len)) T (some [v]))
    (sub : Contains P pc ((call Q).compile pc)) (atPC : Located st pc s) (good : Base s e)
    (input : ∀ i<x.length, s.mem (inputCell i)=bitVal x[i]?)
    (one : s.mem (callerCell 1)=1) (fuel : s.mem (callerCell 0)=T)
    (dim : s.mem (callerCell 2)=x.length) (offset : s.mem (callerCell 3)=base) (length : s.mem (callerCell 4)=len) :
    ∃ (u : State) (t : Store) (steps fee : ℕ), Travels P τ st u steps fee ∧
      Located u (pc+(call Q).len) t ∧ Base t (e+1) ∧ Preserves s t ∧
      t.mem (loc 2)=v.toNat ∧ fee ≤ callFactor Q*(T+1)*bits x base len e pc T := by
  obtain ⟨pre,post,rfl,rfl⟩ := sub
  let P := pre++(call Q).compile pre.length++post
  have iEq (i : ℕ) : 66+4*i=inputCell i := by unfold inputCell tag;omega
  have cEq (i : ℕ) : 67+4*i=callerCell i := by unfold callerCell tag;omega
  have run := Classical.choose_spec (Classical.choose_spec (bounded_bit_subroutine Q)) pre post τ st x base len e T v time
    atPC.counter atPC.live atPC.normal (atPC.memory ▸ good.zero) (atPC.memory ▸ good.clock)
    (fun i => atPC.memory ▸ good.valid i) (fun i hi => by rw [atPC.memory,iEq];exact input i hi)
    (atPC.memory ▸ fuel) (atPC.memory ▸ one) (atPC.memory ▸ dim) (atPC.memory ▸ offset) (atPC.memory ▸ length)
  obtain ⟨j,pc,live,normal,out,zero,clock,valid,bit,port,caller,pay⟩ := run
  let u := (P.step τ)^[j] st
  let t : Store := ⟨u.mem,u.out⟩
  have mono : st.work ≤ u.work := accumulates P τ st j
  change u.work ≤ st.work+callFactor Q*(T+1)*bits x base len e pre.length T at pay
  refine ⟨u,t,j,u.work-st.work,⟨rfl,by omega⟩,⟨pc,live,normal,rfl,rfl⟩,⟨zero,clock,valid⟩,
    ⟨out.trans atPC.output,?_,?_⟩,bit,by omega⟩
  · intro i;change u.mem (inputCell i)=s.mem (inputCell i)
    rw [←iEq];exact (port i).trans (congrFun atPC.memory _)
  · intro i hi;change u.mem (callerCell i)=s.mem (callerCell i)
    rw [←cEq];exact (caller i hi).trans (congrFun atPC.memory _)

end DirectedHamiltonicity.Main.CycleReduction.Guest

namespace DirectedHamiltonicity.Main.CycleReduction.OuterMachine

open TargetedSamplers TargetedSamplers.Structured GuestMemory
open CallerBank (addr project)

def Good (s : Store) (d : Data) := project s=d.bank ∧ (∀ i, s.mem (inputCell i)=d.port i) ∧ Base s d.epoch

def transfer (a b : ℕ) : Fragment := Structured.sequence [.op (.add 14 (addr a) (addr a)),.op (.add 14 14 14),
  .op (.const 15 66),.op (.add 14 14 15),.op (.store 14 (addr b))]

def receive := Structured.sequence [.op (.const (addr 0) 0),.op (.add (addr 5) (loc 2) 0)]

noncomputable def Code.native (Q : Program) : Code → Cmd
  | .pure c => CallerBank.lift c
  | .port a b => (transfer a b).cmd
  | .query => .seq (Guest.call Q) receive.cmd
  | .seq x y => .seq (x.native Q) (y.native Q)
  | .branch a b x y => .branch (addr a) (addr b) (x.native Q) (y.native Q)
  | .loop a b x => .whileGt (addr a) (addr b) (x.native Q)

private theorem input_far (i : ℕ) : 64 ≤ inputCell i := by unfold inputCell tag;omega
private theorem disjoint (i j : ℕ) : inputCell i≠addr j := by unfold inputCell tag addr;omega

theorem ordinary_frame {s t : Store} {d : Data} {b : Store} (h : Good s d) (proj : project t=b)
    (frm : CallerBank.Frame s t) : Good t {d with bank := b} := by
  obtain ⟨_,port,base⟩ := h
  have outside (i : ℕ) (hi : i≠14) (hj : i≠15) (sep : ∀ j, i≠addr j) := frm i ⟨hi,hj,sep⟩
  refine ⟨proj,fun i => (outside (inputCell i) (by have := input_far i;omega) (by have := input_far i;omega)
    (disjoint i)).trans (port i),?_,?_,?_⟩
  · exact (CallerBank.immutable _ 0 (by decide) _ frm).trans base.zero
  · exact (CallerBank.immutable _ 10 (by decide) _ frm).trans base.clock
  · intro i
    rw [outside (tag i) (by unfold tag;omega) (by unfold tag;omega) (fun j => by unfold tag addr;omega)]
    exact base.valid i

theorem transfer_ok (τ : Tapes) {s : Store} {d : Data} (h : Good s d) (a b : ℕ) :
    Good ((transfer a b).run τ s).last (d.publish a b) := by
  rcases h with ⟨pr,port,base⟩
  have bank (i : ℕ) : s.mem (addr i)=d.bank.mem i := congrArg (fun z : Store => z.mem i) pr
  have addrEq (z : ℕ) : z+z+(z+z)+66=inputCell z := by unfold inputCell tag;omega
  let t := ((transfer a b).run τ s).last
  have outside (i : ℕ) (x : i≠14) (y : i≠15) (ne : i≠inputCell (d.bank.mem a)) : t.mem i=s.mem i := by
    simp (disch := omega) [t,transfer,Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,bank,addrEq,x,y,ne,show addr b≠14 by unfold addr;omega,show addr b≠15 by unfold addr;omega]
  have got : t.mem (inputCell (d.bank.mem a))=d.bank.mem b := by
    simp [t,transfer,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,bank,addrEq,
      show addr b≠14 by unfold addr;omega,show addr b≠15 by unfold addr;omega]
  refine ⟨?_,?_,?_,?_,?_⟩
  · change project t=d.bank
    rw [←pr];unfold project
    congr 1
    funext i;apply outside <;> first | exact (disjoint _ _).symm | unfold addr;omega
  · intro i
    change t.mem (inputCell i) = Function.update d.port (d.bank.mem a) (d.bank.mem b) i
    by_cases eq : i=d.bank.mem a
    · subst i;simpa using got
    · rw [Function.update_of_ne eq,outside _ (by have := input_far i;omega) (by have := input_far i;omega)
        (by unfold inputCell tag;omega)];exact port i
  · exact (outside 0 (by decide) (by decide) (by have := input_far (d.bank.mem a);omega)).trans base.zero
  · exact (outside 10 (by decide) (by decide) (by have := input_far (d.bank.mem a);omega)).trans base.clock
  · intro i
    rw [outside (tag i) (by unfold tag;omega) (by unfold tag;omega) (by unfold inputCell tag;omega)]
    exact base.valid i

theorem transfer_work (τ : Tapes) (pc a b w : ℕ) {s : Store} {d : Data} (h : Good s d) (fit : d.bank.Fits w) :
    (transfer a b).charge τ s pc ≤ 128*(100+w+addr a+addr b) := by
  let x := s.mem (addr a)
  have A : (addr a).size ≤ addr a := Nat.size_le.mpr Nat.lt_two_pow_self
  have B : (addr b).size ≤ addr b := Nat.size_le.mpr Nat.lt_two_pow_self
  have fit' : (project s).Fits w := h.1.symm ▸ fit
  have input : x.size ≤ w := fit' a
  have value : (s.mem (addr b)).size ≤ w := fit' b
  have upper : (x+x+(x+x)+66).size ≤ x.size+8 := by
    apply Nat.size_le.mpr;rw [pow_add];have := Nat.lt_size_self x;have := Nat.two_pow_pos x.size;norm_num;omega
  have small1 := (Nat.size_le_size (by omega : x+x ≤ x+x+(x+x)+66)).trans upper
  have small2 := (Nat.size_le_size (by omega : x+x+(x+x) ≤ x+x+(x+x)+66)).trans upper
  have A14 : (14:ℕ).size=4 := rfl
  have A15 : (15:ℕ).size=4 := rfl
  have A66 : (66:ℕ).size=7 := rfl
  simp [transfer,Structured.sequence,Fragment.charge,Fragment.run,Op.eval,Op.charge,Store.write,Function.update_apply,
    show addr b≠14 by unfold addr;omega,show addr b≠15 by unfold addr;omega,←show x=s.mem (addr a) from rfl,A14,A15,A66]
  omega

end DirectedHamiltonicity.Main.CycleReduction.OuterMachine

namespace DirectedHamiltonicity.Main.CycleReduction.OuterMachine

open TargetedSamplers TargetedSamplers.Structured GuestMemory
open CallerBank (addr project)

private theorem caller_eq (i : ℕ) : callerCell i=addr i := by unfold callerCell tag addr;omega

private theorem store_eq {s t : Store} (m : s.mem=t.mem) (o : s.out=t.out) : s=t := by
  cases s;cases t;congr

private theorem receive_ok {s t : Store} {d : Data} (h : Good s d) (p : Guest.Preserves s t)
    (base : Base t (d.epoch+1)) (v : Bool) (out : t.mem (loc 2)=v.toNat) (τ : Tapes) :
    Good (receive.run τ t).last (d.returnBit v) := by
  let z := (receive.run τ t).last
  have zmem : z.mem=Function.update (Function.update t.mem (addr 0) 0) (addr 5) v.toNat := by
    simp [z,receive,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,addr,loc,base.zero] at out ⊢
    rw [out]
  have preserved (i : ℕ) (hi : i≠0) : t.mem (addr i)=s.mem (addr i) := by simpa only [caller_eq] using p.caller i hi
  have init (i : ℕ) : s.mem (addr i)=d.bank.mem i := congrArg (fun u : Store => u.mem i) h.1
  have raw (a : ℕ) (lo : a≠addr 0) (hi : a≠addr 5) : z.mem a=t.mem a := by rw [zmem];simp [lo,hi]
  refine ⟨?_,?_,?_,?_,?_⟩
  · change project z=(d.bank.write 0 0).write 5 v.toNat
    apply store_eq
    · funext i
      change z.mem (addr i)=_
      by_cases one : i=5
      · subst i;simp [Store.write,zmem]
      by_cases zero : i=0
      · subst i;simp [Store.write,zmem,addr]
      rw [raw _ (by unfold addr;omega) (by unfold addr;omega),preserved _ zero,init]
      simp [Store.write,one,zero]
    · change t.out=d.bank.out
      have same := congrArg Store.out h.1
      exact p.output.trans same
  · intro i
    rw [raw (inputCell i) (by unfold inputCell tag addr;omega) (by unfold inputCell tag addr;omega),p.input i]
    exact h.2.1 i
  · exact (raw 0 (by decide) (by decide)).trans base.zero
  · exact (raw 10 (by decide) (by decide)).trans base.clock
  · intro i
    rw [raw (tag i) (by unfold tag addr;omega) (by unfold tag addr;omega)]
    exact base.valid i

private theorem receive_cost (τ : Tapes) (t : Store) (pc e : ℕ) (base : Base t e) (v : Bool) (bit : t.mem (loc 2)=v.toNat) :
    receive.charge τ t pc ≤ 1024 := by
  have b : t.mem 22=v.toNat := bit
  cases v <;> simp [receive,Structured.sequence,Fragment.charge,Fragment.run,Op.eval,Op.charge,Store.write,Function.update_apply,
    addr,loc,base.zero,b] <;> decide

def Code.cap : Code → ℕ
  | .pure c => CallerBank.cap c
  | .port a b => 100+addr a+addr b
  | .query => 0
  | .seq x y => x.cap+y.cap
  | .branch a b x y => addr a+addr b+x.cap+y.cap
  | .loop a b x => addr a+addr b+x.cap

noncomputable def unit (Q P : Program) (H w : ℕ) := (2048+8*Guest.callFactor Q)*(300+w+H+P.length.size)

private theorem local_unit (Q P : Program) (H w : ℕ) : CallerBank.unitCost P H w ≤ unit Q P H w := by
  have p : 128 ≤ 2048+8*Guest.callFactor Q := by omega
  exact Nat.mul_le_mul p (by omega)

private theorem query_native {Q : Program} {τ : Tapes} {w : ℕ} (d : Data) (x : List Bool) (v : Bool)
    (fit : d.bank.Fits w) (epoch : d.epoch.size ≤ w) (one : d.bank.mem 1=1) (dim : d.bank.mem 2=x.length)
    (input : ∀ i<x.length, d.port i=bitVal x[i]?)
    (time : Q.RunsIn (runTapes x (CoinWindow.window τ.coins (d.bank.mem 3) (d.bank.mem 4))) (d.bank.mem 0) (some [v]))
    (P : Program) (H pc : ℕ) (st : State) (s : Store) (sub : Contains P pc ((Code.query.native Q).compile pc))
    (atPC : Located st pc s) (h : Good s d) :
    ∃ u t j fee, Travels P τ st u j fee ∧ Located u (pc+(Code.query.native Q).len) t ∧
      Good t (d.returnBit v) ∧ fee ≤ (d.bank.mem 0+1)*unit Q P H w := by
  have caller (i : ℕ) : s.mem (callerCell i)=d.bank.mem i := by
    rw [caller_eq];exact congrArg (fun u : Store => u.mem i) h.1
  obtain ⟨m,z,j,f,go,mid,base,frame,bit,budget⟩ := Guest.call_runs Q P x (d.bank.mem 3) (d.bank.mem 4)
    d.epoch pc (d.bank.mem 0) τ s st v time sub.left atPC h.2.2 (fun i hi => (h.2.1 i).trans (input i hi))
    ((caller 1).trans one) (caller 0) ((caller 2).trans dim) (caller 3) (caller 4)
  have recSite : Contains P (pc+(Guest.call Q).len) (receive.cmd.compile (pc+(Guest.call Q).len)) := by simpa using sub.right
  obtain ⟨u,tail,loc⟩ := receive.compile_charge P τ _ m z recSite mid
  have cost := budget
  let T := d.bank.mem 0
  let F := Guest.callFactor Q
  let U := 300+w+H+P.length.size
  have lab := CallerBank.room sub
  have labSize := Nat.size_le_size (by omega : pc ≤ P.length)
  have small : Guest.bits x (d.bank.mem 3) (d.bank.mem 4) d.epoch pc T ≤ 8*U := by
    have a := fit 0;have b := fit 2;have c := fit 3;have e := fit 4
    rw [dim] at b;dsimp [Guest.bits,U,T];omega
  have cap := cost.trans (Nat.mul_le_mul_left _ small)
  have tailCost := receive_cost τ z (pc+(Guest.call Q).len) _ base v bit
  have extra : 1024 ≤ (T+1)*(2048*U) := by
    have pos : 1 ≤ U := by dsimp [U];omega
    have left := Nat.le_mul_of_pos_right 2048 pos
    exact (show 1024 ≤ 2048 by decide).trans (left.trans (Nat.le_mul_of_pos_left _ (by omega)))
  refine ⟨u,_,_,_,go.trans tail,by simpa [Code.native,Cmd.len,Nat.add_assoc] using loc,receive_ok h frame base v bit τ,?_⟩
  calc
    _ ≤ F*(T+1)*(8*U)+(T+1)*(2048*U) := Nat.add_le_add cap (tailCost.trans extra)
    _ = _ := by change _=(T+1)*((2048+8*F)*U);ring

/-- Compile all finite outer control and charge its executed arms and bounded calls. -/
theorem native {Q τ w c a d k} (ev : Eval Q τ w c a d k) (P : Program) (H : ℕ)
    (pc : ℕ) (st : State) (s : Store) (allow : c.cap ≤ H) (sub : Contains P pc ((c.native Q).compile pc))
    (atPC : Located st pc s) (h : Good s a) :
    ∃ u t j fee, Travels P τ st u j fee ∧ Located u (pc+(c.native Q).len) t ∧ Good t d ∧ fee ≤ k*unit Q P H w := by
  have unitLe := local_unit Q P H w
  induction ev generalizing pc st s with
  | pure fit run =>
    obtain ⟨u,t,j,f,real,loc,proj,frm,bound⟩ := CallerBank.exec run P H pc st s allow sub atPC h.2.2.zero fit h.1
    exact ⟨u,t,j,f,real,loc,ordinary_frame h proj frm,bound.trans (Nat.mul_le_mul_left _ unitLe)⟩
  | port d a b fit =>
    obtain ⟨u,path,loc⟩ := (transfer a b).compile_charge P τ pc st s sub atPC
    have pay := transfer_work τ pc a b w h fit
    change 100+addr a+addr b ≤ H at allow
    have enough : 128*(100+w+addr a+addr b) ≤ unit Q P H w :=
      (Nat.mul_le_mul (show 128 ≤ 2048+8*Guest.callFactor Q by omega) (show 100+w+addr a+addr b ≤ 300+w+H+P.length.size by omega))
    exact ⟨_,_,_,_,path,loc,transfer_ok τ h a b,by simpa only [one_mul] using pay.trans enough⟩
  | query d x v fit epoch one dim input time => exact query_native d x v fit epoch one dim input time P H pc st s sub atPC h
  | @seq c f start mid dest k l first second ix iy =>
    change c.cap+f.cap ≤ H at allow
    obtain ⟨u,b,i,p,g,atMid,good,cost⟩ := ix pc st s (by omega) sub.left atPC h
    have site : Contains P (pc+(c.native Q).len) ((f.native Q).compile (pc+(c.native Q).len)) := by simpa using sub.right
    obtain ⟨z,d,j,f,rest,loc,ok,bound⟩ := iy _ u b (by omega) site atMid good
    exact ⟨_,_,_,_,g.trans rest,by simpa [Code.native,Cmd.len,Nat.add_assoc] using loc,ok,by rw [Nat.add_mul];omega⟩
  | @yes a b y n start finish k fit cmp body ih =>
    change addr a+addr b+y.cap+n.cap ≤ H at allow
    obtain ⟨ht,_,_,hy⟩ := branch_sites sub
    have c : s.mem (addr a) ≤ s.mem (addr b) := by change (project s).mem a ≤ (project s).mem b;rw [h.1];exact cmp
    have hi := step_jle τ atPC _ _ _ ht;rw [if_pos c] at hi
    obtain ⟨u,t,i,f,go,loc,good,cost⟩ := ih _ _ s (by omega) hy hi h
    have r := CallerBank.room sub;simp only [Code.native,Cmd.len] at r
    have fee := (CallerBank.test_bound P H w a b _ s (h.1.symm ▸ fit) (by omega)
      (by omega : pc+1+(n.native Q).len+1 ≤ P.length)).trans unitLe
    exact ⟨_,_,_,_,(test_travels (τ:=τ) atPC _ _ _ ht).trans go,by simpa [Code.native,Cmd.len,Nat.add_assoc] using loc,good,
      by rw [Nat.add_mul,one_mul];omega⟩
  | @no a b y n start finish k fit cmp body ih =>
    change addr a+addr b+y.cap+n.cap ≤ H at allow
    obtain ⟨ht,hn,hj,_⟩ := branch_sites sub
    have c : ¬s.mem (addr a) ≤ s.mem (addr b) := by change ¬(project s).mem a ≤ (project s).mem b;rw [h.1];exact cmp
    have hi := step_jle τ atPC _ _ _ ht;rw [if_neg c] at hi
    obtain ⟨u,t,i,f,go,loc,good,cost⟩ := ih _ _ s (by omega) hn hi h
    have back := step_jump τ loc _ hj
    have r := CallerBank.room sub;simp only [Code.native,Cmd.len] at r
    have fee := (CallerBank.test_bound P H w a b _ s (h.1.symm ▸ fit) (by omega)
      (by omega : pc+1+(n.native Q).len+1 ≤ P.length)).trans unitLe
    have jmp := (CallerBank.jump_bound P H w _ t good.2.2.zero
      (by omega : pc+1+(n.native Q).len+1+(y.native Q).len ≤ P.length)).trans unitLe
    exact ⟨_,_,_,_,((test_travels (τ:=τ) atPC _ _ _ ht).trans go).trans (test_travels (τ:=τ) loc 0 0 _ hj),
      by simpa [Code.native,Cmd.len,Nat.add_assoc] using back,good,by simp only [Nat.add_mul,one_mul];omega⟩
  | @done a b body start fit cmp =>
    change addr a+addr b+body.cap ≤ H at allow
    have sites := loop_sites sub
    have c : s.mem (addr a) ≤ s.mem (addr b) := by change (project s).mem a ≤ (project s).mem b;rw [h.1];exact cmp
    have hi := step_jle τ atPC _ _ _ sites.1;rw [if_pos c] at hi
    have r := CallerBank.room sub;simp only [Code.native,Cmd.len] at r
    refine ⟨_,_,_,_,test_travels (τ:=τ) atPC _ _ _ sites.1,by simpa [Code.native,Cmd.len,Nat.add_assoc] using hi,h,?_⟩
    simp only [one_mul];exact (CallerBank.test_bound P H w _ _ _ s (h.1.symm ▸ fit) (by omega) (by omega)).trans unitLe
  | @again a b body start m t k l fit cmp first tail ix iy =>
    have cap0 := allow;change addr a+addr b+body.cap ≤ H at cap0
    obtain ⟨ht,bodySite,jmp⟩ := loop_sites sub
    have c : ¬s.mem (addr a) ≤ s.mem (addr b) := by change ¬(project s).mem a ≤ (project s).mem b;rw [h.1];exact cmp
    have hi := step_jle τ atPC _ _ _ ht;rw [if_neg c] at hi
    obtain ⟨u,z,i,f,go,loc,good,cost⟩ := ix _ _ s (by omega) bodySite hi h
    have restart := step_jump τ loc _ jmp
    obtain ⟨v,last,j,g,rest,fin,ok,budget⟩ := iy pc _ z allow sub restart good
    have r := CallerBank.room sub;simp only [Code.native,Cmd.len] at r
    have fee := (CallerBank.test_bound P H w a b _ s (h.1.symm ▸ fit) (by omega)
      (by omega : pc+1+(body.native Q).len+1 ≤ P.length)).trans unitLe
    have jump := (CallerBank.jump_bound P H w pc z good.2.2.zero (by omega)).trans unitLe
    exact ⟨_,_,_,_,(((test_travels (τ:=τ) atPC _ _ _ ht).trans go).trans (test_travels (τ:=τ) loc 0 0 _ jmp)).trans rest,
      fin,ok,by simp only [Nat.add_mul,one_mul];omega⟩

end DirectedHamiltonicity.Main.CycleReduction.OuterMachine

namespace DirectedHamiltonicity.Main.CycleReduction.OuterMachine

open TargetedSamplers TargetedSamplers.Structured GuestMemory

private theorem at_halt {P : Program} {τ : Tapes} {k : ℕ} (h : (P.config τ k).halted=true) :
    P.final τ=some (P.config τ k) := by
  classical
  have existsK : ∃ j, (P.config τ j).halted=true := ⟨k,h⟩
  rw [Program.final,dif_pos existsK]
  let i := Nat.find existsK
  have le : i ≤ k := Nat.find_min' existsK h
  have stop : (P.config τ i).halted=true := Nat.find_spec existsK
  have fix : Function.IsFixedPt (P.step τ) (P.config τ i) := by simp [Function.IsFixedPt,Program.step,stop]
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
  change some (P.config τ i)=some ((P.step τ)^[i+d] State.init)
  rw [Nat.add_comm i d,Function.iterate_add_apply];exact congrArg some (fix.iterate d).symm

theorem native_runs {Q τ w c d k} (ev : Eval Q τ w c initial d k) :
    let P := (c.native Q).program
    P.RunsIn τ (k*unit Q P c.cap w+1) (some d.bank.out) := by
  let cmd := c.native Q
  let P := cmd.program
  let s : Store := ⟨fun _ => 0,[]⟩
  have sub : Contains P 0 (cmd.compile 0) := ⟨[],[.halt],rfl,rfl⟩
  have dest : P[cmd.len]?=some .halt := by
    change (cmd.compile 0++[Instr.halt])[cmd.len]?=_
    rw [List.getElem?_append_right (by simp)];simp
  have start : Located State.init 0 s := ⟨rfl,rfl,rfl,rfl,rfl⟩
  have init : Good s initial := ⟨rfl,fun _ => rfl,rfl,rfl,fun _ => le_rfl⟩
  obtain ⟨u,t,j,fee,path,atEnd,good,pay⟩ := native ev P c.cap 0 State.init s le_rfl sub start init
  have stopPC : u.pc=cmd.len := by simpa using atEnd.counter
  have terminal : (P.step τ u).halted=true := by simp [Program.step,atEnd.live,stopPC,dest]
  have reached : P.config τ (j+1)=P.step τ u := by
    change (P.step τ)^[j+1] State.init=_;rw [Function.iterate_succ_apply',path.1]
  have final := at_halt (P:=P) (τ:=τ) (k:=j+1) (reached.symm ▸ terminal)
  have out := congrArg Store.out good.1
  change t.out=d.bank.out at out
  refine ⟨_,final,?_,?_⟩
  · rw [reached];simp [Program.step,atEnd.live,stopPC,dest,path.2,State.init];exact pay
  · rw [reached];simp [State.result,Program.step,atEnd.live,stopPC,dest,atEnd.normal,atEnd.output,out]

private theorem polynomial_bound (p : Polynomial ℕ) :
    ∃ c d : ℕ, ∀ x : ℕ, 1 ≤ x → p.eval x ≤ c*x^d := by
  induction p using Polynomial.induction_on' with
  | monomial d c => exact ⟨c,d,fun x _ => by simp⟩
  | add p r hp hr =>
    obtain ⟨a,k,h⟩ := hp
    obtain ⟨c,d,g⟩ := hr
    refine ⟨a+c,max k d,fun x hx => ?_⟩
    rw [Polynomial.eval_add,Nat.add_mul]
    exact Nat.add_le_add ((h x hx).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (le_max_left ..))))
      ((g x hx).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (le_max_right ..))))

theorem executes_of_controller {Q : Program} {A k : ℕ} (h : BoundedController Q A k) : ExecutesSearch Q A k := by
  obtain ⟨c,W,J,controller⟩ := h
  let P := (c.native Q).program
  let m := 2048+8*Guest.callFactor Q
  let h0 := 300+c.cap+P.length.size
  let p : Polynomial ℕ := J*(Polynomial.C m*(W+Polynomial.C h0))+1
  obtain ⟨C,j,bound⟩ := polynomial_bound p
  refine ⟨P,(C+1:ℕ),j,by positivity,?_⟩
  intro n adj coins
  obtain ⟨d,i,ev,out,time⟩ := controller n adj coins
  have runs := native_runs ev
  rw [out] at runs
  refine ⟨_,runs,?_⟩
  let S := searchWork A k n
  have spos : 0<S := by dsimp [S,searchWork];positivity
  have formula : p.eval (n+1)=J.eval (n+1)*unit Q P c.cap (W.eval (n+1))+1 := by
    simp only [p,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one];unfold unit m h0;ring
  have cost : i*unit Q P c.cap (W.eval (n+1))+1 ≤ S*p.eval (n+1) := by
    rw [formula,Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ time) spos
  have maj := cost.trans (Nat.mul_le_mul_left S (bound (n+1) (by omega)))
  have res : i*unit Q P c.cap (W.eval (n+1))+1 ≤ (C+1)*S*(n+1)^j := by
    calc
      _ ≤ S*(C*(n+1)^j) := maj
      _ ≤ S*((C+1)*(n+1)^j) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
      _ = _ := by ring
  exact_mod_cast res

end DirectedHamiltonicity.Main.CycleReduction.OuterMachine

open TargetedSamplers DirectedHamiltonicity.Main.CycleReduction DirectedHamiltonicity.Main.CycleReduction.OuterMachine

theorem solution (Q : Program) (A k : ℕ) : BoundedController Q A k → ExecutesSearch Q A k := by
  exact executes_of_controller
