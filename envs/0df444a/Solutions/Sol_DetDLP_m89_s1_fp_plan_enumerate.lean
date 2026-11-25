-- Prove2me | solution 1 for DetDLP.m89_s1_fp_plan_enumerate
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T02:15:39.686531+00:00
-- url     : https://prove2.me/submissions/8b40955d-bb0d-4609-bdfa-a7df85ee8468

import Definitions.Def_DetDLP_M89_S1_Plans
import Definitions.Def_DetDLP_PolyTBridge
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_DetDLP_m89_s1_word_pipe
import Theorems.Thm_DetDLP_stage1_complexity_dominance
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul

set_option autoImplicit false
namespace DetDLP.m89_affine_enum

variable {p : ℕ} [Fact p.Prime]

/-- The residue hit at hash-table index `u`; all intermediate residues can be computed modulo `p`. -/
def pre (p a b u : ℕ) : ℕ := ((a^(p-2) % p) * (u+p-b)) % p

private theorem cast_pre {a b u : ℕ} (ha : 1 ≤ a) (hap : a < p) (hb : b < p) :
    (pre p a b u : ZMod p) = (a : ZMod p)⁻¹ * ((u : ZMod p) - b) := by
  have ha' : (a : ZMod p) ≠ 0 := by
    intro he; have h := congrArg ZMod.val he; rw [ZMod.val_natCast_of_lt hap,ZMod.val_zero] at h; omega
  have hp := (Fact.out : Nat.Prime p).two_le
  have hi : (a : ZMod p)^(p-2) = (a : ZMod p)⁻¹ := by
    apply (mul_left_cancel₀ ha')
    rw [mul_inv_cancel₀ ha',←pow_succ', show p-2+1=p-1 by omega]
    exact ZMod.pow_card_sub_one_eq_one ha'
  have hb' : b ≤ u+p := by omega
  simp [pre,Nat.cast_sub hb',hi]

private theorem hash_pre {a b u : ℕ} (ha : 1 ≤ a) (hap : a < p) (hb : b < p) (hu : u < p) :
    (a * pre p a b u + b) % p = u := by
  have ha' : (a : ZMod p) ≠ 0 := by
    intro he; have h := congrArg ZMod.val he; rw [ZMod.val_natCast_of_lt hap,ZMod.val_zero] at h; omega
  have hh : ((a * pre p a b u + b : ℕ) : ZMod p) = u := by
    push_cast; rw [cast_pre ha hap hb,←mul_assoc,mul_inv_cancel₀ ha',one_mul,sub_add_cancel]
  simpa only [ZMod.val_natCast,ZMod.val_natCast_of_lt hu,Nat.mod_eq_of_lt hu] using congrArg ZMod.val hh

private theorem pre_hash {a b : ℕ} (ha : 1 ≤ a) (hap : a < p) (hb : b < p) (x : ZMod p) :
    (pre p a b ((a*x.val+b)%p) : ZMod p) = x := by
  have ha' : (a : ZMod p) ≠ 0 := by
    intro he; have h := congrArg ZMod.val he; rw [ZMod.val_natCast_of_lt hap,ZMod.val_zero] at h; omega
  rw [cast_pre ha hap hb]; simp [ha']

def unitAt (p : ℕ) [Fact p.Prime] (v : ℕ) : Option (ZMod p)ˣ :=
  if h : (v : ZMod p) = 0 then none else some (Units.mk0 (v : ZMod p) h)

private theorem unitAt_spec {x : (ZMod p)ˣ} {v : ℕ} : unitAt p v = some x ↔ (v : ZMod p) = (x : ZMod p) := by
  unfold unitAt; split
  · rename_i h; simp [h, Ne.symm x.ne_zero]
  · simp only [Option.some.injEq]; exact ⟨fun h => congrArg Units.val h,fun h => Units.ext h⟩

def block (p T a b : ℕ) [Fact p.Prime] : List (ZMod p)ˣ :=
  (List.range (min T p)).filterMap (fun u => unitAt p (pre p a b u))

theorem block_spec {m T : ℕ} (s : FpSeed p m) (i : Fin m) :
    let a := (s i).1.val + 1; let b := (s i).2.val
    (block p T a b).Nodup ∧ (block p T a b).toFinset = fpFactorBlock (p := p) T s i := by
  intro a b
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hap : a < p := by have h := (s i).1.isLt; dsimp [a]; omega
  have hb : b < p := (s i).2.isLt
  have hp := (Fact.out : Nat.Prime p).pos
  have inject : ∀ u ∈ List.range (min T p), ∀ v ∈ List.range (min T p), pre p a b u = pre p a b v → u = v := by
    intro u hu v hv h
    rw [List.mem_range] at hu hv
    rw [← hash_pre ha hap hb (hu.trans_le (min_le_right ..)),h,hash_pre ha hap hb (hv.trans_le (min_le_right ..))]
  constructor
  · unfold block
    change ((List.range (min T p)).filterMap (unitAt p ∘ pre p a b)).Nodup
    rw [← List.filterMap_map]
    have nd := List.Nodup.map_on inject List.nodup_range
    have hmap : ∀ (v : ℕ) (_ : v ∈ (List.range (min T p)).map (pre p a b)), v < p := by
      intro v hv; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv; exact Nat.mod_lt _ hp
    -- Only residues in the canonical range occur in this list.
    generalize he : (List.range (min T p)).map (pre p a b) = li at nd hmap ⊢
    clear he inject
    induction li with
    | nil => simp
    | cons q qs ih =>
      obtain ⟨hn,hd⟩ := List.nodup_cons.mp nd
      have hqs := ih hd (fun v hv => hmap v (List.mem_cons_of_mem _ hv))
      cases hq : unitAt p q with
      | none => simpa [List.filterMap_cons,hq] using hqs
      | some x =>
        simp only [List.filterMap_cons,hq,List.nodup_cons]
        refine ⟨?_,hqs⟩
        intro hx; obtain ⟨r,hr,hx⟩ := List.mem_filterMap.mp hx
        have hval := congrArg ZMod.val ((unitAt_spec.mp hq).trans (unitAt_spec.mp hx).symm)
        rw [ZMod.val_natCast_of_lt (hmap q (List.mem_cons_self ..)),ZMod.val_natCast_of_lt (hmap r (List.mem_cons_of_mem _ hr))] at hval
        exact hn (hval ▸ hr)
  · ext x
    simp only [List.mem_toFinset,block,List.mem_filterMap,List.mem_range,unitAt_spec,fpFactorBlock,Finset.mem_filter,Finset.mem_univ,true_and]
    change (∃ u, u < min T p ∧ (pre p a b u : ZMod p) = ↑x) ↔ decide ((a*(x : ZMod p).val+b)%p < T) = true
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨u,hu,he⟩
      have hval := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (a := pre p a b u) (Nat.mod_lt _ hp)] at hval
      rw [←hval,hash_pre ha hap hb (hu.trans_le (min_le_right ..))]; exact hu.trans_le (min_le_left ..)
    · intro hu
      exact ⟨_,lt_min hu (Nat.mod_lt _ hp),pre_hash ha hap hb _⟩

end DetDLP.m89_affine_enum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.m89_enum_pad
open PolyTBridge
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork.TM

inductive Label where
  | init | loop | double | two1 | two2 | back | one | delim | drain | write | halt
  deriving DecidableEq, Fintype

def inst : Label → Op Label
  | .init => .push .tmp true .loop
  | .loop => .read true .raw fun b => if b = some true then .double else .delim
  | .double => .read true .tmp fun b => if b.isSome then .two1 else .back
  | .two1 => .push (.hi .main) true .two2
  | .two2 => .push (.hi .main) true .double
  | .back => .read true (.hi .main) fun b => if b.isSome then .one else .loop
  | .one => .push .tmp true .back
  | .delim => .push .raw false .drain
  | .drain => .read true .tmp fun b => if b.isSome then .write else .halt
  | .write => .push .raw true .drain
  | .halt => .stop

def mem (w : List Bool) (n h : ℕ) : Mem
  | .raw => w
  | .tmp => List.replicate n true
  | .hi .main => List.replicate h true
  | _ => []

@[simp] theorem mraw (w z : List Bool) (n h : ℕ) : Function.update (mem w n h) .raw z = mem z n h := by
  funext i; cases i with
  | hi j => cases j <;> rfl
  | _ => rfl
@[simp] theorem mtmp (w : List Bool) (n h k : ℕ) : Function.update (mem w n h) .tmp (List.replicate k true) = mem w k h := by
  funext i; cases i with
  | hi j => cases j <;> rfl
  | _ => rfl
@[simp] theorem mhi (w : List Bool) (n h k : ℕ) : Function.update (mem w n h) (.hi .main) (List.replicate k true) = mem w n k := by
  funext i; cases i with
  | hi i => cases i <;> rfl
  | _ => rfl

abbrev G := Goes inst .init

private theorem tmpPop {q t : Label} (n h : ℕ) (w : List Bool) (f : Option Bool → Label)
    (hq : inst q = .read true .tmp f) (ht : f (some true) = t) : G 3 q (mem w (n+1) h) (some t) (mem w n h) := by
  simpa only [mem,afterRead,if_true,List.replicate_succ,List.tail_cons,List.head?_cons,ht,mtmp] using
    (go_read (ops := inst) (q:=q) (start:=.init) (d:=mem w (n+1) h) true .tmp f hq)

private theorem tmpZero {q t : Label} (h : ℕ) (w : List Bool) (f : Option Bool → Label)
    (hq : inst q = .read true .tmp f) (ht : f none = t) : G 3 q (mem w 0 h) (some t) (mem w 0 h) := by
  convert (go_read (ops := inst) (q:=q) (start:=.init) (d:=mem w 0 h) true .tmp f hq) using 1
  · change some t = some (f none); rw [ht]
  · exact (mtmp w 0 h 0).symm

private theorem pushTmp (q t : Label) (w : List Bool) (n h : ℕ) (hq : inst q = .push .tmp true t) :
    G 2 q (mem w n h) (some t) (mem w (n+1) h) := by
  convert (go_push (ops:=inst) (q:=q) (start:=.init) (d:=mem w n h) .tmp true hq) using 1
  exact (mtmp w n h (n+1)).symm

private theorem pushHi (q t : Label) (w : List Bool) (n h : ℕ) (hq : inst q = .push (.hi .main) true t) :
    G 2 q (mem w n h) (some t) (mem w n (h+1)) := by
  convert (go_push (ops:=inst) (q:=q) (start:=.init) (d:=mem w n h) (.hi .main) true hq) using 1
  exact (mhi w n h (h+1)).symm

private theorem double (w : List Bool) (n h : ℕ) : G (7*n+3) .double (mem w n h) (some .back) (mem w 0 (2*n+h)) := by
  induction n generalizing h with
  | zero => simpa using tmpZero (q:=.double) (t:=.back) h w _ rfl rfl
  | succ n ih =>
    have a := tmpPop (q:=.double) (t:=.two1) n h w _ rfl rfl
    have b := pushHi .two1 .two2 w n h rfl
    have c := pushHi .two2 .double w n (h+1) rfl
    simpa only [show 7*(n+1)+3=3+2+2+(7*n+3) by omega,show 2*(n+1)+h=2*n+(h+1+1) by omega] using
      ((a.trans b).trans c).trans (ih (h+1+1))

private theorem back (w : List Bool) (n h : ℕ) : G (5*h+3) .back (mem w n h) (some .loop) (mem w (n+h) 0) := by
  induction h generalizing n with
  | zero =>
    convert (go_read (ops:=inst) (q:=.back) (start:=.init) (d:=mem w n 0) true (.hi .main) _ rfl) using 1
    · rfl
    · exact (mhi w n 0 0).symm
  | succ k ih =>
    have a : G 3 .back (mem w n (k+1)) (some .one) (mem w n k) := by
      convert (go_read (ops:=inst) (q:=.back) (start:=.init) (d:=mem w n (k+1)) true (.hi .main) _ rfl) using 1
      · rfl
      · exact (mhi w n (k+1) k).symm
    simpa only [show 5*(k+1)+3=3+2+(5*k+3) by omega,show n+(k+1)=n+1+k by omega] using
      (a.trans (pushTmp .one .back w n k rfl)).trans (ih (n+1))

private theorem drain (w : List Bool) (n : ℕ) : G (5*n+4) .drain (mem w n 0) none (mem (List.replicate n true ++ w) 0 0) := by
  induction n generalizing w with
  | zero => exact (tmpZero (q:=.drain) (t:=.halt) 0 w _ rfl rfl).trans (go_stop rfl)
  | succ n ih =>
    have a := tmpPop (q:=.drain) (t:=.write) n 0 w _ rfl rfl
    have c : G 2 .write (mem w n 0) (some .drain) (mem (true::w) n 0) := by
      convert (go_push (ops:=inst) (q:=.write) (start:=.init) (d:=mem w n 0) .raw true rfl) using 1
      exact (mraw w (true::w) n 0).symm
    convert (a.trans c).trans (ih (true::w)) using 1
    · omega
    · rw [List.replicate_succ',List.append_assoc]; rfl

def fmt (k : ℕ) (w : List Bool) := List.replicate k true ++ false :: w

private theorem loop (w : List Bool) (k n : ℕ) :
    G (22*(2^k*n) - 17*n + 9*k + 9) .loop (mem (fmt k w) n 0) none (mem (fmt (2^k*n) w) 0 0) := by
  induction k generalizing n with
  | zero =>
    have a : G 3 .loop (mem (false::w) n 0) (some .delim) (mem w n 0) := by
      convert (go_read (ops:=inst) (q:=.loop) (start:=.init) (d:=mem (false::w) n 0) true .raw _ rfl) using 1
      · rfl
      · exact (mraw (false::w) w n 0).symm
    have c : G 2 .delim (mem w n 0) (some .drain) (mem (false::w) n 0) := by
      convert (go_push (ops:=inst) (q:=.delim) (start:=.init) (d:=mem w n 0) .raw false rfl) using 1
      exact (mraw w (false::w) n 0).symm
    simp only [pow_zero,one_mul,Nat.mul_zero,Nat.add_zero]; unfold fmt
    change G (22*n-17*n+9) .loop (mem (false::w) n 0) none _
    apply ((a.trans c).trans (drain (false::w) n)).mono; omega
  | succ k ih =>
    have a : G 3 .loop (mem (fmt (k+1) w) n 0) (some .double) (mem (fmt k w) n 0) := by
      convert (go_read (ops:=inst) (q:=.loop) (start:=.init) (d:=mem (fmt (k+1) w) n 0) true .raw _ rfl) using 1
      · rfl
      · exact (mraw _ (fmt k w) n 0).symm
    have d := double (fmt k w) n 0
    simp only [Nat.add_zero] at d
    have c := back (fmt k w) 0 (2*n)
    simp only [Nat.zero_add] at c
    -- The geometric sum of all previous doublings is at most twice the final output.
    have h := ((a.trans d).trans c).trans (ih (2*n))
    clear a d c
    -- Stronger potential: charge the current 17*n to the increase in the live count.
    rw [show 2^(k+1)*n = 2^k*(2*n) by rw [pow_succ]; ring]
    apply h.mono
    have hx : 2*n ≤ 2^k*(2*n) := Nat.le_mul_of_pos_left _ (by positivity)
    omega

/-- Expand the unary header while retaining every payload bit. Both budgets are linear in
    the expanded header, payload and initial header; the constants are independent of all three. -/
theorem machine : ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (C : ℕ), ∀ k w,
    let B := (C*(2^k+k+w.length+1) : ℕ)
    RunsWithin M o (fmt k w) (fmt (2^k) w) B B := by
  let P := table inst .init
  let s := Fintype.card Port
  refine ⟨GuardedCompiler.primitive P, P.outputStack, 256*(s+1), ?_⟩
  intro k w
  have h := (pushTmp .init .loop (fmt k w) 0 0 rfl).trans (loop w k 1)
  obtain ⟨reg,n,hn,tr⟩ := h (fun _ => false)
  have hstart : BitProgram.initial P (fmt k w) = cfg (some Label.init) (fun _ => false) (mem (fmt k w) 0 0) := by
    refine congrArg (BitProgram.Cfg.mk _ _) ?_
    funext j; obtain ⟨i,rfl⟩ := port.surjective j
    cases i with
    | raw => simp [P,table,physical,mem]
    | tmp => simp [P,table,physical,mem]
    | hi j => cases j <;> simp [P,table,physical,mem]
    | lo j => cases j <;> simp [P,table,physical,mem]
  rw [←hstart] at tr
  have ho : (cfg (Q:=Label) none reg (mem (fmt (2^k*1) w) 0 0)).stacks P.outputStack = fmt (2^k) w := by simp [P,cfg,table,physical,mem]
  have run := CompileSpace.compile_runsWithin_from_time P tr rfl ho
  have len : (fmt k w).length = k+w.length+1 := by simp [fmt]; omega
  have t : n ≤ 22*2^k+9*k+11 := by simp only [Nat.mul_one] at hn; omega
  let u := 2^k+k+w.length+1
  have hs : 2*((fmt k w).length)+n+15 ≤ 256*u := by dsimp [u]; rw [len]; omega
  apply runsWithin_mono_local run
  · exact_mod_cast (show 7*n ≤ (256*(s+1))*u by dsimp [u]; nlinarith [Nat.zero_le (s*(2^k+k+w.length+1))])
  · exact_mod_cast (show s*((fmt k w).length+n+(fmt k w).length+15) ≤ 256*(s+1)*u by
      have hmul := Nat.mul_le_mul_left s hs
      nlinarith [Nat.zero_le u])

end DetDLP.m89_enum_pad

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace DetDLP.m89_enum_words
open M89S1 m89_affine_enum m89_enum_pad Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk
  Groundwork.PolyT.map Groundwork.PolyT.flatMap Groundwork.PolyT.filter Groundwork.PolyT.filterMap
  Groundwork.PolyT.mod Groundwork.PolyT.mul Groundwork.PolyT.div Groundwork.PolyT.idxOf Groundwork.PolyT.length
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_some__e6a32bd6af45

abbrev Word := List Bool
abbrev State := Bool × Bool × Word × List Word
def scan (s : State) (b : Bool) : State :=
  bif s.1 then bif s.2.1 then s else (false,true,b::s.2.2.1,s.2.2.2)
  else bif s.2.1 then bif b then (true,false,s.2.2.1,s.2.2.2) else (false,false,[],s.2.2.1.reverse :: s.2.2.2)
  else bif b then (false,true,[],s.2.2.2) else (true,true,[],s.2.2.2)
def fields (w : Word) := (w.foldl scan (false,false,[],[])).2.2.2.reverse

private theorem scan_size (s : State) (b : Bool) : len (scan s b) ≤ len s + 5 := by
  obtain ⟨i,j,w,l⟩ := s; cases i <;> cases j <;> cases b <;> simp [scan,len_pair,len_bools,len_bool,len_cons,len_nil] <;> omega
@[local fun_prop] theorem fields_poly : PolyT fields := by
  have h : PolyT (fun w : Word => w.foldl scan (false,false,[],[])) := by
    refine foldl_add (g:=fun _ => scan) (by fun_prop) (by fun_prop) (by unfold scan; fun_prop) ⟨_,PB.const 5,?_⟩
    exact fun _ s e _ => scan_size s e
  unfold fields; fun_prop

private theorem scan_frame (w acc : Word) (l : List Word) : (Encoding.frame w).foldl scan (false,true,acc,l) = (false,false,[],(acc.reverse++w)::l) := by
  induction w generalizing acc with
  | nil => simp [Encoding.frame,scan]
  | cons b w ih => change (Encoding.frame w).foldl scan (false,true,b::acc,l) = _; simpa using ih (b::acc)

@[simp] theorem fields_encode (l : List Word) : fields (Encoding.encodeList id l) = l := by
  have run (L a : List Word) : (Encoding.encodeList id L).foldl scan (false,false,[],a) = (true,true,[],L.reverse++a) := by
    induction L generalizing a with
    | nil => rfl
    | cons w L ih =>
      change (Encoding.frame w ++ Encoding.encodeList id L).foldl scan (false,true,[],a) = _
      rw [List.foldl_append,scan_frame]; simpa using ih (w::a)
  simp [fields,run]

private theorem frame_flat (w : Word) : Encoding.frame w = w.flatMap (fun b => [true,b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [Encoding.frame,List.flatMap] using congrArg (fun z => true::b::z) ih

@[local fun_prop] theorem enc_poly {α : Type} [Enc α] {g : α → List Word} (hg : PolyT g) : PolyT (fun x => Encoding.encodeList id (g x)) := by
  have he (l : List Word) : Encoding.encodeList id l = l.flatMap (fun u => true :: Encoding.frame u) ++ [false] := by
    induction l with
    | nil => rfl
    | cons w l ih => change true :: (Encoding.frame w ++ Encoding.encodeList id l) = _; simp [ih,List.flatMap,List.append_assoc]
  simp only [he,frame_flat]; fun_prop

def mr (d a : ℕ) (b : Bool) (v : ℕ) : ℕ := ((v*v)*(if b then a else 1)) % (d+1)
def powResidue (d a e : ℕ) := e.bits.foldr (mr d a) (1%(d+1))

private theorem fold_mod (d a : ℕ) (l : Word) : l.foldr (mr d a) (1%(d+1)) = a^(bval l) % (d+1) := by
  induction l with
  | nil => simp [bval_nil]
  | cons b l ih =>
    rw [List.foldr_cons,ih,bval_cons,pow_add,pow_mul']; unfold mr
    rw [←Nat.mod_mul_mod (a^(bval l)%(d+1)*(a^(bval l)%(d+1))) _ (d+1),←Nat.mul_mod]
    cases b <;> simp [pow_two,Nat.mod_mul_mod]

theorem powResidue_spec (d a e : ℕ) : powResidue d a e = a^e%(d+1) := by simp [powResidue,fold_mod,bval_bits]

@[local fun_prop] theorem powResidue_poly {α : Type} [Enc α] {d a e : α → ℕ} (hd : PolyT d) (ha : PolyT a) (he : PolyT e) : PolyT (fun x => powResidue (d x) (a x) (e x)) := by
  obtain ⟨t,ht,_,hlen⟩ := len_bound (show PolyT (fun x => d x+1) by fun_prop)
  apply foldr (g:=fun x => mr (d x) (a x)) (by fun_prop) (by fun_prop) (by unfold mr; fun_prop)
  refine ⟨_,ht,fun x k => ?_⟩; rw [fold_mod]
  exact (len_nat_mono (Nat.mod_lt _ (Nat.succ_pos _)).le).trans (hlen x)

def plen (w : Word) := (w.idxOf false)
def raw (w : Word) := w.drop (plen w+1)
def parts (w : Word) := fields ((fields w).getD 1 []).tail
def prime (w : Word) := bval ((fields w).getD 0 [])
def large (w : Word) := ((fields w).getD 1 []).headD false
def tval (w : Word) := if large w then bval ((parts w).getD 0 []) else prime w
def seed (w : Word) := (parts w).getD 1 []
def width (w : Word) := (prime w-1).bits.length
def nblock (w : Word) := if large w then (seed w).length/(2*width w) else 2
def coord (w : Word) (b i : ℕ) := bval (((w.drop (i*b)).take b).reverse)
def tally (w : Word) := fmt (tval w).bits.length w

@[local fun_prop] theorem tally_poly : PolyT tally := by
  unfold tally fmt tval parts prime large
  simp only [← List.map_const (l:=(_ : Word)) (b:=true)]
  fun_prop

def indices (w : Word) := List.range w.length
@[local fun_prop] theorem indices_poly {α : Type} [Enc α] {f : α → Word} (hf : PolyT f) : PolyT (fun x => indices (f x)) := by
  apply Groundwork.PolyT.range
  change PolyT (fun x => List.replicate (f x).length ())
  simp only [←List.map_const (l:=(_ : Word)) (b:=())]; fun_prop

def row (p a b : ℕ) (us : List ℕ) : List ℕ :=
  us.filterMap (fun u => let v := (powResidue (p-1) a (p-2)*(u+p-b)) % p
                         if v = 0 then none else some v)

@[local fun_prop] theorem row_poly {α : Type} [Enc α] {p a b : α → ℕ} {us : α → List ℕ}
    (hp : PolyT p) (ha : PolyT a) (hb : PolyT b) (hu : PolyT us) : PolyT (fun x => row (p x) (a x) (b x) (us x)) := by
  unfold row; apply Groundwork.PolyT.filterMap
  · let v (x : α × ℕ) := powResidue (p x.1-1) (a x.1) (p x.1-2)*(x.2+p x.1-b x.1)%p x.1
    have h : PolyT v := by unfold v; fun_prop
    change PolyT (fun x : α × ℕ => if v x = 0 then none else some (v x))
    fun_prop
  · exact hu

@[local fun_prop] theorem co_poly {α : Type} [Enc α] {w : α → Word} {b i : α → ℕ} (hw : PolyT w) (hb : PolyT b) (hi : PolyT i) :
    PolyT (fun x => coord (w x) (b x) (i x)) := by unfold coord; fun_prop

@[local fun_prop] theorem raw_poly : PolyT raw := by unfold raw plen; fun_prop
@[local fun_prop] theorem pr_poly : PolyT prime := by unfold prime; fun_prop
@[local fun_prop] theorem la_poly : PolyT large := by unfold large; fun_prop
@[local fun_prop] theorem se_poly : PolyT seed := by unfold seed parts; fun_prop
@[local fun_prop] theorem tv_poly : PolyT tval := by unfold tval parts; fun_prop
@[local fun_prop] theorem wi_poly : PolyT width := by unfold width; fun_prop
def output (w : Word) :=
  let v := raw w; let p := prime v
  let is := (indices w).filter (fun i => decide (i < nblock v))
  let us := (indices w).filter (fun u => decide (u < tval v ∧ u < p))
  let f := fun (i : ℕ) =>
    let a := if large v then coord (seed v) (width v) (2*i) else 1
    let b := if large v then coord (seed v) (width v) (2*i+1) else 0
    encodeNatListBin (row p a b us)
  Encoding.encodeList id (is.map f)

@[local fun_prop] theorem output_poly : PolyT output := by
  have hm : PolyT nblock := by unfold nblock; fun_prop
  unfold output; dsimp only
  apply enc_poly
  apply Groundwork.PolyT.map
  · apply w5_M6Sort.encode_poly
    apply row_poly <;> fun_prop
  · fun_prop

end DetDLP.m89_enum_words

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.m89_enum_spec
open M89S1 m89_affine_enum m89_enum_pad m89_enum_words Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def arg {m : ℕ} (p : ℕ) (L : Option (ℕ × FpSeed p m)) := Encoding.encodeList id [countWord p,m89_fp_plan_word L]
@[simp] theorem raw_fmt (k : ℕ) (w : Word) : raw (fmt k w) = w := by
  have h : plen (fmt k w) = k := by
    simp [plen,fmt,List.idxOf_append_of_notMem]
  rw [raw,h]; simp [fmt,List.drop_append]

@[simp] theorem bval_count (n : ℕ) : bval (countWord n) = n := by by_cases hn : n = 0; subst n; rfl; simp [countWord,hn,bval_bits]

theorem width_eq (p : ℕ) (hp : 2 ≤ p) : (p-1).size = bitLen p := by
  apply le_antisymm
  · apply Nat.size_le.2; have h : p ≤ 2^(bitLen p) := Nat.le_pow_clog (by decide) _; omega
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2; have h := Nat.size_le.mp (le_refl (p-1).size); omega

private theorem bval_fixed (b n : ℕ) (hn : n < 2^b) : bval (List.ofFn (fun i : Fin b => n.testBit i.val)) = n := by
  induction b generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n; rfl
  | succ b ih =>
    rw [List.ofFn_succ,bval_cons]
    simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
    rw [ih (n/2) ((Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [pow_succ] using hn)),Nat.testBit_zero]
    by_cases h : n % 2 = 1 <;> simp [h] <;> omega

private theorem bval_digit (b n : ℕ) (hn : n < 2^b) : bval (digitWord b n).reverse = n := by
  apply Eq.trans _ (bval_fixed b n hn); apply congrArg bval
  apply List.ext_getElem (by simp [digitWord]); intro j hj hk
  simp only [digitWord,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn,Fin.val_rev]
  congr 1; simp only [List.length_ofFn] at hk; omega

theorem load_coord {p m : ℕ} (S : FpSeed p m) (i : Fin m) (k : Fin 2) :
    coord (List.ofFn (fpBits S)) (bitLen p) (2*i.val+k.val) = fpWords S i k := by
  let b := bitLen p
  have bound : fpWords S i k < 2^b := by
    unfold fpWords; split
    · have h := (S i).1.isLt; have hh : p ≤ 2^b := Nat.le_pow_clog (by decide) p; omega
    · exact (S i).2.isLt.trans_le (Nat.le_pow_clog (by decide) p)
  have hslice : ((List.ofFn (fpBits S)).drop ((2*i.val + k.val)*b)).take b = digitWord b (fpWords S i k) := by
    have ij : 2*i.val + k.val < m*2 := by have := i.isLt; have := k.isLt; omega
    have reach := Nat.mul_le_mul_right b (show 2*i.val+k.val+1 ≤ m*2 by omega)
    rw [Nat.add_mul,Nat.one_mul] at reach
    apply List.ext_getElem (by simp only [digitWord,List.length_take,List.length_drop,List.length_ofFn]; change min b (m*2*b-(2*i.val+k.val)*b)=b; omega)
    intro j hj hk
    have jb : j < b := by simpa [digitWord] using hk
    let ix := finProdFinEquiv (finProdFinEquiv (i,k), (⟨j,jb⟩ : Fin b))
    have idx : ix.val = (2*i.val+k.val)*b+j := by simp [ix,finProdFinEquiv_apply_val]; ring
    rw [List.getElem_take,List.getElem_drop,List.getElem_ofFn]; change packBits (b:=b) (fpWords S) _ = _
    have eq : (⟨(2*i.val+k.val)*b+j,by omega⟩ : Fin (m*2*b)) = ix := Fin.ext idx.symm
    rw [eq]; simp [ix,packBits,digitWord]
  unfold coord; rw [hslice]; exact bval_digit b _ bound

private theorem filter_range (l t : ℕ) (ht : t ≤ l) : (List.range l).filter (fun u => decide (u<t)) = List.range t := by
  induction l, ht using Nat.le_induction with
  | base => apply List.filter_eq_self.mpr; intro a h; simpa using h
  | succ l hl ih => rw [List.range_succ,List.filter_append,ih]; simp [Nat.not_lt.mpr hl]

private theorem map_range {α : Type} (n : ℕ) (g : ℕ → α) : (List.range n).map g = List.ofFn (fun i : Fin n => g i.val) := by
  apply List.ext_getElem (by simp); intro i hi hj; simp [List.getElem_range]

theorem row_spec (p T a b : ℕ) [Fact p.Prime] : row p a b (List.range (min T p)) = (block p T a b).map (fun x : (ZMod p)ˣ => (x : ZMod p).val) := by
  rw [block,List.map_filterMap]; apply List.filterMap_congr; intro u hu
  have hp := (Fact.out : Nat.Prime p).pos
  have hpre : pre p a b u < p := Nat.mod_lt _ hp
  have hval := ZMod.val_natCast_of_lt (a:=pre p a b u) hpre
  have pp : p-1+1=p := by omega
  dsimp only; rw [powResidue_spec,pp]
  change (if pre p a b u = 0 then none else some (pre p a b u)) = _
  unfold unitAt; split
  · rename_i hh; simp [hh]
  · rename_i hh; have hz : (pre p a b u : ZMod p) ≠ 0 := by
      intro he; apply hh; rw [←hval,he,ZMod.val_zero]
    simp [hz,hval]

private theorem encode_map (l : List Nat) : encodeNatListBin l = Encoding.encodeList countWord l := rfl
private theorem encode_block {p : ℕ} [Fact p.Prime] (l : List (ZMod p)ˣ) :
    encodeNatListBin (l.map fun a : (ZMod p)ˣ => (a : ZMod p).val) = Encoding.encodeList (fun a : (ZMod p)ˣ => countWord (a : ZMod p).val) l := by
  induction l with
  | nil => rfl
  | cons a l ih => change true :: (_ ++ encodeNatListBin _) = true :: (_ ++ _); rw [ih]

private theorem output_rows (w : Word) (k m p T : ℕ) [Fact p.Prime] (a b : ℕ → ℕ)
    (hpp : prime w = p) (hT : tval w = T) (hm : nblock w = m) (hs : m ≤ (fmt k w).length)
    (ht : T ≤ (fmt k w).length)
    (hA : ∀ i : Fin m, (if large w then coord (seed w) (width w) (2*i.val) else 1) = a i)
    (hB : ∀ i : Fin m, (if large w then coord (seed w) (width w) (2*i.val+1) else 0) = b i) :
    output (fmt k w) = encodeFpFactorBlocks (fun i : Fin m => block p T (a i) (b i)) := by
  unfold output; simp only [raw_fmt,hpp,hT,hm,indices]; rw [filter_range _ m hs]
  have hpred : (fun u : ℕ => decide (u < T ∧ u < p)) = (fun u => decide (u < min T p)) := by funext u; simp
  rw [hpred,filter_range _ _ ((min_le_left ..).trans ht),map_range]
  unfold encodeFpFactorBlocks
  have hmap (l : List (List (ZMod p)ˣ)) : Encoding.encodeList id (l.map (fun v => Encoding.encodeList (fun a : (ZMod p)ˣ => countWord (a : ZMod p).val) v)) = Encoding.encodeList (Encoding.encodeList (fun a : (ZMod p)ˣ => countWord (a : ZMod p).val)) l := by
    induction l with | nil => rfl | cons v l ih => change true :: (_ ++ Encoding.encodeList id _) = true :: (_ ++ _); rw [ih]; rfl
  rw [←hmap,List.map_ofFn]; congr 1; congr 1; funext i
  rw [hA i,hB i,row_spec,encode_block]; rfl

theorem block_le (b : ℕ) : blockCount b ≤ b+2 := by
  apply max_le (by omega) (Nat.ceil_le.mpr ?_)
  have u : Nat.clog 2 (b+2) ≤ b+2 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (Nat.lt_pow_self (by decide)).le
  have v : 1 ≤ Nat.clog 2 (b+2) := Nat.clog_pos (by decide) (by omega)
  exact (Real.rpow_le_self_of_one_le (by exact_mod_cast v) (by norm_num)).trans (by exact_mod_cast u)

private theorem grow (b : ℕ) (hb : 20 ≤ b) : 8192*(b+2)+4 ≤ 2^(b-1) := by
  induction b, hb using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [show k+1-1 = (k-1)+1 by omega,pow_succ]; omega

theorem small (p : ℕ) (hs : ¬(64 ≤ p-1 ∧ 4096*blockCount (bitLen p) ≤ p-1)) : blockCount (bitLen p) = 2 := by
  let b := bitLen p
  have hm : 2 ≤ blockCount b := le_max_left ..
  have hp : p ≤ 4096*blockCount b+1 := by change ¬(64 ≤ p-1 ∧ 4096*blockCount b ≤ p-1) at hs; omega
  have h : p ≤ 4096*(b+2)+1 := by have := block_le b; omega
  have hl : b ≤ 20 := by
    by_contra! hx
    have he : 2^(b-1) < p := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).1 (show b-1 < b by omega)
    have := grow b (by omega); omega
  apply le_antisymm _ hm
  apply max_le le_rfl (Nat.ceil_le.mpr ?_)
  have hk : Nat.clog 2 (b+2) ≤ 16 := (Nat.clog_le_iff_le_pow (by decide)).2 (by norm_num; omega)
  have h16 : (16:ℝ)^((1:ℝ)/4) = 2 := by
    rw [show (16:ℝ) = (2:ℝ)^4 by norm_num,←Real.rpow_natCast_mul (by norm_num)]; norm_num
  change (Nat.clog 2 (b+2):ℝ)^((1:ℝ)/4) ≤ (2:ℝ)
  rw [←h16]; exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk) (by norm_num)

@[simp] theorem prime_arg {m : ℕ} (p : ℕ) (L : Option (ℕ × FpSeed p m)) : prime (arg p L) = p := by simp [prime,arg]
@[simp] theorem raw_large {p m : ℕ} (t : ℕ) (s : FpSeed p m) : large (arg p (some (t,s))) = true := by simp [large,arg,m89_fp_plan_word]
@[simp] theorem raw_small {p m : ℕ} : large (arg (m:=m) p none) = false := by simp [large,arg,m89_fp_plan_word]
@[simp] theorem parts_large {p m : ℕ} (t : ℕ) (s : FpSeed p m) : parts (arg p (some (t,s))) = [countWord t,List.ofFn (fpBits s)] := by simp [parts,arg,m89_fp_plan_word]
@[simp] theorem seed_large {p m : ℕ} (t : ℕ) (s : FpSeed p m) : seed (arg p (some (t,s))) = List.ofFn (fpBits s) := by simp [seed]
@[simp] theorem tval_large {p m : ℕ} (t : ℕ) (s : FpSeed p m) : tval (arg p (some (t,s))) = t := by simp [tval]
@[simp] theorem tval_small {p m : ℕ} : tval (arg (m:=m) p none) = p := by simp [tval]
@[simp] theorem width_arg {p m : ℕ} [Fact p.Prime] (L : Option (ℕ × FpSeed p m)) : width (arg p L) = bitLen p := by simp [width,Nat.size_eq_bits_len,width_eq p (Fact.out : Nat.Prime p).two_le]

theorem good_output {p : ℕ} [Fact p.Prime] (L : Option (ℕ × FpSeed p (blockCount (bitLen p)))) (hok : m89_fp_plan_ok L) :
    let w := arg p L
    ∃ F : Fin (blockCount (bitLen p)) → List (ZMod p)ˣ,
      (∀ i, (F i).Nodup ∧ (F i).toFinset = m89_fp_plan_block L i) ∧
      output (fmt (2^(tval w).bits.length) w) = encodeFpFactorBlocks F := by
  intro w; let b := bitLen p; let m := blockCount b
  have hp := (Fact.out : Nat.Prime p).two_le
  have hb : 1 ≤ b := Nat.clog_pos (by decide) hp
  let k := 2^(tval w).bits.length
  have ht : tval w ≤ (fmt k w).length := by
    have h : tval w < k := by dsimp [k]; rw [Nat.size_eq_bits_len]; exact Nat.size_le.mp le_rfl
    simp [fmt]; omega
  cases L with
  | none =>
    have hs := small p hok
    let S : FpSeed p m := fun _ => (⟨0,by omega⟩,0)
    let F := fun _ : Fin m => block p p 1 0
    refine ⟨F,?_,?_⟩
    · intro i; have h := block_spec (T:=p) S i
      change (block p p 1 0).Nodup ∧ (block p p 1 0).toFinset = fpFactorBlock (p:=p) p S i at h
      refine ⟨h.1,h.2.trans ?_⟩
      ext x; simp [fpFactorBlock,fpFactorMem,S,Nat.mod_lt _ (by omega : 0 < p),m89_fp_plan_block]
    · have hm : nblock w = m := by simp [nblock,w,m,b,hs]
      have hm' : m ≤ (fmt k w).length := by dsimp [m,b]; rw [hs]; change tval (arg (m:=m) p none) ≤ _ at ht; rw [tval_small] at ht; omega
      exact output_rows w k m p p (fun _ => 1) (fun _ => 0) (prime_arg ..) tval_small hm hm' (by simpa only [w,tval_small] using ht) (by simp [w]) (by simp [w])
  | some s =>
    obtain ⟨t,S⟩ := s
    let a := fun j => coord (List.ofFn (fpBits S)) b (2*j)
    let β := fun j => coord (List.ofFn (fpBits S)) b (2*j+1)
    let F := fun i : Fin m => block p t (a i) (β i)
    have hA (i : Fin m) : a i = (S i).1.val + 1 := by simpa [a,b,fpWords] using load_coord S i 0
    have hB (i : Fin m) : β i = (S i).2.val := by simpa [β,b,fpWords] using load_coord S i 1
    refine ⟨F,fun i => ?_,?_⟩
    · dsimp only [F]; rw [hA,hB]; exact block_spec S i
    · have hm : nblock w = m := by
        simp only [nblock,w,raw_large,if_true,seed_large,List.length_ofFn,width_arg]
        change m*2*b/(2*b)=m; rw [Nat.mul_assoc,Nat.mul_div_cancel _ (by positivity : 0 < 2*b)]
      have hlen : m ≤ w.length := by
        have frame_ge (s : Word) : s.length ≤ (Encoding.frame s).length := by
          induction s with | nil => simp | cons a s ih => change s.length+1 ≤ (Encoding.frame s).length+1+1; omega
        have enc_ge (u v : Word) : v.length ≤ (Encoding.encodeList id [u,v]).length := by
          simp [Encoding.encodeList]; have := frame_ge v; omega
        have h1 := enc_ge (countWord p) (m89_fp_plan_word (some (t,S)))
        have h2 := enc_ge (countWord t) (List.ofFn (fpBits S))
        rw [List.length_ofFn] at h2
        change m*2*b ≤ _ at h2
        
        change (true :: Encoding.encodeList id [countWord t,List.ofFn (fpBits S)]).length ≤ w.length at h1
        have hm' : m ≤ m*2*b := by nlinarith [Nat.mul_le_mul_left (m*2) hb]
        simp only [List.length_cons] at h1; omega
      have hlen' : w.length ≤ (fmt k w).length := by
        simp only [fmt,List.length_append,List.length_replicate,List.length_cons]
        exact (Nat.le_succ _).trans (Nat.le_add_left _ _)
      apply output_rows w k m p t a β (prime_arg ..) (tval_large ..) hm (hlen.trans hlen') (by simpa only [w,tval_large] using ht)
      · intro i; simp [w,a,b]
      · intro i; simp [w,β,b]

end DetDLP.m89_enum_spec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.m89_enum_growth
open M89S1 m89_enum_pad m89_enum_words m89_enum_spec
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem threshold (p m : ℕ) (hp : 2 ≤ p) (hm : 2 ≤ m) :
    (hashThreshold p (p-1) m (p-1) : ℝ) ≤ 9000*((m:ℝ)^2+(m:ℝ)*(p:ℝ)^((1:ℝ)/(m:ℝ))) := by
  let e := (1:ℝ)/(m:ℝ); let n := p-1; let r := (p:ℝ)^e; let D := (m:ℝ)^2+(m:ℝ)*r
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by simpa [e] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hmr
  have r1 : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ p by omega)) he
  have npos : (0:ℝ) < n := by exact_mod_cast (show 0 < p-1 by omega)
  have np : (n:ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have pn : (p:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast (show p ≤ 2*(p-1) by omega)
  have h16 : (16:ℝ)^e ≤ 16 := Real.rpow_le_self_of_one_le (by norm_num) he1
  have hx : (16*(n:ℝ))^e ≤ 16*r := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul h16 (Real.rpow_le_rpow (by positivity) np he) (by positivity) (by norm_num)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (16*(n:ℝ))^e by positivity)
  have qbound : (qStar m n : ℝ) ≤ 4096*(m:ℝ)+16*r+1 := by
    unfold qStar; rw [Nat.cast_max,Nat.cast_mul]
    change max (4096*(m:ℝ)) ((⌈(16*(n:ℝ))^e⌉₊:ℝ)) ≤ _
    apply max_le <;> linarith [Nat.cast_nonneg (α:=ℝ) m]
  have ht := Nat.ceil_lt_add_one (show 0 ≤ (p:ℝ)*(qStar m n : ℝ)/(n:ℝ) by positivity)
  have hr : (p:ℝ)*(qStar m n : ℝ)/(n:ℝ) ≤ 2*(qStar m n : ℝ) := by
    apply (div_le_iff₀ npos).2
    nlinarith only [mul_le_mul_of_nonneg_right pn (Nat.cast_nonneg (α:=ℝ) (qStar m n))]
  change (⌈(p:ℝ)*(qStar m n : ℝ)/(n:ℝ)⌉₊:ℝ) ≤ 9000*D
  have hrprod := mul_le_mul_of_nonneg_right hmr (show 0 ≤ r by linarith)
  dsimp only [D]; nlinarith [sq_nonneg ((m:ℝ)-1)]

private theorem block_fmt (p : ℕ) [Fact p.Prime] (L : Option (ℕ × FpSeed p (blockCount (bitLen p))))
    (hok : m89_fp_plan_ok L) : (tval (arg p L) : ℝ) ≤
       9000*((blockCount (bitLen p):ℝ)^2+(blockCount (bitLen p):ℝ)*(p:ℝ)^((1:ℝ)/(blockCount (bitLen p):ℝ))) := by
  let m := blockCount (bitLen p)
  have hm : 2 ≤ m := le_max_left ..
  cases L with
  | none =>
    rw [tval_small]; change ¬(64 ≤ p-1 ∧ 4096*m ≤ p-1) at hok
    have hp : p ≤ 4096*m+1 := by omega
    have hpr : (p:ℝ) ≤ 4096*(m:ℝ)+1 := by exact_mod_cast hp
    change _ ≤ 9000*((m:ℝ)^2+(m:ℝ)*(p:ℝ)^((1:ℝ)/(m:ℝ)))
    have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
    have h0 : 0 ≤ (m:ℝ)*(p:ℝ)^((1:ℝ)/(m:ℝ)) := by positivity
    nlinarith [sq_nonneg ((m:ℝ)-1)]
  | some pair =>
    rcases pair with ⟨t,S⟩; obtain ⟨_,_,rfl,_⟩ := hok; rw [tval_large]; exact threshold p m (Fact.out : Nat.Prime p).two_le hm

private theorem frame_len (w : Word) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with | nil => rfl | cons b w ih => change (Encoding.frame w).length+1+1=2*(w.length+1)+1; omega
private theorem two_len (x y : Word) : (Encoding.encodeList id [x,y]).length = 2*(x.length+y.length)+5 := by simp [Encoding.encodeList,frame_len]; omega
private theorem cw_len (n : ℕ) : (countWord n).length ≤ n.size+1 := by by_cases h : n=0 <;> simp [countWord,h,Nat.size_eq_bits_len]
private theorem size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
private theorem pow_size (n : ℕ) : 2^n.size ≤ 2*(n+1) := by
  cases h : n.size with
  | zero => simp only [pow_zero]; omega
  | succ k => have h' := (Nat.lt_size (m:=k) (n:=n)).mp (by omega); rw [pow_succ]; omega

private theorem lengths (p : ℕ) [Fact p.Prime] (L : Option (ℕ × FpSeed p (blockCount (bitLen p)))) :
    let b := bitLen p; let m := blockCount b; let w := arg p L; let t := tval w
    w.length + t.bits.length + 2^t.bits.length + 33 ≤ 2*b+7*t+8*(m*b)+70 := by
  intro b m w t
  have hcw : p.size ≤ b+1 := by
    apply Nat.size_le.2; rw [pow_succ]; have h : p ≤ 2^b := Nat.le_pow_clog (by decide) p
    have hpos : 0 < 2^b := by positivity
    omega
  have hcp := cw_len p; have hct := cw_len t; have hst := size_le_self t; have hpow := pow_size t
  rw [Nat.size_eq_bits_len]
  have hw : w.length ≤ 2*b+4*t+8*(m*b)+30 := by
    cases L with
    | none =>
      change (Encoding.encodeList id [countWord p,[false]]).length ≤ _
      rw [two_len]; simp only [List.length_cons,List.length_nil]; omega
    | some pair =>
      obtain ⟨T,S⟩ := pair; have he : T = t := (tval_large T S).symm
      change (Encoding.encodeList id [countWord p,true::Encoding.encodeList id [countWord T,List.ofFn (fpBits S)]]).length ≤ _
      rw [two_len,List.length_cons,two_len,List.length_ofFn,he]; change 2*((countWord p).length + (2*((countWord t).length + m*2*b)+5+1))+5 ≤ _
      nlinarith only [hct,hst,hcp,hcw]
  omega

theorem base : ∃ C : ℕ, ∀ (p : ℕ) [Fact p.Prime] (L : Option (ℕ × FpSeed p (blockCount (bitLen p)))), m89_fp_plan_ok L →
    let w := arg p L; let k := (tval w).bits.length
    ((w.length + k + 2^k + 33 : ℕ) : ℝ) ≤ mainSpaceBound C (bitLen p) := by
  obtain ⟨C,hC⟩ := stage1_complexity_dominance.2.2.1 1 1000000
  refine ⟨C,?_⟩; intro p inst L hok w k
  let b := bitLen p; let m := blockCount b; let t := tval w
  let r := (p:ℝ)^((1:ℝ)/(m:ℝ)); let D := (m:ℝ)^2+(m:ℝ)*r
  have h := (hC p p (Fact.out : Nat.Prime p).two_le (by omega)).2
  change polyBound 1 b * (1000000*D) ≤ mainSpaceBound C b at h
  apply le_trans _ h
  have hl : ((w.length+k+2^k+33:ℕ):ℝ) ≤ 2*(b:ℝ)+7*(t:ℝ)+8*((m:ℝ)*(b:ℝ))+70 := by exact_mod_cast lengths p L
  have hT : (t:ℝ) ≤ 9000*D := block_fmt p L hok
  have hm : (2:ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m from le_max_left ..)
  have hn : 0 ≤ (m:ℝ)*r := by dsimp [r]; positivity
  have hDm : (m:ℝ) ≤ D := by dsimp [D]; nlinarith [sq_nonneg ((m:ℝ)-1)]
  have hD : (1:ℝ) ≤ D := by linarith
  have h1 := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (α:=ℝ) b)
  have h2 := mul_le_mul_of_nonneg_right hDm (Nat.cast_nonneg (α:=ℝ) b)
  apply hl.trans; unfold polyBound; rw [pow_one,Nat.cast_one,one_mul]
  nlinarith only [hT,hm,hDm,hD,h1,h2,Nat.cast_nonneg (α:=ℝ) b]

end DetDLP.m89_enum_growth
set_option autoImplicit false
namespace DetDLP.m89_enum_final
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
private theorem absorb_prod (K k n b : ℕ) (hb : 1 ≤ b) : (K:ℝ) * (mainSpaceBound k b)^n ≤ mainSpaceBound (K+n*k) b := by
  let s := (b:ℝ)/(logSafe b)^((1:ℝ)/4)
  have hs : 1 ≤ s := scale_ge_one hb
  have W (i : ℕ) : mainSpaceBound i b = (2:ℝ)^((i:ℝ)*s) := by unfold mainSpaceBound s; congr 1; ring
  rw [W,W,← Real.rpow_mul_natCast (by norm_num)]
  have hK : (K:ℝ) ≤ (2:ℝ)^((K:ℝ)*s) := by
    calc (K:ℝ) ≤ (2:ℝ)^(K:ℝ) := by rw [Real.rpow_natCast]; exact_mod_cast (Nat.lt_two_pow_self (n:=K)).le
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α:=ℝ) K])
  calc _ ≤ (2:ℝ)^((K:ℝ)*s) * (2:ℝ)^((k:ℝ)*s*(n:ℕ)) := mul_le_mul_of_nonneg_right hK (by positivity)
       _ = _ := by rw [←Real.rpow_add (by norm_num)]; push_cast; congr 1; ring

theorem poly_stage (K C b n : ℕ) (hb : 1 ≤ b) (hn : ((n+1:ℕ):ℝ) ≤ mainSpaceBound C b) :
    polyBound K n ≤ mainSpaceBound (K+K*C) b := by
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ (n:ℝ)+1 by positivity) (by exact_mod_cast hn) K) (Nat.cast_nonneg (α:=ℝ) K)).trans (absorb_prod K C K b hb)
theorem lin_stage (K C b n : ℕ) (hb : 1 ≤ b) (hn : (n:ℝ) ≤ mainSpaceBound C b) :
    ((K*n:ℕ):ℝ) ≤ mainSpaceBound (K+1*C) b := by
  rw [Nat.cast_mul]; exact (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α:=ℝ) K)).trans (by simpa only [pow_one] using absorb_prod K C 1 b hb)
end DetDLP.m89_enum_final

open DetDLP DetDLP.M89S1 DetDLP.m89_affine_enum DetDLP.m89_enum_words DetDLP.m89_enum_spec DetDLP.m89_enum_pad DetDLP.m89_enum_final
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution : CountOracle → ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
    ∀ (p : ℕ) [Fact p.Prime],
      let b := bitLen p; let m := blockCount b
      ∀ L : Option (ℕ × FpSeed p m), m89_fp_plan_ok L → ∃ F : Fin m → List (ZMod p)ˣ,
        (∀ i, (F i).Nodup ∧ (F i).toFinset = m89_fp_plan_block L i) ∧
        RunsWithin M o (Encoding.encodeList id [countWord p,m89_fp_plan_word L]) (encodeFpFactorBlocks F) (mainSpaceBound K b) (mainSpaceBound K b) := by
  intro _
  obtain ⟨C,hC⟩ := m89_enum_growth.base
  obtain ⟨A,a,i,pre⟩ := PolyTBridge.polyT_listBool_runsWithin tally tally_poly
  obtain ⟨B,d,j,pad⟩ := m89_enum_pad.machine
  obtain ⟨D,e,k,finish⟩ := PolyTBridge.polyT_listBool_runsWithin output output_poly
  obtain ⟨P,o,I,pipe⟩ := m89_s1_word_pipe A a B d (i+i*C) (j+1*C) false
  obtain ⟨N,r,K,pipe2⟩ := m89_s1_word_pipe P o D e I (k+k*C) false
  refine ⟨N,r,K,?_⟩; intro p inst b m L hok
  let w := arg p L; let l := (tval w).bits.length
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (Fact.out : Nat.Prime p).two_le
  have hbase : ((w.length+l+2^l+33 : ℕ):ℝ) ≤ mainSpaceBound C b := hC p L hok
  have H (n : ℕ) (hn : n ≤ w.length+l+2^l+33) : (n:ℝ) ≤ mainSpaceBound C b := (by exact_mod_cast hn : (n:ℝ) ≤ ((w.length+l+2^l+33 : ℕ):ℝ)).trans hbase
  have hs0 : w.length+1 ≤ w.length+l+2^l+33 := Nat.add_le_add (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _)) (by decide : 1 ≤ 33)
  have h1 := poly_stage i C b w.length hb (H _ hs0)
  have h2 := lin_stage j C b (2^l+l+w.length+1) hb (H _ (by omega))
  have h3 := poly_stage k C b (fmt (2^l) w).length hb (H _ (by simp only [fmt,List.length_append,List.length_replicate,List.length_cons]; omega))
  have hpre := PolyTBridge.runsWithin_mono_local (pre w) h1 h1
  have hpad := PolyTBridge.runsWithin_mono_local (pad l w) h2 h2
  have hfin := PolyTBridge.runsWithin_mono_local (finish (fmt (2^l) w)) h3 h3
  have run := pipe2 b hb _ _ _ (pipe b hb _ _ _ hpre hpad) hfin
  obtain ⟨F,hF,hs⟩ := good_output L hok
  exact ⟨F,hF,hs ▸ run⟩
