-- Prove2me | solution 1 for DetDLP.m89_s1_fp_plan_prepare
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T04:59:41.371333+00:00
-- url     : https://prove2.me/submissions/46f0290a-8935-4096-964b-a9a18f66f778

import Definitions.Def_DetDLP_S8B_Parameters
import Definitions.Def_DetDLP_S8B_MomentCompare
import Definitions.Def_DetDLP_M89_S1_Queries
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_foldl_add
import Definitions.Def_DetDLP_S8B_Descent
import Definitions.Def_DetDLP_M89_S1_Plans
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Theorems.Thm_DetDLP_stage1_complexity_dominance
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace DetDLP.S8B.Ctl
open M89S1 Groundwork Groundwork.PolyT
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


def enc (l : List Word) := Encoding.encodeList id l
def pair (w v : Word) := Encoding.frame w ++ v

theorem frame_eq (w v : Word) : pair w v = w.flatMap (fun b => [true,b]) ++ [false] ++ v := by simp [pair,frame_flat]

@[local fun_prop] theorem pair_poly {α} [Enc α] {w v : α → Word} (hw : PolyT w) (hv : PolyT v) : PolyT (fun x => pair (w x) (v x)) := by simp only [frame_eq]; fun_prop

@[local fun_prop] theorem count_poly {α} [Enc α] {f : α → ℕ} (hf : PolyT f) : PolyT (fun x => countWord (f x)) := by unfold countWord; fun_prop

def seedLen (p : ℕ) := blocks (p-1).size * 2 * (p-1).size
def parameterList (p : ℕ) := ((p.bits ++ [false,false]).take (blocks (p-1).size)).map (fun _ => ())

attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
@[local fun_prop] theorem params_poly {α} [Enc α] {p : α → ℕ} (hp : PolyT p) : PolyT (fun x => parameterList (p x)) := by
  unfold parameterList; apply Groundwork.PolyT.map (by fun_prop); apply Groundwork.PolyT.take (blocks_poly (by fun_prop)) (by fun_prop)

theorem unary_length {α} [Enc α] {l : α → List Unit} (hl : PolyT l) : Unary (fun x => (l x).length) := by
  apply hl.congr; intro x; exact List.eq_replicate_of_mem (fun a _ => Subsingleton.elim ..)

def stageT (p : ℕ) := threshold p (p-1) (parameterList p).length (p-1)
@[local fun_prop] theorem stageT_poly {α} [Enc α] {p : α → ℕ} (hp : PolyT p) : PolyT (fun x => stageT (p x)) := by
  apply threshold_poly hp (by fun_prop) (by fun_prop) (unary_length (params_poly hp)) (by fun_prop)

def select (p : ℕ) (vs : List Word) :=
  let m := (parameterList p).length; let t := stageT p
  let v := fun i => bval (vs.getD i [])
  momentRight (p^m) (((p-1)*t)^m) (p-1) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)

@[local fun_prop] theorem select_poly {α} [Enc α] {p : α → ℕ} {vs : α → List Word} (hp : PolyT p) (hv : PolyT vs) : PolyT (fun x => select (p x) (vs x)) := by
  unfold select; dsimp only; apply momentRight_poly
  · exact pow_unary hp (unary_length (params_poly hp))
  · exact pow_unary (by fun_prop) (unary_length (params_poly hp))
  all_goals fun_prop

/-- Store the raw input and prefix before the at most seven previously received answers. -/
def ask (raw : Word) (p : ℕ) (w : Word) (vs : List Word) : Word :=
  let i := vs.length
  false :: pair (enc (raw :: w :: vs)) (queryWord 1 (countWord p) [countWord (i%4),countWord (stageT p), w++[decide (4 ≤ i)]])

def finish (raw plan : Word) := true :: enc [raw,plan]

def primeOf (tag : Bool) (raw : Word) := bval (if tag then (fields raw).getD 0 [] else raw)

def step (tag : Bool) (a : Word) :=
  let outer := fields (true :: (a ++ [false]))
  let st := outer.getD 0 []
  if outer.length ≤ 1 then
    let p := primeOf tag st
    if 64 ≤ p-1 ∧ 4096*blocks (p-1).size ≤ p-1 then ask st p [] [] else finish st [false]
  else
    let state := fields st
    let raw := state.getD 0 []; let w := state.getD 1 []; let p := primeOf tag raw
    let vs := state.drop 2 ++ [outer.getD 1 []]
    if vs.length < 8 then ask raw p w vs else
      let newW := w ++ [select p vs]
      if seedLen p ≤ newW.length then finish raw (true :: enc [countWord (stageT p),newW])
      else ask raw p newW []

attribute [local fun_prop] blocks_poly P2M_Groundwork_PolyT_size__c8c8eb1b342f
@[local fun_prop] theorem fields_comp {α} [Enc α] {w : α → Word} (hw : PolyT w) : PolyT (fun x => fields (w x)) := Groundwork.PolyT.comp fields_poly hw
@[local fun_prop] theorem ask_poly {α} [Enc α] {raw w : α → Word} {p : α → ℕ} {vs : α → List Word} (hr : PolyT raw) (hp : PolyT p) (hw : PolyT w) (hv : PolyT vs) : PolyT (fun x => ask (raw x) (p x) (w x) (vs x)) := by unfold ask enc queryWord; dsimp only; fun_prop
@[local fun_prop] theorem finish_poly {α} [Enc α] {r w : α → Word} (hr : PolyT r) (hw : PolyT w) : PolyT (fun x => finish (r x) (w x)) := by unfold finish enc; fun_prop
@[local fun_prop] theorem primeOf_poly {α} [Enc α] {w : α → Word} (t : Bool) (hw : PolyT w) : PolyT (fun x => primeOf t (w x)) := by cases t <;> simp [primeOf] <;> fun_prop

def init (raw : Word) (p : ℕ) := if 64 ≤ p-1 ∧ 4096*blocks (p-1).size ≤ p-1 then ask raw p [] [] else finish raw [false]
def advance (raw : Word) (p : ℕ) (newW : Word) := if seedLen p ≤ newW.length then finish raw (true :: enc [countWord (stageT p),newW]) else ask raw p newW []
def driver (raw : Word) (p : ℕ) (w : Word) (vs : List Word) := if vs.length < 8 then ask raw p w vs else advance raw p (w ++ [select p vs])
def resume (t : Bool) (state : List Word) (ans : Word) := let raw := state.getD 0 []; driver raw (primeOf t raw) (state.getD 1 []) (state.drop 2 ++ [ans])
def outerStep (t : Bool) (outer : List Word) := let st := outer.getD 0 []; if outer.length ≤ 1 then init st (primeOf t st) else resume t (fields st) (outer.getD 1 [])
@[local fun_prop] theorem init_poly {α} [Enc α] {r : α → Word} {p : α → ℕ} (hr : PolyT r) (hp : PolyT p) : PolyT (fun x => init (r x) (p x)) := by
  have hn : PolyT (fun x => p x - 1) := Groundwork.PolyT.sub hp (const 1)
  have hm : PolyT (fun x => blocks (p x - 1).size) := blocks_poly (P2M_Groundwork_PolyT_size__c8c8eb1b342f hn)
  have hc0 := Groundwork.PolyT.decide_le (const (α:=α) 64) hn
  have hc1 := Groundwork.PolyT.decide_le (Groundwork.PolyT.mul (const 4096) hm) hn
  have hA := ask_poly hr hp (const ([]:Word)) (const ([]:List Word))
  have hF := finish_poly hr (const [false])
  unfold init; simp only [ite_and]; exact P2M_Groundwork_PolyT_ite__226169acf219 hc0 (P2M_Groundwork_PolyT_ite__226169acf219 hc1 hA hF) hF
@[local fun_prop] theorem advance_poly {α} [Enc α] {r w : α → Word} {p : α → ℕ} (hr : PolyT r) (hp : PolyT p) (hw : PolyT w) : PolyT (fun x => advance (r x) (p x) (w x)) := by unfold advance enc seedLen; fun_prop
@[local fun_prop] theorem driver_poly {α} [Enc α] {r w : α → Word} {p : α → ℕ} {vs : α → List Word} (hr : PolyT r) (hp : PolyT p) (hw : PolyT w) (hv : PolyT vs) : PolyT (fun x => driver (r x) (p x) (w x) (vs x)) := by unfold driver; fun_prop
@[local fun_prop] theorem resume_poly {α} [Enc α] (t : Bool) {s : α → List Word} {a : α → Word} (hs : PolyT s) (ha : PolyT a) : PolyT (fun x => resume t (s x) (a x)) := by unfold resume; dsimp only; fun_prop
@[local fun_prop] theorem outerStep_poly {α} [Enc α] (t : Bool) {s : α → List Word} (hs : PolyT s) : PolyT (fun x => outerStep t (s x)) := by unfold outerStep; dsimp only; fun_prop
theorem step_poly (t : Bool) : PolyT (step t) := by change PolyT (fun w : Word => outerStep t (fields (true::(w++[false])))); fun_prop
end DetDLP.S8B.Ctl

set_option autoImplicit false
namespace DetDLP.S8B
open M89S1
theorem threshold_le {p m : ℕ} (hm : 2 ≤ m) (h64 : 64 ≤ p-1) (h4096 : 4096*m ≤ p-1) :
    hashThreshold p (p-1) m (p-1) ≤ p := by
  let n := p-1
  have hn : (64:ℝ) ≤ (n:ℝ) := by exact_mod_cast h64
  have hp : 0 < (n:ℝ) := by linarith
  have he : (1:ℝ)/(m:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm)
  have h16 : (16*(n:ℝ))^((1:ℝ)/(m:ℝ)) ≤ (n:ℝ) := by
    calc
      _ ≤ (16*(n:ℝ))^((1:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ ≤ ((n:ℝ)^2)^((1:ℝ)/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [mul_nonneg (by linarith : 0 ≤ (n:ℝ)-16) hp.le]) (by norm_num)
      _ = _ := by rw [← Real.rpow_natCast_mul hp.le]; norm_num
  have hq : qStar m n ≤ n := max_le h4096 (Nat.ceil_le.mpr h16)
  change Nat.ceil ((p:ℝ)*(qStar m n:ℝ)/(n:ℝ)) ≤ p
  apply Nat.ceil_le.mpr
  exact (div_le_iff₀ hp).mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by positivity))


noncomputable abbrev fpM (p : ℕ) := blockCount (bitLen p)
noncomputable abbrev fpT (p : ℕ) := hashThreshold p (p-1) (fpM p) (p-1)
noncomputable def fpMom (p : ℕ) [Fact p.Prime] : Fin 4 → W → ℕ :=
  let D := fun s : FpSeed p (fpM p) => fpFactorBlock (p:=p) (fpT p) s
  moment fpBits (fun s => productSize (D s)) (fun s => collisionEnergyMul (D s))
noncomputable def fpNext (p : ℕ) [Fact p.Prime] :=
  fromMoments (p^fpM p) (((p-1)*fpT p)^fpM p) (p-1) (fpMom p)

theorem fp_law (p : ℕ) [hp : Fact p.Prime] (h64 : 64 ≤ p-1) (h4096 : 4096*fpM p ≤ p-1) :
    ∃ s : FpSeed p (fpM p), m89_fp_plan_ok (some (fpT p,s)) ∧
      List.ofFn (fpBits s) = path (fpNext p) (fpM p*2*bitLen p) := by
  have pp := hp.out.pos
  have hn : 0 < p-1 := by omega
  have hm : 2 ≤ fpM p := le_max_left ..
  have hq : 0 < qStar (fpM p) (p-1) := lt_of_lt_of_le (by omega : 0 < 4096*fpM p) (le_max_left ..)
  have ht : 0 < fpT p := by unfold fpT hashThreshold; apply Nat.ceil_pos.mpr; positivity
  let _ : Nonempty (FpSeed p (fpM p)) := ⟨fun _ => (⟨0,hn⟩,⟨0,pp⟩)⟩
  have hμ : (qBlk p (p-1) (fpT p))^(fpM p) = (↑(((p-1)*fpT p)^fpM p) : ℝ)/↑(p^fpM p) := by simp [qBlk,div_pow,mul_pow]
  obtain ⟨s,hs,hw⟩ := path_winner (@fpBits p (fpM p)) (fpCost p (fpM p)) (fpNext p) (by
    intro w _
    let D := fun s : FpSeed p (fpM p) => fpFactorBlock (p := p) (fpT p) s
    have HH := fromMoments_spec (@fpBits p (fpM p)) w (fun s => productSize (D s)) (fun s => collisionEnergyMul (D s))
      (p-1) (p^fpM p) (((p-1)*fpT p)^fpM p) (by positivity) (by positivity)
    simpa only [fpNext,fpMom,fpCost,collisionPotentialMul,ZMod.card_units,←hμ,fpT,D,fpM] using HH)
  exact ⟨s,⟨h64,h4096,rfl,hs⟩,hw⟩
end DetDLP.S8B

set_option autoImplicit false
namespace DetDLP.S8B.Ctl
open M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem block_le (b : ℕ) : blockCount b ≤ b+2 := by
  apply max_le (by omega) (Nat.ceil_le.mpr ?_)
  have u : Nat.clog 2 (b+2) ≤ b+2 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (Nat.lt_pow_self (by decide)).le
  have v : 1 ≤ Nat.clog 2 (b+2) := Nat.clog_pos (by decide) (by omega)
  exact (Real.rpow_le_self_of_one_le (by exact_mod_cast v) (by norm_num)).trans (by exact_mod_cast u)


private theorem size_eq (p : ℕ) : (p-1).size = bitLen p := by
  apply le_antisymm
  · apply Nat.size_le.mpr
    have := Nat.le_pow_clog (by decide : 1<2) p
    have : 0 < 2^bitLen p := by positivity
    unfold bitLen at *; omega
  · apply (Nat.clog_le_iff_le_pow (by decide)).2
    have := Nat.lt_size_self (p-1); omega
@[simp] theorem paramLen (p : ℕ) : (parameterList p).length = fpM p := by
  have hh : fpM p ≤ p.bits.length + 2 := (block_le _).trans (Nat.add_le_add_right (by rw [←size_eq,Nat.size_eq_bits_len]; exact Nat.size_le_size (Nat.sub_le ..)) 2)
  simp [parameterList,blocks_eq,size_eq,fpM,List.length_take, min_eq_left hh]
@[simp] theorem stage_eq (p : ℕ) : stageT p = fpT p := by simp [stageT,threshold_eq,show 0 < fpM p from lt_of_lt_of_le (by decide : 0<2) (le_max_left ..)]
@[simp] theorem seedLen_eq (p : ℕ) : seedLen p = fpM p * 2 * bitLen p := by simp [seedLen,blocks_eq,size_eq,fpM]
@[simp] theorem bval_count (n : ℕ) : bval (countWord n) = n := by cases n with | zero => rfl | succ n => simp [countWord,bval_bits]
@[simp] theorem fields_nat (l : List ℕ) : fields (encodeNatListBin l) = l.map countWord := by
  have h : encodeNatListBin l = enc (l.map countWord) := by induction l with | nil => rfl | cons a l ih => change true :: (_ ++ encodeNatListBin l) = true :: (_ ++ enc (l.map countWord)); rw [ih]; rfl
  rw [h]; exact fields_encode _
@[simp] theorem base0 (p : ℕ) : primeOf false (countWord p) = p := by simp [primeOf]
@[simp] theorem base1 (p x : ℕ) : primeOf true (encodeNatListBin [p,x]) = p := by simp [primeOf]

theorem parseInit (st : Word) : fields (true :: (pair st [] ++ [false])) = [st] := by
  simpa [pair,Encoding.encodeList] using fields_encode [st]

theorem parseAns (st : Word) (n : ℕ) : fields (true :: (pair st (encodeNatListBin [n]) ++ [false])) = [st,countWord n] := by
  let x := enc [st,countWord n]
  have eq : true :: (pair st (encodeNatListBin [n]) ++ [false]) = x ++ [false] := by simp [x,enc,pair,encodeNatListBin,Encoding.encodeList,List.append_assoc]
  have aux (l : List Word) (a : List Word) : (enc l).foldl scan (false,false,[],a) = (true,true,[],l.reverse++a) := by
    induction l generalizing a with
    | nil => rfl
    | cons w l ih =>
      change (Encoding.frame w ++ enc l).foldl scan (false,true,[],a) = _
      have fr (s acc : Word) (v : List Word) : (Encoding.frame s).foldl scan (false,true,acc,v) = (false,false,[],(acc.reverse++s)::v) := by
        induction s generalizing acc with | nil => simp [Encoding.frame,scan] | cons b s ih => change (Encoding.frame s).foldl scan (false,true,b::acc,v) = _; simpa using ih (b::acc)
      rw [List.foldl_append,fr]; simpa using ih (w::a)
  rw [eq]; simp [x,fields,List.foldl_append,aux,scan]

theorem step_init (t : Bool) (raw : Word) : step t (pair raw []) = init raw (primeOf t raw) := by
  change outerStep t _ = _; rw [parseInit]; rfl

theorem step_ans (t : Bool) (raw w : Word) (vs : List Word) (n : ℕ) :
    step t (pair (enc (raw::w::vs)) (encodeNatListBin [n])) = driver raw (primeOf t raw) w (vs++[countWord n]) := by
  change outerStep t _ = _; rw [parseAns]; simp [outerStep,resume,enc,fields_encode]
end DetDLP.S8B.Ctl

set_option autoImplicit false
namespace DetDLP.S8B.Ctl
open M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem moment_bound (p : ℕ) [h : Fact p.Prime] (j : Fin 4) (w : W) :
    fpMom p j w ≤ p^(4*fpM p+1) := by
  classical
  let m := fpM p
  let D := fun s : FpSeed p m => fpFactorBlock (p:=p) (fpT p) s
  have hp := h.out.pos
  have card : Fintype.card (ZMod p)ˣ ≤ p := (ZMod.card_units p).le.trans (Nat.sub_le ..)
  have size (s : FpSeed p m) : productSize (D s) ≤ p^m := by
    simpa [productSize] using Finset.prod_le_prod' (s:=Finset.univ) (g:=fun _ : Fin m => p) (fun i _ => ((D s i).card_le_univ.trans card))
  have rep (s : FpSeed p m) (g : (ZMod p)ˣ) : repCountMul (D s) g ≤ p^m := by
    unfold repCountMul
    apply (Finset.card_le_univ _).trans; simpa using Nat.pow_le_pow_left card m
  have big (s : FpSeed p m) : collisionEnergyMul (D s) ≤ p^(2*m+1) := by
    unfold collisionEnergyMul
    calc
      _ ≤ ∑ _ : (ZMod p)ˣ, (p^m)^2 := Finset.sum_le_sum (fun g _ => Nat.pow_le_pow_left (rep s g) _)
      _ = Fintype.card (ZMod p)ˣ * (p^m)^2 := by simp
      _ ≤ p*(p^m)^2 := Nat.mul_le_mul_right _ card
      _ = p^(2*m+1) := by rw [pow_succ p (2*m), Nat.mul_comm 2 m,pow_mul]; ring
  have seeds : Fintype.card (FpSeed p m) ≤ p^(2*m) := by
    simp [FpSeed,pow_mul,pow_two]; exact Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (Nat.sub_le p 1)) _
  change (∑ s ∈ slice fpBits w, (if j=0 then 1 else if j=1 then productSize (D s) else if j=2 then (productSize (D s))^2 else collisionEnergyMul (D s))) ≤ _
  calc
    _ ≤ ∑ _ ∈ slice (@fpBits p m) w, p^(2*m+1) := by
      apply Finset.sum_le_sum; intro s _; split_ifs
      · exact Nat.one_le_pow _ _ hp
      · exact (size s).trans (Nat.pow_le_pow_right hp (by omega))
      · apply (Nat.pow_le_pow_left (size s) 2).trans
        rw [←pow_mul]; exact Nat.pow_le_pow_right hp (by omega)
      · exact big s
    _ ≤ p^(2*m)*p^(2*m+1) := by simp only [Finset.sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ ((Finset.card_le_univ _).trans seeds)
    _ = _ := by rw [←pow_add]; congr 1; dsimp [m]; omega

theorem cw_size (n : ℕ) : (countWord n).length ≤ n.size+1 := by by_cases h:n=0 <;> simp [countWord,h,Nat.size_eq_bits_len]

def cap (b : ℕ) := 1000*(b+3)^2

theorem field_bound (p : ℕ) [hp : Fact p.Prime] (j : Fin 4) (w : W) :
    (countWord (fpMom p j w)).length ≤ (bitLen p+1)*(4*fpM p+2)+1 := by
  let e := 4*fpM p+1
  have ht := (moment_bound p j w).trans (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1<2) p) e)
  rw [←pow_mul] at ht
  have hs : (fpMom p j w).size ≤ bitLen p * e + 1 := Nat.size_le.mpr (ht.trans_lt (by change 2^(bitLen p*e) < 2^(bitLen p*e+1); exact Nat.pow_lt_pow_right (by decide) (by omega)))
  dsimp [e] at hs
  exact (cw_size _).trans (by nlinarith)
def unitCap (b : ℕ) := 20*(b+3)^2

theorem cw_le_prime (n p : ℕ) (h : n ≤ p) : (countWord n).length ≤ bitLen p+2 := by
  have hp := Nat.le_pow_clog (by decide : 1<2) p
  have h2 : 2^(bitLen p) < 2^(bitLen p+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  exact (cw_size n).trans (by have := Nat.size_le.mpr ((h.trans hp).trans_lt h2); omega)

theorem enc_len (l : List Word) (u : ℕ) (h : ∀ w ∈ l, w.length ≤ u) : (enc l).length ≤ l.length*(2*u+2)+1 := by
  have ff (w : W) : (Encoding.frame w).length = 2*w.length+1 := by induction w with | nil => rfl | cons b w ih => change (Encoding.frame w).length+1+1 = _; simp; omega
  induction l with
  | nil => simp [enc,Encoding.encodeList]
  | cons a l ih =>
    change (true :: (Encoding.frame a ++ enc l)).length ≤ _
    have hh := ih (fun w hw => h w (by simp [hw])); have ha := h a (by simp)
    simp only [List.length_cons,List.length_append,ff]; nlinarith

theorem pair_len (w v : W) : (pair w v).length = 2*w.length+1+v.length := by
  have ff (s : W) : (Encoding.frame s).length = 2*s.length+1 := by induction s with | nil => rfl | cons b s ih => change (Encoding.frame s).length+1+1 = _; simp; omega
  simp [pair,ff]

theorem atomic_bounds (p : ℕ) [Fact p.Prime] :
    let b := bitLen p; let z := unitCap b
    fpM p * 2 * b + 1 ≤ z ∧ b+8 ≤ z ∧
    (∀ i w, (countWord (fpMom p i w)).length ≤ z) ∧
    (∀ x < p, (encodeNatListBin [p,x]).length ≤ z) := by
  intro b z
  have hm := block_le b; change fpM p ≤ b+2 at hm
  have hprod := Nat.mul_le_mul_right b hm
  have hprod' := Nat.mul_le_mul_right (b+1) hm
  constructor
  · dsimp [z,unitCap]; nlinarith
  constructor
  · dsimp [z,unitCap]; nlinarith
  constructor
  · intro i w; apply (field_bound p i w).trans; change (b+1)*(4*fpM p+2)+1 ≤ _; dsimp [z,unitCap]; nlinarith
  · intro x hx; change (enc [countWord p,countWord x]).length ≤ _
    apply (enc_len _ (b+2) (by simp; exact ⟨cw_le_prime p p le_rfl,cw_le_prime x p hx.le⟩)).trans; simp; dsimp [z,unitCap]; nlinarith
end DetDLP.S8B.Ctl

set_option autoImplicit false
namespace DetDLP.S8B.Ctl
open M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def tr (t : Bool) (O : PrimitiveMachine) (o : Fin O.tapeCount) (τ σ : ℝ) : ℕ → Word → Word → Word → ℕ → Prop :=
  Nat.rec (motive := fun _ => Word → Word → Word → ℕ → Prop) (fun _ _ _ _ => False)
    (fun _ prev st ans out z => (step t (pair st ans) = true :: out ∧ (pair st ans).length ≤ z ∧ out.length ≤ z) ∨
    ∃ st' q ans', step t (pair st ans) = false :: pair st' q ∧ (pair st ans).length ≤ z ∧ (pair st' q).length ≤ z ∧ ans'.length ≤ z ∧ RunsWithin O o q ans' τ σ ∧ prev st' ans' out z)

noncomputable def value (p : ℕ) [Fact p.Prime] (w : W) (i : ℕ) := fpMom p ⟨i%4,Nat.mod_lt _ (by decide)⟩ (w++[decide (4 ≤ i)])
noncomputable def table (p : ℕ) [Fact p.Prime] (w : W) : ℕ → List W
  | 0 => []
  | i+1 => table p w i ++ [countWord (value p w i)]
@[simp] theorem table_length (p : ℕ) [Fact p.Prime] (w : W) (i : ℕ) : (table p w i).length=i := by induction i with | zero => rfl | succ i ih => simp [table,ih]

theorem select_table (p : ℕ) [Fact p.Prime] (w : W) : select p (table p w 8) = fpNext p w := by
  simp [select,table,value,fpNext,fromMoments,paramLen,stage_eq,List.getD_cons_succ,List.getD_cons_zero]

def packet (p : ℕ) (w : W) (i : ℕ) := queryWord 1 (countWord p) [countWord (i%4),countWord (stageT p),w++[decide (4 ≤ i)]]

theorem ask_table (raw : W) (p : ℕ) [Fact p.Prime] (w : W) (i : ℕ) : ask raw p w (table p w i) = false :: pair (enc (raw::w::table p w i)) (packet p w i) := by simp [ask,packet]

theorem packet_run {O : PrimitiveMachine} {o : Fin O.tapeCount} {K : ℕ}
    (hO : ∀ w b n, Query w b n → RunsWithin O o w (encodeNatListBin [n]) (mainSpaceBound K b) (polyBound K b))
    (p : ℕ) [Fact p.Prime] (w : W) (i : ℕ) (hw : w.length < seedLen p) (ht : fpT p ≤ p) :
    RunsWithin O o (packet p w i) (encodeNatListBin [value p w i]) (mainSpaceBound K (bitLen p)) (polyBound K (bitLen p)) := by
  apply hO
  unfold packet value; rw [stage_eq]; apply Query.fpMoment p (⟨i%4,Nat.mod_lt _ (by decide)⟩ : Fin 4) _ ht
  rw [seedLen_eq] at hw; simp; omega

/-- All lengths needed for one call, using the same polynomial cap for both machines. -/
theorem packet_bounds (raw w : W) (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : i < 8) (hr : raw.length ≤ unitCap (bitLen p)) (hw : w.length < seedLen p) (ht : fpT p ≤ p) :
    let st := enc (raw::w::table p w i); let q := packet p w i; let a := encodeNatListBin [value p w i]; let z := cap (bitLen p)
    (pair st q).length ≤ z ∧ a.length ≤ z ∧ (pair st a).length ≤ z := by
  intro st q a z
  let u := unitCap (bitLen p)
  obtain ⟨hL,hb,hv,_⟩ := atomic_bounds p
  have hw' : w.length+1 ≤ u := by rw [seedLen_eq] at hw; dsimp [u]; omega
  have htable (k : ℕ) : ∀ x ∈ table p w k, x.length ≤ u := by
    induction k with
    | zero => simp [table]
    | succ k ih => intro x hx; simp only [table,List.mem_append,List.mem_singleton] at hx; rcases hx with h|rfl; exact ih _ h; exact hv _ _
  have hs := enc_len (raw::w::table p w i) u (by simp only [List.mem_cons,forall_eq_or_imp]; exact ⟨hr,hw'.trans' (by omega),htable _⟩)
  change st.length ≤ _ at hs; simp only [List.length_cons,table_length] at hs
  have hs' : st.length ≤ 9*(2*u+2)+1 := hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)
  have hq : q.length ≤ 5*(2*u+2)+1 := by
    apply enc_len [countWord 1,countWord p,countWord (i%4),countWord (stageT p),w++[decide (4 ≤ i)]] u
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,List.length_append,List.length_singleton]; refine ⟨?_,?_,?_,?_,by rintro _ rfl; simpa using hw'⟩
    · change 1 ≤ _; dsimp [u]; omega
    · exact (cw_le_prime _ _ le_rfl).trans (by dsimp [u]; omega)
    · have h' : i%4 ≤ 3 := by omega
      have := cw_le_prime _ 3 h'; change (countWord (i%4)).length ≤ 4 at this; dsimp [u]; omega
    · rw [stage_eq]; exact (cw_le_prime _ _ ht).trans (by dsimp [u]; omega)
  have ha : a.length ≤ 1*(2*u+2)+1 := enc_len [countWord (value p w i)] u (by simpa [value,u] using hv ⟨i%4,Nat.mod_lt _ (by decide)⟩ (w++[decide (4 ≤ i)]))
  have fit : 49*u+80 ≤ z := by dsimp [u,z,unitCap,cap]; nlinarith
  simp only [pair_len]; omega
end DetDLP.S8B.Ctl

set_option autoImplicit false
namespace DetDLP.S8B.Ctl
open M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable def chosen (p : ℕ) [Fact p.Prime] (k : ℕ) := path (fpNext p) k
noncomputable def largeOutput (p : ℕ) [Fact p.Prime] (raw : W) := enc [raw,true :: enc [countWord (fpT p),chosen p (seedLen p)]]

theorem large_run {O : PrimitiveMachine} {o : Fin O.tapeCount} {K : ℕ}
    (hO : ∀ w b n, Query w b n → RunsWithin O o w (encodeNatListBin [n]) (mainSpaceBound K b) (polyBound K b))
    (p : ℕ) [hp : Fact p.Prime] (t : Bool) (raw : W) (hr : raw.length ≤ unitCap (bitLen p)) (hpraw : primeOf t raw = p)
    (h64 : 64 ≤ p-1) (h4096 : 4096*fpM p ≤ p-1) :
    tr t O o (mainSpaceBound K (bitLen p)) (polyBound K (bitLen p)) (8*seedLen p+1) raw [] (largeOutput p raw) (cap (bitLen p)) := by
  let b := bitLen p; let N := seedLen p; let z := cap b; let u := unitCap b
  let R := tr t O o (mainSpaceBound K b) (polyBound K b)
  let out := largeOutput p raw
  have ht := threshold_le (show 2 ≤ fpM p from le_max_left ..) h64 h4096
  change fpT p ≤ p at ht
  have hpos : 0 < N := by
    have h := Nat.clog_pos (by decide : 1<2) hp.out.one_lt
    have hm : 2 ≤ fpM p := le_max_left ..
    dsimp [N]; rw [seedLen_eq]; change 0 < fpM p * 2 * Nat.clog 2 p; positivity
  have hw (k) : (chosen p k).length = k := path_len ..
  have fit : 49*u+80 ≤ z := by change 49*(20*(b+3)^2)+80 ≤ 1000*(b+3)^2; have H := Nat.pow_le_pow_left (show 3 ≤ b+3 by omega) 2; omega
  obtain ⟨hN,hb,_,_⟩ := atomic_bounds p
  have hout : out.length ≤ z := by
    have hT : (countWord (fpT p)).length ≤ u := (cw_le_prime _ _ ht).trans (by dsimp [u,b]; omega)
    have hW : (chosen p N).length ≤ u := by rw [hw]; dsimp [u,N,b]; rw [seedLen_eq]; omega
    have hw2 := enc_len [countWord (fpT p),chosen p N] u (by simp; exact ⟨hT,hW⟩)
    have hh := enc_len [raw,true :: enc [countWord (fpT p),chosen p N]] (4*u+6) (by simp; exact ⟨by change raw.length ≤ _; dsimp [u,b]; omega,by simp at hw2; omega⟩)
    change (enc [raw,true :: enc [countWord (fpT p),chosen p N]]).length ≤ _; simp at hh; omega
  have recRun (r k i : ℕ) (kN : k<N) (hi : i<8) (eq : r + 8*k + i + 1 = 8*N) :
      let w := chosen p k
      R (r+1) (enc (raw::w::table p w i)) (encodeNatListBin [value p w i]) out z := by
    induction r generalizing k i with
    | zero =>
      have hki : k+1=N := by omega
      have hi7 : i=7 := by omega
      subst i; let w := chosen p k
      have hh := packet_bounds raw w p 7 (by decide) hr (by rw [show w.length = k from hw k]; exact kN) ht
      apply Or.inl; refine ⟨?_,hh.2.2,hout⟩
      rw [step_ans,hpraw]; change driver raw p w (table p w 8) = _
      simp only [driver,table_length,show ¬ 8<8 by decide,if_false,select_table]
      change advance raw p (chosen p (k+1)) = _
      simp [advance,hw, hki,N,←hki,finish,out,largeOutput,stage_eq]
    | succ r ih =>
      let w := chosen p k
      have wl : w.length < seedLen p := (hw k).trans_lt kN
      have before := (packet_bounds raw w p i hi hr wl ht).2.2
      by_cases more : i+1<8
      · have bounds := packet_bounds raw w p (i+1) more hr wl ht
        apply Or.inr
        refine ⟨_,_,_,?_,before,bounds.1,bounds.2.1,packet_run hO p w (i+1) wl ht,ih k (i+1) kN more (by omega)⟩
        rw [step_ans,hpraw]; change driver raw p w (table p w (i+1)) = _
        simp [driver,table_length,more,ask_table]
      · have hi7 : i=7 := by omega
        subst i; have hk : k+1<N := by omega
        let w' := chosen p (k+1)
        have wl' : w'.length < seedLen p := (hw _).trans_lt hk
        have bounds := packet_bounds raw w' p 0 (by decide) hr wl' ht
        apply Or.inr
        refine ⟨_,_,_,?_,before,bounds.1,bounds.2.1,packet_run hO p w' 0 wl' ht,ih (k+1) 0 hk (by decide) (by omega)⟩
        rw [step_ans,hpraw]; change driver raw p w (table p w 8) = _
        simp only [driver,table_length,show ¬ 8<8 by decide,if_false,select_table]
        change advance raw p w' = _
        rw [advance,if_neg (Nat.not_le.mpr wl')]; exact ask_table raw p w' 0
  have bounds := packet_bounds raw [] p 0 (by decide) hr hpos ht
  have h0 := recRun (8*N-1) 0 0 hpos (by decide) (by omega)
  rw [show 8*N-1+1 = 8*N by omega] at h0
  apply Or.inr; refine ⟨_,_,_,?_,?_,bounds.1,bounds.2.1,packet_run hO p [] 0 hpos ht,h0⟩
  · rw [step_init,hpraw]; unfold init
    have hh : blocks (p-1).size = fpM p := by
      rw [blocks_eq]; congr 1; apply le_antisymm
      · apply Nat.size_le.mpr; have := Nat.le_pow_clog (by decide : 1 < 2) p; change p-1 < 2^(Nat.clog 2 p); omega
      · apply (Nat.clog_le_iff_le_pow (by decide)).2; have := Nat.lt_size_self (p-1); omega
    rw [hh,if_pos ⟨h64,h4096⟩]; exact ask_table raw p [] 0
  · rw [pair_len]; simp; dsimp [z,u,b] at fit; omega
end DetDLP.S8B.Ctl

set_option autoImplicit false
set_option maxRecDepth 8192
namespace DetDLP.S8B.Ctl
open M89S1 Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem pb_pow {f : ℕ → ℕ} (h : PB f) (k : ℕ) : PB (fun b => (f b)^k) := by
  induction k with | zero => simpa using PB.const 1 | succ k ih => simpa [pow_succ] using ih.mul h

def pn (K b : ℕ) := K*(b+1)^K
private theorem poly_pn {f : ℕ → ℕ} (h : PB f) (K : ℕ) : PB (fun b => pn K (f b)) := (PB.const K).mul (pb_pow (h.add (PB.const 1)) K)

theorem bounds (K A : ℕ) : ∃ J, ∀ (p r : ℕ) (hp : 2 ≤ p) (hr : r ≤ cap (bitLen p)),
    let b := bitLen p; let z := cap b; let τ := mainSpaceBound A b; let σ := polyBound A b
    (r : ℝ)*(polyBound K z + (K : ℝ)*(τ+σ+1)) ≤ mainSpaceBound J b ∧
    polyBound K z + (K : ℝ)*(σ+1) ≤ polyBound J b := by
  let F (b : ℕ) := (cap b+1)*(pn K (cap b)+K*(pn A b +1)+K+1)
  have hc : PB cap := (PB.const 1000).mul (pb_pow (PB.id'.add (PB.const 3)) 2)
  have hf : PB F := (hc.add (PB.const 1)).mul ((((poly_pn hc K).add ((PB.const K).mul ((poly_pn PB.id' A).add (PB.const 1)))).add (PB.const K)).add (PB.const 1))
  obtain ⟨D,hD⟩ := hf
  obtain ⟨C,hC⟩ := stage1_complexity_dominance.2.2.1 D 0
  refine ⟨max D (C+A),?_⟩; intro p r hp hr b z τ σ
  have hτ : 1 ≤ τ := by apply Real.one_le_rpow (by norm_num); unfold logSafe; positivity
  have S : (F b : ℝ) ≤ polyBound D b := by unfold polyBound; exact_mod_cast hD b
  have T := (hC p 0 hp (by omega)).1
  have fs : (F b:ℝ) = ((z:ℝ)+1)*(polyBound K z+K*(σ+1)+K+1) := by dsimp [F,z,pn,polyBound,σ]; push_cast; ring
  have zn := Nat.cast_nonneg (α:=ℝ) z
  have z0 : 0 ≤ polyBound K z := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _) 
  have σ0 : 0 ≤ σ := by unfold σ polyBound; positivity
  have K0 := Nat.cast_nonneg (α:=ℝ) K
  have X0 : 0 ≤ polyBound K z + K*(σ+1) := by positivity
  have prod : mainSpaceBound C b * τ = mainSpaceBound (C+A) b := by unfold τ mainSpaceBound; rw [←Real.rpow_add (by norm_num)]; push_cast; congr 1; ring
  constructor
  · apply le_trans _ (stage1_complexity_dominance.1 _ _ _ (le_max_right D (C+A))).1
    rw [←prod]; apply le_trans _ (mul_le_mul_of_nonneg_right (S.trans T) (by linarith : 0 ≤ τ))
    rw [fs]; have hr' : (r:ℝ) ≤ z+1 := by exact_mod_cast (hr.trans (Nat.le_succ _))
    have mid : polyBound K z + K*(τ+σ+1) ≤ (polyBound K z+K*(σ+1)+K+1)*τ := by nlinarith [mul_nonneg X0 (sub_nonneg.mpr hτ)]
    rw [mul_assoc]; exact mul_le_mul hr' mid (add_nonneg z0 (mul_nonneg K0 (by linarith))) (by linarith)
  · apply le_trans _ (S.trans (stage1_complexity_dominance.1 _ _ _ (le_max_left D (C+A))).2)
    rw [fs]; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) z) (show 0 ≤ polyBound K z+K*(σ+1)+K+1 by positivity)]

theorem weakenRun {M : PrimitiveMachine} {o : Fin M.tapeCount} {a b : W} {τ σ τ' σ' : ℝ} (h : RunsWithin M o a b τ σ) (ht : τ ≤ τ') (hs : σ ≤ σ') : RunsWithin M o a b τ' σ' := by
  obtain ⟨n,c,run,halt,out,tm,sp⟩ := h; exact ⟨n,c,run,halt,out,tm.trans ht,fun k s hk tr => (sp k s hk tr).trans hs⟩

theorem machine (t : Bool) {O : PrimitiveMachine} (o : Fin O.tapeCount) (A : ℕ) : ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (J : ℕ),
    ∀ p r raw output, 2 ≤ p → 1 ≤ r → r ≤ cap (bitLen p) → tr t O o (mainSpaceBound A (bitLen p)) (polyBound A (bitLen p)) r raw [] output (cap (bitLen p)) →
    RunsWithin M out raw output (mainSpaceBound J (bitLen p)) (polyBound J (bitLen p)) := by
  obtain ⟨M,out,K,_,h⟩ := m89_polyT_oracle_loop (step t) (step_poly t) O o
  obtain ⟨J,hJ⟩ := bounds K A
  refine ⟨M,out,J,?_⟩; intro p r raw output hp hr hz trc
  let b := bitLen p
  have hτ : 0 ≤ mainSpaceBound A b := by unfold mainSpaceBound; positivity
  have hσ : 0 ≤ polyBound A b := by unfold polyBound; positivity
  apply weakenRun _ (hJ p r hp hz).1 (hJ p r hp hz).2
  apply h _ _ hτ hσ r (cap b) raw output hr
  have heq : pair = (fun (x y : W) => x.flatMap (fun d => [true,d]) ++ [false] ++ y) := funext (fun x => funext (frame_eq x))
  unfold tr at trc; rw [heq] at trc; exact trc
end DetDLP.S8B.Ctl

set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace


open DetDLP.S8B DetDLP.S8B.Ctl
theorem solution : CountOracle → ∃ (U : PrimitiveMachine) (u : Fin U.tapeCount) (V : PrimitiveMachine) (v : Fin V.tapeCount) (J : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 
      let b := bitLen p; let m := blockCount b
      ∃ L : Option (ℕ × FpSeed p m), m89_fp_plan_ok L ∧
        RunsWithin U u (countWord p) (Encoding.encodeList id [(countWord p),m89_fp_plan_word L]) (mainSpaceBound J b) (polyBound J b) ∧
        ∀ X : (ZMod p)ˣ, RunsWithin V v (encodeNatListBin [p,(X : ZMod p).val]) (Encoding.encodeList id [(encodeNatListBin [p,(X : ZMod p).val]),m89_fp_plan_word L]) (mainSpaceBound J b) (polyBound J b) := by
  rintro ⟨O,o,A,hO⟩
  obtain ⟨U,u,I,hu⟩ := machine false o A
  obtain ⟨V,v,H,hv⟩ := machine true o A
  refine ⟨U,u,V,v,max I H,?_⟩; intro p hp b m
  have h2 := hp.out.two_le
  let z := cap b; let n := seedLen p
  have fit : 49*unitCap b+80 ≤ z := by change 49*(20*(b+3)^2)+80 ≤ 1000*(b+3)^2; have h := Nat.pow_le_pow_left (show 3 ≤ b+3 by omega) 2; omega
  obtain ⟨hL,hb,_,hX⟩ := atomic_bounds p
  have hr : (countWord p).length ≤ unitCap b := (cw_le_prime p p le_rfl).trans (by dsimp [b]; omega)
  have common : ∃ L : Option (ℕ × FpSeed p m), m89_fp_plan_ok L ∧ ∃ r, 1 ≤ r ∧ r ≤ cap b ∧
      ∀ t raw, raw.length ≤ unitCap b → primeOf t raw = p → tr t O o (mainSpaceBound A b) (polyBound A b) r raw [] (enc [raw,m89_fp_plan_word L]) z := by
    by_cases hg : 64 ≤ p-1 ∧ 4096*fpM p ≤ p-1
    · obtain ⟨s,hs,hw⟩ := fp_law p hg.1 hg.2
      refine ⟨some (fpT p,s),hs,8*n+1,by omega,?_,?_⟩
      · change 8*seedLen p+1 ≤ z; rw [seedLen_eq]; dsimp [z,b] at fit ⊢; omega
      · intro t raw hr hpraw; have hh := large_run hO p t raw hr hpraw hg.1 hg.2
        simpa only [n,z,b,largeOutput,chosen,m89_fp_plan_word,hw,seedLen_eq,enc] using hh
    · refine ⟨none,hg,1,le_rfl,by change 1 ≤ z; omega,?_⟩
      intro t raw hr hpraw; apply Or.inl; refine ⟨?_,?_,?_⟩
      · rw [step_init,hpraw]; unfold init; rw [blocks_eq]; have he : (p-1).size = bitLen p := by
          apply le_antisymm
          · apply Nat.size_le.mpr; have := Nat.le_pow_clog (by decide : 1 < 2) p; change p-1 < 2^(Nat.clog 2 p); omega
          · apply (Nat.clog_le_iff_le_pow (by decide)).2; have := Nat.lt_size_self (p-1); omega
        rw [he,if_neg hg]; rfl
      · rw [pair_len]; simp; omega
      · have := enc_len [raw,[false]] (unitCap b) (by simp; exact ⟨hr,by dsimp [b]; omega⟩); change (enc [raw,[false]]).length ≤ z; simp at this; omega
  obtain ⟨L,hL,r,hr1,hr2,trace⟩ := common
  refine ⟨L,hL,?_,?_⟩
  · have h := hu p r _ _ h2 hr1 hr2 (trace false _ hr (base0 p))
    exact weakenRun h (stage1_complexity_dominance.1 _ _ b (le_max_left I H)).1 (stage1_complexity_dominance.1 _ _ b (le_max_left I H)).2
  · intro X; have hx := ZMod.val_lt (X : ZMod p)
    have h := hv p r _ _ h2 hr1 hr2 (trace true _ (hX _ hx) (base1 p _))
    exact weakenRun h (stage1_complexity_dominance.1 _ _ b (le_max_right I H)).1 (stage1_complexity_dominance.1 _ _ b (le_max_right I H)).2

#print axioms solution
