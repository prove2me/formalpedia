-- Prove2me | solution 1 for DetDLP.m3d_ec_compiled_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:57:21.732237+00:00
-- url     : https://prove2.me/submissions/cae5b766-d4b4-4c54-a603-79a6315f96e6

import Definitions.Def_DetDLP_M3D_ECFastDefs
import Theorems.Thm_DetDLP_m3d_ec_step_poly
import Definitions.Def_DetDLP_W3C_NineOracleLoop
import Definitions.Def_DetDLP_W5_M6TapeSimulator
import Definitions.Def_DetDLP_W1_Bounds

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

end DetDLP.M3D.Fast.ECRun
namespace DetDLP.M3D.Fast.ECRun.Bounds
open Groundwork ECStep NineOracleLoop DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.Computation

theorem outputLength {E : PrimitiveMachine} {o : Fin E.tapeCount} {q ans : Wd} {t s : ℝ}
    (h : RunsWithin E o q ans t s) : ans.length ≤ ⌊s⌋₊ + 8 := by
  obtain ⟨k,c,_,_,eq,tr⟩ := w5_EntryTapeCode.call E o q ans t s h (fun _ => false) (fun _ => none)
  have hb := tr.prefix le_rfl tr.trace (w5_EntryTapeCode.lane E o false true)
  rw [← eq]; refine le_trans ?_ hb
  generalize c.stacks (w5_EntryTapeCode.lane E o false true) = tags
  generalize c.stacks (w5_EntryTapeCode.lane E o false false) = vals
  induction tags generalizing vals with
  | nil => rfl
  | cons a l ih => cases a <;> cases vals <;> simp [w5_EntryTapeCode.extract,ih]

private theorem pairFst {s t x y : Wd} (h : pairWord s x = pairWord t y) : s = t := by
  have hh := congrArg (fun w => (parse (true :: w)).1.reverse) h
  simpa only [parsePair,List.reverse_reverse] using hh

private theorem sendState {slot : Fin 9} {s t x y : Wd} (h : send slot s x = false :: pairWord t y) : t = s :=
  (pairFst (List.cons.inj h).2).symm

private theorem mkState {i o p k r f a : Wd} {L d ph j : ℕ} (hph : ph ≤ 10) (hj : j ≤ d+3)
    (ho : o.length ≤ L) (hp : p.length ≤ L) (hk : k.length ≤ L) (hr : r.length ≤ L)
    (hf : f.length ≤ d) (ha : a.length ≤ L) : StateBounded i L d (packState ph j i o p k r f a) :=
  Or.inr ⟨_,_,_,_,_,_,_,_,rfl,hph,hj,ho,hp,hk,hr,hf,ha⟩

private theorem transition {i st ans st' q : Wd} {L d : ℕ} (head : i.headD true = true)
    (hs : StateBounded i L d st) (ha : ans.length ≤ L)
    (he : ecStep (pairWord st ans) = false :: pairWord st' q) : StateBounded i L (d+1) st' := by
  rcases hs with rfl | ⟨ph,j,o,p,k,r,f,a,rfl,hph,hj,ho,hp,hk,hr,hf,haux⟩
  · rw [entry head] at he
    rw [sendState he]; apply mkState <;> simp <;> omega
  rw [packed] at he
  simp only [ECStep.round,show PolyT.bval (get (fields ph j i o p k r f a) 0) = ph from decode_count ph] at he
  split_ifs at he <;>
    simp only [case0,case1,case2,case3,case4,case6,case7,case8,case9,massPhase,cutOrChild,
      beginRoot,decompose,show idx (fields ph j i o p k r f a) = j from decode_count j] at he
  all_goals (try split_ifs at he)
  all_goals first | exact Bool.noConfusion (List.cons.inj he).1 | (rw [sendState he]; apply mkState <;>
    (try simp only [List.length_append,List.length_cons,List.length_nil,inp,ord,plan,blk,rep,pre,ECStep.get,fields,
      List.getD_cons_zero,List.getD_cons_succ]) <;> omega)

private theorem indexLength (n : ℕ) : (countWord n).length ≤ n+1 := by
  by_cases h : n=0
  · simp [h,countWord]
  · simp only [countWord,if_neg h,Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr n.lt_two_pow_self).trans (Nat.le_succ _)

private theorem pairLength (x y : Wd) : (pairWord x y).length = 2*x.length+1+y.length := by
  rw [show pairWord x y = Encoding.frame x ++ y from congrArg (· ++ y) (frame_correct x)]
  simp [w3_frameLength]


private theorem pairBound {i st ans : Wd} {L d fuel : ℕ} (hs : StateBounded i L d st)
    (ha : ans.length ≤ L) (hd : d ≤ fuel) : (pairWord st ans).length ≤ inputBound i.length L fuel := by
  rw [pairLength]; unfold inputBound
  rcases hs with rfl | ⟨ph,j,o,p,k,r,f,a,rfl,hph,hj,ho,hp,hk,hr,hf,haux⟩
  · omega
  · have := indexLength ph; have := indexLength j
    simp only [packState,Encoding.encodeList,id_eq,List.length_cons,List.length_nil,List.length_append,w3_frameLength]; omega

theorem uniformLoop : ∃ K : ℕ, ∀ {i out : Wd} {fuel L : ℕ} {call : Wd → Wd → Prop},
    i.headD true = true → Runs (BoundedCall L call) fuel i [] out →
    let n := inputBound i.length L fuel
    LoopRuns ecStep call fuel i [] out (n+K*(3*n+3)^K) := by
  obtain ⟨_,K,_,hK⟩ := m3d_ec_step_poly
  refine ⟨K,?_⟩; intro i out fuel L call hi run n
  let lim := n+K*(3*n+3)^K
  have loop (left d : ℕ) (hd : left+d=fuel) (st ans : Wd) (hs : StateBounded i L d st)
      (ha : ans.length ≤ L) (h : Runs (BoundedCall L call) left st ans out) :
      LoopRuns ecStep call left st ans out lim := by
    obtain ⟨old,tr⟩ := h
    induction left generalizing d st ans with
    | zero => exact False.elim tr
    | succ left ih =>
      have hIn : (pairWord st ans).length ≤ n := pairBound hs ha (by omega)
      have hOut := hK (pairWord st ans)
      simp only [len_bools] at hOut
      have cost : K*(3*(pairWord st ans).length+2+1)^K ≤ K*(3*n+3)^K :=
        Nat.mul_le_mul_left K (Nat.pow_le_pow_left (by omega) K)
      rcases tr with ⟨he,_,_⟩ | ⟨st',q,y,he,_,_,_,⟨hc,hy⟩,ht⟩
      · apply Or.inl; refine ⟨he,by dsimp [lim]; omega,?_⟩
        rw [he,List.length_cons] at hOut; dsimp [lim]; omega
      · apply Or.inr; refine ⟨st',q,y,he,by dsimp [lim]; omega,?_,?_,hc,?_⟩
        · rw [he,List.length_cons] at hOut; dsimp [lim]; omega
        · have hn : L ≤ n := by dsimp [n,inputBound]; omega
          dsimp [lim]; omega
        · exact ih (d+1) (by omega) st' y (transition hi hs ha he) hy ht
  exact loop fuel 0 (by omega) i [] (Or.inl rfl) (Nat.zero_le _) run

/-- One machine for all inputs and both branches. Only the oracle budgets,
    the number of rounds, and the answer bound vary with the input. -/
theorem compiled (A : Fin 9 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C K : ℕ),
    ∀ {i y : Wd} {r L : ℕ} {τ σ : ℝ}, i.headD true = true → 1 ≤ r → 0 ≤ τ → 0 ≤ σ →
      Runs (BoundedCall L (NineCall A o τ σ)) r i [] y →
      let n := roundLimit K (inputBound i.length L r)
      RunsWithin D out i y (r*(polyBound C n+C*(τ+σ+1))) (polyBound C n+C*(σ+1)) := by
  obtain ⟨K,bound⟩ := uniformLoop
  obtain ⟨D,out,C,_,loop⟩ := W3C.NineOracleLoop.nine_oracle_polyT_loop ecStep m3d_ec_step_poly A o
  exact ⟨D,out,C,K,fun {_ _ _ _ τ σ} head hr ht hs run =>
    loop τ σ ht hs _ _ _ _ hr (bound head run)⟩

end DetDLP.M3D.Fast.ECRun.Bounds

namespace DetDLP.M3D.Fast.ECRun.Bounds
open DetDLP_W1_Bounds Groundwork ECStep NineOracleLoop
open OAI.Algorithms.SubexponentialSAT.Computation

private structure Budget (J : ℕ) where
  b : ℕ
  pos : 1 ≤ b
  i : Wd
  r : ℕ
  L : ℕ
  τ : ℝ
  σ : ℝ
  ht : 0 ≤ τ
  hs : 0 ≤ σ
  sizes : (i.length : ℝ) + r + L + σ ≤ mainSpaceBound J b
  time : τ ≤ mainTimeBound J b

private theorem costs (J C K : ℕ) : ∃ H : ℕ, ∀ v : Budget J,
    let n := roundLimit K (inputBound v.i.length v.L v.r)
    v.r*(polyBound C n+C*(v.τ+v.σ+1)) ≤ mainTimeBound H v.b ∧
    polyBound C n+C*(v.σ+1) ≤ mainSpaceBound H v.b := by
  let S := fun v : Budget J => sScale v.b
  let T := fun v : Budget J => 4*tScale v.b
  have hS (v) : 1 ≤ S v := scales_one v.pos
  have hST (v) : S v ≤ T v := compareScale v.b
  have hT (v) : 1 ≤ T v := (hS v).trans (hST v)
  have ds : Dom S (fun v => mainSpaceBound J v.b) := ⟨J, fun v => (sEq v.b J).ge⟩
  have dt : Dom T (fun v => v.τ) := by
    refine ⟨J,fun v => v.time.trans ?_⟩; rw [← tEq]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h : 0 ≤ tScale v.b := by unfold tScale; positivity
    dsimp only [T]; exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have dr : Dom S (fun v => (v.r : ℝ)) := ds.weaken fun v => by linarith [v.sizes,v.hs,Nat.cast_nonneg (α:=ℝ) v.L,Nat.cast_nonneg (α:=ℝ) v.i.length]
  have dσ : Dom S (fun v => v.σ) := ds.weaken fun v => by linarith [v.sizes,Nat.cast_nonneg (α:=ℝ) v.L,Nat.cast_nonneg (α:=ℝ) v.i.length,Nat.cast_nonneg (α:=ℝ) v.r]
  let u := fun v : Budget J => inputBound v.i.length v.L v.r
  let n := fun v : Budget J => roundLimit K (u v)
  have du : Dom S (fun v => (u v : ℝ)) := by
    have h : Dom S (fun v => (v.i.length : ℝ)+v.L+v.r) := ds.weaken fun v => by linarith [v.sizes,v.hs]
    simpa [u,inputBound] using (dconst hS 200).mul (h.add hS (dconst hS 1)) (fun _ => by positivity) (fun _ => by positivity)
  have dn : Dom S (fun v => (n v : ℝ)) := by
    have h := (dconst hS 3).mul du (fun _ => by positivity) (fun _ => by positivity)
    have h' := (h.add hS (dconst hS 3)).pow hS (fun _ => by positivity) K
    simpa [n,roundLimit] using du.add hS ((dconst hS K).mul h' (fun _ => by positivity) (fun _ => by positivity))
  have dp : Dom S (fun v => polyBound C (n v)) := by
    simpa only [polyBound,Nat.cast_one] using (dconst hS C).mul ((dn.add hS (dconst hS 1)).pow hS (fun _ => by positivity) C) (fun _ => by positivity) (fun _ => by positivity)
  have sp := dp.add hS ((dconst hS C).mul (dσ.add hS (dconst hS 1)) (fun _ => by positivity) (fun v => by linarith [v.hs]))
  have mixed := (dt.add hT (liftTime hS hST dσ)).add hT (dconst hT 1)
  have tm := (liftTime hS hST dr).mul ((liftTime hS hST dp).add hT ((dconst hT C).mul mixed
    (fun _ => by positivity) (fun v => by linarith [v.ht,v.hs]))) (fun _ => by positivity)
    (fun v => by dsimp [polyBound]; have := v.ht; have := v.hs; positivity)
  obtain ⟨a,ha⟩ := tm; obtain ⟨z,hz⟩ := sp
  simp only [Nat.cast_one] at ha hz
  refine ⟨max (4*a) z, fun v => ⟨(ha v).trans ?_,(hz v).trans ?_⟩⟩
  · rw [← tEq]; have eq : E (T v) a = E (tScale v.b) (4*a) := by unfold E T; push_cast; congr 1; ring
    rw [eq]; apply monoE _ (le_max_left ..); unfold tScale; positivity
  · rw [← sEq]; apply monoE _ (le_max_right ..); linarith [hS v]

/-- Uniform final resource bound, instantiated with a budget shared by the
    small scan and the native trace. -/
theorem compiledMain (A : Fin 9 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) (J : ℕ) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (H : ℕ),
    ∀ {b : ℕ} {i y : Wd} {r L : ℕ} {τ σ : ℝ}, 1 ≤ b → i.headD true = true → 1 ≤ r →
      0 ≤ τ → 0 ≤ σ → (i.length : ℝ)+r+L+σ ≤ mainSpaceBound J b → τ ≤ mainTimeBound J b →
      Runs (BoundedCall L (NineCall A o τ σ)) r i [] y →
      RunsWithin D out i y (mainTimeBound H b) (mainSpaceBound H b) := by
  obtain ⟨D,out,C,K,compile⟩ := compiled A o
  obtain ⟨H,budget⟩ := costs J C K
  refine ⟨D,out,H,?_⟩; intro b i y r L τ σ hb head hr ht hs sizes time run
  obtain ⟨t,s⟩ := budget ⟨b,hb,i,r,L,τ,σ,ht,hs,sizes,time⟩
  exact MachineComposition.runsWithin_mono (compile head hr ht hs run) t s

end DetDLP.M3D.Fast.ECRun.Bounds

namespace DetDLP.M3D.Fast.ECRun.Bounds
open ECStep NineOracleLoop OAI.Algorithms.SubexponentialSAT.Computation

private theorem strengthen {A : Fin 9 → PrimitiveMachine} {o : ∀ j, Fin (A j).tapeCount}
    {τ σ : ℝ} {fuel lim : ℕ} {st ans out : Wd}
    (h : LoopRuns ecStep (NineCall A o τ σ) fuel st ans out lim) :
    LoopRuns ecStep (BoundedCall (⌊σ⌋₊ + 8) (NineCall A o τ σ)) fuel st ans out lim := by
  induction fuel generalizing st ans with
  | zero => exact False.elim h
  | succ fuel ih =>
    rcases h with done | ⟨st',q,a,he,hi,hq,ha,hc,next⟩
    · exact Or.inl done
    · obtain ⟨j,p,eq,run⟩ := hc
      exact Or.inr ⟨_,_,_,he,hi,hq,ha,⟨⟨j,p,eq,run⟩,outputLength run⟩,ih next⟩

theorem compiledRuns (A : Fin 9 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) (J : ℕ) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (H : ℕ),
    ∀ {b : ℕ} {i y : Wd} {r : ℕ} {τ σ : ℝ}, 1 ≤ b → i.headD true = true → 1 ≤ r →
      0 ≤ τ → 0 ≤ σ → (i.length : ℝ)+r+2*σ+8 ≤ mainSpaceBound J b → τ ≤ mainTimeBound J b →
      Runs (NineCall A o τ σ) r i [] y → RunsWithin D out i y (mainTimeBound H b) (mainSpaceBound H b) := by
  obtain ⟨D,out,H,compile⟩ := compiledMain A o J
  refine ⟨D,out,H,?_⟩; intro b i y r τ σ hb head hr ht hs sizes time run
  obtain ⟨n,trace⟩ := run
  exact compile hb head hr ht hs (by push_cast; linarith [Nat.floor_le hs]) time ⟨n,strengthen trace⟩

end DetDLP.M3D.Fast.ECRun.Bounds
open DetDLP DetDLP.M3D.Fast.ECRun DetDLP.M3D.Fast.NineOracleLoop OAI.Algorithms.SubexponentialSAT.Computation
theorem solution (A : Fin 9 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) (J : ℕ) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (H : ℕ),
    ∀ {b : ℕ} {i y : Wd} {r : ℕ} {τ σ : ℝ}, 1 ≤ b → i.headD true = true → 1 ≤ r →
      0 ≤ τ → 0 ≤ σ → (i.length : ℝ)+r+2*σ+8 ≤ mainSpaceBound J b → τ ≤ mainTimeBound J b →
      Runs (NineCall A o τ σ) r i [] y → RunsWithin D out i y (mainTimeBound H b) (mainSpaceBound H b) := by 
  exact DetDLP.M3D.Fast.ECRun.Bounds.compiledRuns A o J
