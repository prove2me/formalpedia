-- Prove2me | solution 1 for DetDLP.d4_padded_tree_rank_walker_v2_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T10:32:00.951389+00:00
-- url     : https://prove2.me/submissions/39727ea7-e7d5-454b-9c29-cd201b97d076

import Definitions.Def_DetDLP_D4WalkerTranscriptV2
import Theorems.Thm_DetDLP_f9a2_b_mul_poly
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Theorems.Thm_DetDLP_d4_rank_walker_v2_step_poly
set_option autoImplicit false
open DetDLP DetDLP.D4RankWalker DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace OAI.Algorithms.SubexponentialSAT.Computation

private theorem scan_frame (x rev : Wd) (acc : List Wd) :
    (Encoding.frame x).foldl scan (false,true,rev,acc) = (false,false,[],(rev.reverse ++ x) :: acc) := by
  induction x generalizing rev with
  | nil => simp [Encoding.frame,scan]
  | cons b x ih => change (Encoding.frame x).foldl scan (false,true,b::rev,acc) = _; simpa using ih (b :: rev)
private theorem scan_pack (xs acc : List Wd) :
    (pack xs).foldl scan (false,false,[],acc) = (true,true,[],xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    change (Encoding.frame x ++ pack xs).foldl scan (false,true,[],acc) = _
    rw [List.foldl_append,scan_frame]; simpa using ih (x :: acc)
@[local simp] private theorem unpack_pack (xs : List Wd) : unpack (pack xs) = xs := by simp [unpack,scan_pack]
private theorem parseAux (x xs acc : Wd) : ∀ fuel : Wd, x.length ≤ fuel.length →
    fuel.foldl advance (acc,Encoding.frame x ++ xs) = (x.reverse ++ acc,false :: xs) := by
  induction x generalizing acc with
  | nil => intro fuel _; induction fuel <;> simp_all [Encoding.frame,advance,List.foldl]
  | cons b x ih => intro fuel hf; cases fuel with
    | nil => simp at hf
    | cons k fuel => simpa [Encoding.frame,advance,List.foldl,List.append_assoc] using ih (b::acc) fuel (by simpa using hf)
private theorem lens (x : Wd) : (Encoding.frame x).length = 2*x.length + 1 := by
  induction x with
  | nil => rfl
  | cons b x ih => change (Encoding.frame x).length + 1 + 1 = _; simp; omega
private theorem parsePair (a b : Wd) : parse (true :: pair a b) = (a.reverse,false::b) := by
  unfold parse pair; rw [frame_correct]; simp only [List.tail_cons]
  rw [parseAux]; simp; simp [lens]; omega
@[local simp] private theorem firstPair (a b : Wd) : first (true :: pair a b) = a := by simp [first,parsePair]
@[local simp] private theorem morePair (a b : Wd) : more (true :: pair a b) = b := by simp [more,parsePair]
private theorem width_eq (n : ℕ) : digitWidth n = Nat.clog 2 n := by
  unfold digitWidth; apply le_antisymm
  · apply Nat.size_le.mpr
    have := Nat.le_pow_clog (by decide : 1 < 2) n
    have : 0 < 2^Nat.clog 2 n := by positivity
    omega
  · apply (Nat.clog_le_iff_le_pow (by decide)).2; have := Nat.lt_size_self (n-1); omega

private def cap : ℕ → ℕ | 0 => 0 | n+1 => 1 + 64*cap n
private theorem cap_eq (n : ℕ) : 63*cap n+1=64^n := by induction n with | zero => rfl | succ n ih => rw [pow_succ,← ih]; simp [cap]; ring
private def unitCost (ctx i : Wd) := cap (num ctx 0-num i 0)
private def potential (ctx : Wd) (xs : List Wd) := (xs.map (unitCost ctx)).sum
private theorem nextCost (ctx i ans : Wd) (hi : small ctx i = false) :
    potential ctx (children i ans) + 1 = unitCost ctx i := by
  have h : num i 0 < num ctx 0 := by have h := hi; simp [small] at h; omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_lt h
  have h1 : num ctx 0 - num i 0 = k+1 := by omega
  have h2 : num ctx 0 - (num i 0+1) = k := by omega
  have childD (g : ℕ) : unitCost ctx (childWord i (num (fld ans 0) 4) (fld (fld ans 3) g)) = cap k := by
    have hd : num (childWord i (num (fld ans 0) 4) (fld (fld ans 3) g)) 0 = num i 0 + 1 := by simp [childWord,num,fld]
    simp only [unitCost,hd,h2]
  simp only [potential, children, List.map_map, Function.comp_def, childD]
  simp [unitCost,h1,cap]; omega
private theorem drop_active (ctx : Wd) (xs : List Wd) (i : Wd) (tail : List Wd)
    (h : xs.drop ((xs.map (small ctx)).idxOf false) = i :: tail) : small ctx i = false := by
  induction xs with
  | nil => simp at h
  | cons a xs ih => cases ha : small ctx a <;> simp [ha] at h
                    · obtain ⟨rfl,rfl⟩ := h; exact ha
                    · exact ih h
private theorem potentialDrop (ctx : Wd) (xs : List Wd) (k : ℕ) :
    potential ctx (xs.drop k) ≤ potential ctx xs := by
  have h := congrArg (potential ctx) (List.take_append_drop k xs)
  simp only [potential,List.map_append,List.sum_append] at *; omega

private theorem step_start (ctx : Wd) (i : WorkItem) (b u : ℕ) :
  walkerStepV2 (pair (startV2 ctx i b u) []) = dispatchV2 ctx [i.bits] [] b u (oneWord ctx) 0 := by
  simp [walkerStepV2,startV2,fld,num]
private theorem step_count (ctx : Wd) (xs ys : List Wd) (b u : ℕ) (acc ans : Wd) (lossSum : ℕ) :
  walkerStepV2 (pair (phaseStateV2 [true] ctx xs ys b u acc lossSum) ans) = countPhaseV2 ctx xs ys b u acc ans lossSum := by
  simp [walkerStepV2,phaseStateV2,fld,num]
private theorem step_branch (ctx i : Wd) (tail ys : List Wd) (b u : ℕ) (acc ans : Wd) (lossSum : ℕ) :
  walkerStepV2 (pair (phaseStateV2 [false] ctx (i::tail) ys b u acc lossSum) ans) =
  dispatchV2 ctx (children i ans ++ tail) ys b u (productV2 ctx acc ans) (lossSum + stepLoss ctx i) := by
  simp [walkerStepV2,phaseStateV2,fld,num]

private def Chain : List Call → Wd → Wd → Prop
  | [],cmd,out => cmd = true :: out
  | (st,q,ans)::cs,cmd,out => cmd = issue st q ∧ Chain cs (walkerStepV2 (pair st ans)) out

private theorem walk_chain (ctx : Wd) (F : Wd → WalkerStep) (fuel : ℕ)
    (xs ys : List Wd) (b u : ℕ) (acc : Wd) (lossSum : ℕ) (bound : potential ctx xs ≤ fuel) :
    let cs := callsV2 ctx F fuel xs ys b u acc lossSum
    let out := tag ((unrollAuxV2 ctx F fuel xs ys acc lossSum).read b u)
    Chain cs (dispatchV2 ctx xs ys b u acc lossSum) out ∧ cs.length ≤ 2*fuel := by
  dsimp only
  induction fuel generalizing xs ys b u acc lossSum with
  | zero =>
    cases hp : xs.drop ((xs.map (small ctx)).idxOf false) with
    | nil =>
      rw [unrollAuxV2.eq_1,callsV2.eq_2 _ _ _ _ _ _ _ _ _ (by simp [hp])]
      by_cases h : u=0 <;> simp [hp,dispatchV2,Chain,D4RankCode.Tree.read,h,tag]
    | cons i tail =>
      have h := nextCost ctx i [] (drop_active ctx xs i tail hp)
      have z := potentialDrop ctx xs ((xs.map (small ctx)).idxOf false)
      rw [hp] at z; change unitCost ctx i + potential ctx tail ≤ potential ctx xs at z; omega
  | succ fuel ih =>
    cases hp : xs.drop ((xs.map (small ctx)).idxOf false) with
    | nil =>
      rw [unrollAuxV2.eq_1,callsV2.eq_2 _ _ _ _ _ _ _ _ _ (by simp [hp])]
      by_cases h : u=0 <;> simp [hp,dispatchV2,Chain,D4RankCode.Tree.read,h,tag]
    | cons i tail =>
      let s := F i; let w := digitWidth s.n; let d := u % 2^w
      have wc : Nat.clog 2 s.n = w := (width_eq s.n).symm
      have hi := drop_active ctx xs i tail hp
      have z := potentialDrop ctx xs ((xs.map (small ctx)).idxOf false)
      rw [hp] at z
      let ys' := ys ++ xs.take ((xs.map (small ctx)).idxOf false)
      change unitCost ctx i + potential ctx tail ≤ potential ctx xs at z
      rw [unrollAuxV2.eq_1,callsV2.eq_1 _ _ _ _ _ _ _ _ _ _ _ hp]
      simp only [dispatchV2,hp,List.isEmpty_cons,List.headD_cons,D4RankCode.Tree.read]
      simp only [← width_eq]
      by_cases hb : w ≤ b
      · by_cases hd : d < s.n
        · let ans := s.branch ⟨d,hd⟩
          have hn := nextCost ctx i ans hi
          have bound' : potential ctx (children i ans ++ tail) ≤ fuel := by
            unfold potential at *; rw [List.map_append,List.sum_append]; omega
          have hr := ih (children i ans ++ tail) ys' (b-w) (u/2^w) (productV2 ctx acc ans) (lossSum + stepLoss ctx i) bound'
          dsimp only [d,w,s,ys',ans] at hb hd hr
          simp only [hb,hd,ite_true,dif_pos,Chain,List.length_cons,step_count,countPhaseV2,decode_count,step_branch,List.headD_cons,true_and]
          exact ⟨⟨rfl,rfl,hr.1⟩,by omega⟩
        · dsimp only [d,w,s] at hb hd
          simp [hb,hd,Chain,step_count,countPhaseV2,decode_count,tag]
          exact ⟨rfl,by omega⟩
      · dsimp only [w,s] at hb
        simp [hb,Chain,step_count,countPhaseV2,decode_count,tag]
        exact ⟨rfl,by omega⟩

private def Loop (O : PrimitiveMachine) (o : Fin O.tapeCount) (τ σ : ℝ) (L r : ℕ) (st ans out : Wd) : Prop :=
  Nat.rec (motive := fun _ => Wd → Wd → Wd → ℕ → Prop) (fun _ _ _ _ => False)
    (fun _ prev st ans out L =>
    (walkerStepV2 (pair st ans) = true :: out ∧ (pair st ans).length ≤ L ∧ out.length ≤ L) ∨
    ∃ st' q ans', walkerStepV2 (pair st ans) = issue st' q ∧ (pair st ans).length ≤ L ∧
      (pair st' q).length ≤ L ∧ ans'.length ≤ L ∧ RunsWithin O o q ans' τ σ ∧ prev st' ans' out L) r st ans out L
private theorem span_bound (cs : List Call) (e : Call) (he : e ∈ cs) : span e ≤ ((cs.map span).foldr max 0) := by
  induction cs with
  | nil => simp at he
  | cons h cs ih =>
    rcases List.mem_cons.mp he with rfl|he
    · exact le_max_left ..
    · exact (ih he).trans (le_max_right ..)
private theorem suffixLe (a b : Wd) : b.length ≤ (pair a b).length := by simp [pair]
private theorem chain_loop (O : PrimitiveMachine) (o : Fin O.tapeCount) (τ σ : ℝ) (L : ℕ)
    (cs : List Call) (st ans out : Wd) (h : Chain cs (walkerStepV2 (pair st ans)) out)
    (h0 : (pair st ans).length ≤ L) (h1 : out.length ≤ L)
    (hcs : ∀ e ∈ cs, span e ≤ L ∧ RunsWithin O o e.2.1 e.2.2 τ σ) :
    Loop O o τ σ L (cs.length+1) st ans out := by
  induction cs generalizing st ans with
  | nil => exact Or.inl ⟨h,h0,h1⟩
  | cons e cs ih =>
    obtain ⟨st',q,ans'⟩ := e
    have hh := hcs _ List.mem_cons_self
    have hsq := (le_max_left ..).trans hh.1
    have hsa := (le_max_right ..).trans hh.1
    have next := ih st' ans' h.2 hsa (fun e he => hcs _ (List.mem_cons_of_mem _ he))
    exact Or.inr ⟨st',q,ans',h.1,h0,hsq,(suffixLe st' ans').trans hsa,hh.2,next⟩

private theorem tighten (O : PrimitiveMachine) (o : Fin O.tapeCount) (q ans : Wd) (τ σ : ℝ) (L : ℕ)
    (hq : q.length ≤ L) (h : RunsWithin O o q ans τ σ) :
    RunsWithin O o q ans τ (min σ (O.tapeCount*(L+2*τ+1))) := by
  rcases h with ⟨n,c,tr,hh,hw,ht,hs⟩
  refine ⟨n,c,tr,hh,hw,ht,fun k d hk hd => le_min (hs k d hk hd) ?_⟩
  have bound := locatedTrace_space_le_of_length hd
  have cast : (visitedSpace d : ℝ) ≤ (O.tapeCount : ℝ) * (q.length+2*(k:ℝ)+1) := by exact_mod_cast bound
  apply cast.trans; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have leK : (k:ℝ) ≤ τ := (by exact_mod_cast hk : (k:ℝ) ≤ n).trans ht
  have leQ : (q.length:ℝ) ≤ L := by exact_mod_cast hq
  linarith

private theorem inflate (k t L N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) (τ σ : ℝ) (ht : 0 ≤ τ) (hs : 0 ≤ σ) :
    let K := 12*(k+1)*(t+1)+k+2
    let s := min σ ((t:ℝ)*(L+2*τ+1))
    (3*(N:ℝ))*(polyBound k L + k*(τ+s+1)) ≤ polyBound K (L+N)*(τ+1) ∧
    polyBound k L+k*(s+1) ≤ polyBound K (L+N)+K*(σ+1) := by
  intro K s
  let X : ℝ := (L+N : ℕ)+1
  let Z := X^(k+1)
  let Y := X^K
  have x1 : 1 ≤ X := by dsimp [X]; linarith [Nat.cast_nonneg (α:=ℝ) (L+N)]
  have hkK : k+2 ≤ K := by dsimp [K]; omega
  have nk : (N:ℝ) ≤ X := by dsimp [X]; push_cast; linarith
  have lk : (L:ℝ)+1 ≤ X := by dsimp [X]; push_cast; linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (L:ℝ)+1) lk k
  have hpow1 : 1 ≤ X^k := one_le_pow₀ x1
  have hZ : X ≤ Z := (by simpa only [pow_one] using pow_le_pow_right₀ x1 (by omega : 1 ≤ k+1))
  have hzY : Z ≤ Y := pow_le_pow_right₀ x1 (by omega)
  have prodY : X*Z ≤ Y := by
    have h := pow_le_pow_right₀ x1 hkK
    simpa only [Z,Y,pow_succ,mul_comm X] using h
  have lkZ := lk.trans hZ
  have s1 : s ≤ (t:ℝ)*(L+2*τ+1) := min_le_right ..
  have s2 : s ≤ σ := min_le_left ..
  have sm : s ≤ 2*t*Z*(τ+1) := by
    apply s1.trans
    have hZ1 : 1 ≤ Z := x1.trans hZ
    nlinarith only [mul_nonneg (show 0 ≤ (t:ℝ) by positivity) (show 0 ≤ 2*Z*(τ+1)-(L+2*τ+1) by nlinarith [mul_nonneg (sub_nonneg.mpr hZ1) ht])]
  have pk : polyBound k L ≤ (k:ℝ)*Z := by
    unfold polyBound; apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hpow.trans (pow_le_pow_right₀ x1 (by omega))
  have KK : (K:ℝ) = 12*((k:ℝ)+1)*(t+1)+k+2 := by simp [K]
  have hkp : (k:ℝ) ≤ K := by exact_mod_cast (show k ≤ K by omega)
  have hZ1 : 1 ≤ Z := x1.trans hZ
  have ib : polyBound k L + k*(τ+s+1) ≤ (4*(k+1)*(t+1):ℝ)*Z*(τ+1) := by
    apply add_le_add pk (mul_le_mul_of_nonneg_left (by linarith [sm] : τ+s+1 ≤ τ+2*t*Z*(τ+1)+1) (by positivity)) |>.trans
    nlinarith only [ht,hZ1, mul_nonneg (sub_nonneg.mpr hZ1) ht, mul_nonneg (show 0 ≤ (k:ℝ) by positivity) (show 0 ≤ Z*(τ+1)-(τ+1) by nlinarith [mul_nonneg (sub_nonneg.mpr hZ1) ht]), mul_nonneg (show 0 ≤ (k:ℝ) by positivity) (show 0 ≤ Z*τ by positivity), show 0 ≤ (k:ℝ)*t*Z*(τ+1) by positivity, show 0 ≤ (t:ℝ)*Z*(τ+1) by positivity, show 0 ≤ Z*(τ+1) by positivity]
  change _ ≤ K*Y*(τ+1) ∧ _ ≤ K*Y+K*(σ+1)
  constructor
  · calc
      _ ≤ (3*X)*((4*(k+1)*(t+1):ℝ)*Z*(τ+1)) := mul_le_mul (by linarith) ib (by dsimp [s,polyBound]; positivity) (by positivity)
      _ = (12*(k+1)*(t+1):ℝ)*(X*Z)*(τ+1) := by ring
      _ ≤ K*Y*(τ+1) := by gcongr; linarith [KK]
  · exact add_le_add (pk.trans (mul_le_mul hkp hzY (by positivity) (by positivity))) (mul_le_mul hkp (by linarith) (by dsimp [s]; positivity) (by positivity))

private theorem context_depth (S m p guard l : ℕ) (f : Wd) : num (contextV2 S m p guard l f) 0 = Nat.clog 32 (4*m) := by simp [num,fld,contextV2]

private theorem ask_eq (S m p guard l : ℕ) (f : Polynomial ℤ) (i : WorkItem) (j : ℕ) (h : i.depth < Nat.clog 32 (4*m)) :
    ask (contextV2 S m p guard l (AppendixD4.polynomialBits f)) i.bits j =
    D4NodeQuery.request i.G (fun v : Fin i.pins.length => (i.pins.get v).2)
      (D3Stopped.shift S i.depth) (D3Stopped.width S i.depth) i.pCurr l f j := by
  have rwrow : rowAt (contextV2 S m p guard l (AppendixD4.polynomialBits f)) i.bits = row S i.depth := by
    simp [rowAt,contextV2,WorkItem.bits,num,fld,h]
  unfold ask; rw [rwrow]
  have hh : ((unpack (fld i.bits 3)).map fun pin => num pin 1) = List.ofFn (fun v : Fin i.pins.length => (i.pins.get v).2.val) := by
    simp only [WorkItem.bits,fld,unpack_pack,List.getD_cons_succ,List.getD_cons_zero,List.map_map]
    apply List.ext_getElem
    · simp
    · intro k hk hk'; simp [Function.comp_def,num,fld,encodeNatListBin,← show ∀ xs : List ℕ, pack (xs.map countWord) = Encoding.encodeList countWord xs from fun xs => by induction xs with | nil => rfl | cons _ _ ih => simp [pack,Encoding.encodeList] at *; exact ih]
  rw [hh]; simp [contextV2,WorkItem.bits,row,D4NodeQuery.request,D2.input,fld,num]; rfl

open DetDLP.D4RankWalker in
theorem solution (O : PrimitiveMachine) (o : Fin O.tapeCount) :
    (∀ (S m p guard l : ℕ) (f : Polynomial ℤ) (i : WorkItem) (j : ℕ), i.depth < Nat.clog 32 (4*m) →
      ask (contextV2 S m p guard l (AppendixD4.polynomialBits f)) i.bits j =
      D4NodeQuery.request i.G (fun v : Fin i.pins.length => (i.pins.get v).2)
        (D3Stopped.shift S i.depth) (D3Stopped.width S i.depth) i.pCurr l f j) ∧
    ∃ (A : PrimitiveMachine) (oa : Fin A.tapeCount) (K : ℕ),
      ∀ (S m p guard l : ℕ) (f : Polynomial ℤ) (root : WorkItem) (F : Wd → WalkerStep) (B u : ℕ) (τ σ : ℝ),
        let ctx := contextV2 S m p guard l (AppendixD4.polynomialBits f)
        let cs := runCallsV2 ctx root F B u
        let input := startV2 ctx root B u
        let output := tag ((unrollRankTreeV2 ctx root F).read B u)
        let N := 64^(Nat.clog 32 (4*m)); let L := maxLen input output cs
        0 ≤ τ → 0 ≤ σ → (∀ e ∈ cs, RunsWithin O o e.2.1 e.2.2 τ σ) →
        cs.length+1 ≤ 3*N ∧ RunsWithin A oa input output (polyBound K (L+N)*(τ+1)) (polyBound K (L+N)+K*(σ+1)) := by
  refine ⟨ask_eq,?_⟩
  obtain ⟨A,oa,k,hk,hm⟩ := m89_polyT_oracle_loop walkerStepV2 d4_rank_walker_v2_step_poly O o
  refine ⟨A,oa,12*(k+1)*(O.tapeCount+1)+k+2,?_⟩
  intro S m p guard l f root F B u τ σ ctx cs input output N L ht hs hor
  have hN : 1 ≤ N := Nat.one_le_pow _ _ (by decide)
  have hd : num ctx 0 = Nat.clog 32 (4*m) := context_depth ..
  have hp : potential ctx [root.bits] ≤ 64^num ctx 0 := by
    simp only [potential,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,unitCost]
    have h1 := cap_eq (num ctx 0 - num root.bits 0)
    have h2 : 64^(num ctx 0 - num root.bits 0) ≤ 64^num ctx 0 := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
    omega
  have ch := walk_chain ctx F (64^num ctx 0) [root.bits] [] B u (oneWord ctx) 0 hp
  have hr : cs.length+1 ≤ 3*N := by have hh : cs.length ≤ 2*64^num ctx 0 := ch.2; rw [hd] at hh; dsimp [N] at *; omega
  refine ⟨hr,?_⟩
  let s := min σ ((O.tapeCount:ℝ)*(L+2*τ+1))
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have loop : Loop O o τ s L (cs.length+1) input [] output := by
    apply chain_loop
    · rw [show input = startV2 ctx root B u from rfl, step_start]; exact ch.1
    · exact (le_max_left ..).trans (le_max_left ..)
    · exact (le_max_right ..).trans (le_max_left ..)
    · intro e he; have hl : span e ≤ L := (span_bound cs e he).trans (le_max_right ..)
      exact ⟨hl,tighten O o _ _ _ _ L ((suffixLe e.1 e.2.1).trans ((le_max_left ..).trans hl)) (hor e he)⟩
  have run := hm τ s ht hs0 (cs.length+1) L input output (by omega) loop
  have hi := inflate k O.tapeCount L N hk hN τ σ ht hs
  apply PolyTBridge.runsWithin_mono_local run _ hi.2
  apply le_trans _ hi.1
  apply mul_le_mul_of_nonneg_right _ (by unfold polyBound; positivity)
  exact_mod_cast hr
