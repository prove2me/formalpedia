-- Prove2me | solution 1 for DetDLP.d4b_outer_ranked_transcript
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T08:44:20.995798+00:00
-- url     : https://prove2.me/submissions/e8f103ab-e4f7-4d92-a89a-9ecdf694afc8

import Theorems.Thm_DetDLP_f9a1_b_add_and_readout_poly
import Theorems.Thm_DetDLP_f9a2_b_mul_poly
import Theorems.Thm_DetDLP_f9a3_b_unpack_term_poly
import Definitions.Def_DetDLP_D4BOuterInvariant
set_option autoImplicit false
open DetDLP DetDLP.D4BOuter DetDLP.D4Plan DetDLP.D4BEntry OAI.Algorithms.SubexponentialSAT.Computation
set_option autoImplicit false
namespace DetDLP.D4BOuter
open D4BEntry D4Plan D4Slice DetDLP_W1_Queries AppendixD4 ResidualScalarOracle Polynomial
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
variable {C c : ℕ} {x : Input C c}

private theorem binary (f : ℤ[X]) (q : ℕ) (hq : 0 < q)
    (bin : ∀ i < f.natDegree, f.coeff i = 0 ∨ f.coeff i = 1) :
    (polynomialBits f).map (fun b => if b then 1 else 0) = fCoeffs f q := by
  apply List.ext_getElem
  · simp [polynomialBits,fCoeffs]
  · intro i hi hj
    simp only [fCoeffs,List.length_ofFn] at hj
    simp only [fCoeffs,List.getElem_map,polynomialBits,List.getElem_ofFn]
    rcases bin i hj with h|h
    · simp [h]
    · have h2 : 1 < 2^q := one_lt_pow₀ (by decide) (by omega)
      simp [h,ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt h2]


private theorem flatCopies {α β : Type} (xs : List α) (n : ℕ) (v : β) :
    xs.flatMap (fun _ => List.replicate n v) = List.replicate (xs.length*n) v := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [List.flatMap_cons,ih,List.length_cons,Nat.succ_mul]; rw [Nat.add_comm,List.replicate_add]

theorem context_eq (P : Plan x) (buf : Bits) (hbuf : max (qprec P) x.l ≤ buf.length)
    (bin : ∀ i < P.f.natDegree, P.f.coeff i = 0 ∨ P.f.coeff i = 1) :
    context (input x) (header P) buf = ctxWord P := by
  have hq : 0 < qprec P := by have := x.hp; unfold qprec; omega
  have hp := (le_max_left ..).trans hbuf; have hl := (le_max_right ..).trans hbuf
  have hg : P.guard ≤ buf.length := (Nat.le_add_right ..).trans hp
  simp only [context,ctxWord,header,input,encodeTerminalBTNInstance,nval,field_zero,field_cons,decode_count]
  rw [modBits_eq hp,modBits_eq hg,clipped_eq hl,binary _ _ hq bin,listWord_eq]
  simp only [List.map_const',polynomialBits,List.length_ofFn,flatCopies,List.length_replicate]
  simp [residue,word]

theorem init_small (L : ℕ) (hx : Nat.clog 2 x.S < L) :
    step L (pair (input x) []) = dispatch (listWord [countWord 0]) 0 (input x) := by
  simp [step,nval,input,encodeTerminalBTNInstance,hx]

theorem init_large (L : ℕ) (hx : L ≤ Nat.clog 2 x.S) :
    step L (pair (input x) []) = headerCall (input x) [] := by
  simp [step,nval,input,encodeTerminalBTNInstance,not_lt.mpr hx]

theorem small_done (L : ℕ) : step L (pair (listWord [countWord 0]) (answer x)) = true :: answer x := by
  have hne : answer x ≠ [] := by cases h : (List.ofFn fun i : Fin x.l => ((Z x).coeff i.val : ZMod (2^x.p)).val) <;> simp [answer,h,encodeNatListBin,Encoding.encodeList]
  simp [step,nval,hne]

theorem read_eq (P : Plan x) (a : B P.f x.l (qprec P)) :
    readOut (ctxWord P) (enc P a) = true :: encodeNatListBin (List.ofFn fun j : Fin x.l =>
      word P.f x.l (qprec P) P.hf a j P.zero / 2^P.guard) := by
  simp only [readOut,ctxWord,field_cons,field_zero,listWord_eq]; congr 1
  exact f9a1_b_add_and_readout_poly.2.1 _ _ _ _ _ _ _ P.zero_val

theorem add_eq (P : Plan x) (a b : B P.f x.l (qprec P)) :
    add (ctxWord P) (enc P a) (enc P b) = enc P (a+b) := by
  simp only [add,ctxWord,field_cons,field_zero,listWord_eq]
  exact f9a1_b_add_and_readout_poly.1 ..

theorem enc_flat (P : Plan x) (a : B P.f x.l (qprec P)) :
    enc P a = encodeNatListBin (F9A2.flatten (word P.f x.l (qprec P) P.hf a)) := by
  unfold enc residue F9A2.flatten
  congr 1
  rw [List.ofFn_mul]
  apply congrArg List.flatten; apply congrArg List.ofFn; funext j; apply congrArg List.ofFn; funext i
  have h : (finProdFinEquiv.symm (finProdFinEquiv (j,i))) = (j,i) := finProdFinEquiv.symm_apply_apply _
  rw [show (⟨j.val * P.f.natDegree + i.val, _⟩ : Fin (x.l * P.f.natDegree)) = finProdFinEquiv (j,i) by apply Fin.ext; simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm],h]

theorem mul_eq (P : Plan x) (a b : B P.f x.l (qprec P)) :
    mul (ctxWord P) (enc P a) (enc P b) = enc P (a*b) := by
  simp only [mul,ctxWord,field_cons,field_zero,listWord_eq]
  rw [enc_flat,enc_flat,enc_flat]
  have hd := P.zero.isLt; have hl := x.hl; have hp := x.hp
  exact f9a2_b_mul_poly.1 _ _ _ _ (by omega) hl (by unfold qprec; omega) _ _

theorem spaces_eq (P : Plan x) (u : Fin P.N) :
    spaces (ctxWord P) (branch P u) = List.replicate (spacing P.f (P.R u)) true := by
  simp only [spaces,ctxWord,sides,branch,BipartiteMultigraph.encode,field_zero,field_cons,List.tail_replicate,flatCopies,List.length_ofFn,spacing,List.replicate_succ]

theorem width_eq (P : Plan x) (u : Fin P.N) : width (branch P u) = h P u := by
  simp [width,sides,nval,branch,BipartiteMultigraph.encode,h,digitWidth,P.edges]

theorem radix_eq (P : Plan x) (u : Fin P.N) : radix (ctxWord P) (branch P u) = J P u := by
  simp [radix,ctxWord,header,input,encodeTerminalBTNInstance,nval,width_eq,J,digits]


theorem digitCall_eq (P : Plan x) (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u))
    (acc ba : Bits) : digitCall (ctxWord P) acc u.val (branch P u) (vecWord a) ba =
      dispatch (listWord [countWord 3,ctxWord P,acc,countWord u.val,branch P u,vecWord a,ba]) 2
        (encodeBTNInstance (digitDesc P u a) (P.R u) x.b
          (precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) (spacing P.f (P.R u)*x.l)) := by
  unfold digitCall; rw [width_eq,spaces_eq]
  simp only [List.length_replicate,ctxWord,field_cons,field_zero,
    sides,branch,BipartiteMultigraph.encode,nval,decode_count,List.length_ofFn,P.edges,input,
    encodeTerminalBTNInstance,digitDesc,encodeBTNInstance,listWord_eq,precision,vecWord]

theorem term_eq (P : Plan x) (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u))
    (v : Fin (spacing P.f (P.R u)*x.l) → ℕ) :
    term (ctxWord P) (branch P u) (List.ofFn fun z => (a z).val) (encodeNatListBin (List.ofFn v)) =
      enc P (unpackTerm P.f x.l (qprec P) (P.R u) (h P u) a v) := by
  have hd := P.zero.isLt
  have hpow : 0 < (2:ℕ)^qprec P := by positivity
  have hlen : qprec P ≤ ((2:ℕ)^qprec P).bits.length := by
    rw [Nat.size_eq_bits_len]; exact (Nat.lt_size.mpr (le_refl _)).le
  have hm (r : ℕ) : (if r < qprec P then modBits r ((2^qprec P : ℕ).bits) else (0:ℕ).bits) =
      ((2^r) % 2^qprec P : ℕ).bits := by
    by_cases hr : r < qprec P
    · rw [if_pos hr,modBits_eq (hr.le.trans hlen),Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hr)]
    · rw [if_neg hr,Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 (Nat.le_of_not_gt hr))]
  unfold term; rw [width_eq,spaces_eq]; simp only [ctxWord,field_cons,field_zero,header,input,
    encodeTerminalBTNInstance,nval,decode_count,List.sum_ofFn,listWord_eq]
  rw [hm]
  exact f9a3_b_unpack_term_poly.2.1 _ _ _ _ (by omega) _ _ _ _ _

theorem afterHeader_more (P : Plan x) (buf : Bits) (hb : buf.length < max (qprec P) x.l) :
    afterHeader (input x) (header P) buf = headerCall (input x) (true :: (buf ++ buf)) := by
  unfold afterHeader
  rw [if_pos]; simp only [nval,header,input,encodeTerminalBTNInstance,field_cons,field_zero,decode_count]; exact hb

theorem afterHeader_zero (P : Plan x) (buf : Bits) (hbuf : max (qprec P) x.l ≤ buf.length)
    (bin : ∀ i < P.f.natDegree, P.f.coeff i = 0 ∨ P.f.coeff i = 1) (hz : P.N=0) :
    afterHeader (input x) (header P) buf = true :: answer x := by
  unfold afterHeader
  rw [context_eq P buf hbuf bin]
  simp only [header,input,encodeTerminalBTNInstance,nval,field_cons,field_zero,decode_count]
  rw [if_neg (not_lt.mpr hbuf),if_pos hz]
  have acc : field 7 (ctxWord P) = enc P 0 := by simp [ctxWord]
  rw [acc,read_eq,P.correct]
  have hi : IsEmpty (Fin P.N) := ⟨fun i => by have := i.isLt; omega⟩
  simp

end DetDLP.D4BOuter

set_option autoImplicit false
namespace DetDLP.D4BOuter
open D4BEntry D4Plan


private def bumped (ds : List ℕ) (i : ℕ) := (List.range ds.length).map fun k =>
  if k < i then 0 else if k = i then ds.getD k 0 + 1 else ds.getD k 0

private def number (J : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => v + J * number J vs

private theorem bumped_zero (v : ℕ) (vs : List ℕ) : bumped (v::vs) 0 = (v+1)::vs := by
  apply List.ext_getElem
  · simp [bumped]
  · intro k hk hl
    cases k with
    | zero => simp [bumped]
    | succ k => simp [bumped,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hl : k < vs.length)]

private theorem bumped_succ (v : ℕ) (vs : List ℕ) (i : ℕ) : bumped (v::vs) (i+1) = 0 :: bumped vs i := by
  apply List.ext_getElem
  · simp [bumped]
  · intro k hk hl
    cases k with
    | zero => simp [bumped]
    | succ k => simp [bumped,List.getD_eq_getElem?_getD]

private theorem incr (J : ℕ) (vs : List ℕ) (hvs : ∀ v ∈ vs, v < J) :
    let i := nextAt vs J
    (i < vs.length → number J (bumped vs i) = number J vs + 1 ∧ ∀ v ∈ bumped vs i, v < J) ∧
    (vs.length ≤ i → number J vs + 1 = J^vs.length) := by
  induction vs with
  | nil => simp [nextAt,number]
  | cons v vs ih =>
    have hv := hvs v (by simp)
    have ht : ∀ z ∈ vs, z < J := fun z hz => hvs z (by simp [hz])
    obtain ⟨ih₁,ih₂⟩ := ih ht
    by_cases hi : v+1 < J
    · simp only [nextAt,List.map_cons,decide_eq_true hi,List.idxOf_cons_self,List.length_cons,
        Nat.zero_lt_succ,not_le.mpr (Nat.zero_lt_succ _),false_implies,true_implies,and_true,bumped_zero,number]
      exact ⟨by omega,by simpa using And.intro hi ht⟩
    · have hh : nextAt (v::vs) J = nextAt vs J+1 := by simp [nextAt,hi,List.idxOf_cons_ne]
      simp only [hh,List.length_cons,Nat.succ_lt_succ_iff,Nat.succ_le_succ_iff,bumped_succ,number,zero_add]
      have hJ : J = v+1 := by omega
      constructor
      · intro hi'; obtain ⟨eq,hs⟩ := ih₁ hi'
        exact ⟨by rw [eq,Nat.mul_succ]; omega,by simpa using And.intro (by omega : 0 < J) hs⟩
      · intro hi'; rw [pow_succ',←ih₂ hi',Nat.mul_succ]; omega

private theorem number_rank {J n : ℕ} (a : Fin n → Fin J) : number J (digitsOf a) = (finFunctionFinEquiv a).val := by
  rw [finFunctionFinEquiv_apply]; induction n with
  | zero => simp [digitsOf,number]
  | succ n ih =>
    rw [Fin.sum_univ_succ]; simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ',←Nat.mul_assoc]
    unfold digitsOf; rw [List.ofFn_succ]; simp only [number]; congr 1
    rw [show number J (List.ofFn fun i : Fin n => (a i.succ).val) = _ from ih (fun i => a i.succ),Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring

/-- The implemented cursor either advances by exactly one rank or is already at the last rank. -/
theorem cursor_exact {n J : ℕ} (a : Fin n → Fin J) :
    let ds := digitsOf a; let i := nextAt ds J; let r := (finFunctionFinEquiv a).val
    (i < n → ∃ b : Fin n → Fin J, advanceVec ds i = encodeNatListBin (digitsOf b) ∧
      (finFunctionFinEquiv b).val = r+1) ∧ (n ≤ i → r+1 = J^n) := by
  intro ds i r
  have hlen : ds.length = n := by simp [ds,digitsOf]
  have hs : ∀ z ∈ ds,z < J := by simp [ds,digitsOf]
  obtain ⟨hn,he⟩ := incr J ds hs
  constructor
  · intro hi; obtain ⟨hr,hb⟩ := hn (hlen ▸ hi)
    have hlen' : (bumped ds i).length = n := by simp [bumped,hlen]
    let b (k : Fin n) : Fin J := ⟨(bumped ds i)[k.val]'(lt_of_lt_of_eq k.isLt hlen'.symm),hb _ (List.getElem_mem _)⟩
    have heq : bumped ds i = digitsOf b := by apply List.ext_getElem <;> simp [digitsOf,b,hlen']
    refine ⟨b,congrArg encodeNatListBin heq,?_⟩
    rw [←number_rank,←heq]; exact hr.trans (congrArg (·+1) (number_rank a))
  · intro h; rw [show r = number J ds from (number_rank a).symm]; simpa only [hlen] using he (hlen ▸ h)

end DetDLP.D4BOuter

set_option autoImplicit false
namespace DetDLP.D4BOuter
open D4BEntry D4Plan D4Slice DetDLP_W1_Queries AppendixD4 ResidualScalarOracle Polynomial
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
variable {C c : ℕ} {x : Input C c}
noncomputable section
@[simp] theorem prefix_zero {R : Type} [AddCommMonoid R] {n : ℕ} (f : Fin n → R) : prefixSum f 0 = 0 := by simp [prefixSum]
theorem prefix_succ {R : Type} [AddCommMonoid R] {n : ℕ} (f : Fin n → R) (k : Fin n) : prefixSum f (k.val+1) = prefixSum f k.val + f k := by
  classical
  have eq (i : Fin n) : (if i.val < k.val+1 then f i else 0) = (if i.val < k.val then f i else 0) + (if i=k then f i else 0) := by
    by_cases h : i=k
    · simp [h]
    · have hn : i.val ≠ k.val := fun t => h (Fin.ext t)
      rw [if_neg h,add_zero]; congr 1; exact propext (by omega)
  simp only [prefixSum,eq,Finset.sum_add_distrib]; simp
theorem prefix_all {R : Type} [AddCommMonoid R] {n : ℕ} (f : Fin n → R) : prefixSum f n = ∑ i,f i := by simp [prefixSum]
@[simp] theorem inside_zero (P : Plan x) (v : DigitsData P) (u : Fin P.N) : inside P v u 0 = 0 := prefix_zero _
theorem inside_succ (P : Plan x) (v : DigitsData P) (u : Fin P.N) (a : Vect P u) :
    inside P v u ((finFunctionFinEquiv a).val+1) = inside P v u (finFunctionFinEquiv a).val + summand P v u a := by
  simpa only [inside, Equiv.symm_apply_apply] using prefix_succ (fun i => summand P v u (finFunctionFinEquiv.symm i)) (finFunctionFinEquiv a)
theorem inside_all (P : Plan x) (v : DigitsData P) (u : Fin P.N) :
    inside P v u (J P u^(P.R u).nV) = unpack P.f x.l (qprec P) (P.R u) (h P u) (J P u) (v u) := by
  rw [inside,prefix_all,←f9a3_b_unpack_term_poly.1]; exact Fintype.sum_equiv finFunctionFinEquiv.symm _ _ (fun _ => rfl)
@[simp] theorem outside_zero (P : Plan x) : outside P 0 = 0 := prefix_zero _
theorem outside_succ (P : Plan x) (u : Fin P.N) : outside P (u.val+1) = outside P u.val + P.w u * BTNContract (P.R u) (P.V u) := prefix_succ _ _
theorem read_end (P : Plan x) : readOut (ctxWord P) (enc P (outside P P.N)) = true :: answer x := by
  rw [read_eq,P.correct,outside,prefix_all]

theorem header_yes (P : Plan x) (buf : Bits) (hb : max (qprec P) x.l ≤ buf.length)
    (bin : ∀ i < P.f.natDegree, P.f.coeff i = 0 ∨ P.f.coeff i = 1) (hn : 0<P.N) :
    afterHeader (input x) (header P) buf = branchCall (ctxWord P) (enc P 0) 0 := by
  unfold afterHeader; rw [context_eq P buf hb bin]
  simp only [header,input,encodeTerminalBTNInstance,nval,field_cons,field_zero,decode_count]; rw [if_neg (not_lt.mpr hb),if_neg (Nat.ne_of_gt hn)]
  simp [ctxWord]
theorem step_hd (P : Plan x) (L : ℕ) (buf : Bits) :
    step L (pair (listWord [countWord 1,input x,buf]) (header P)) = afterHeader (input x) (header P) buf := by
  simp [step,nval,show header P ≠ [] by simp [header,Encoding.encodeList]]
theorem br_call (P : Plan x) (u : Fin P.N) (s : Res P) :
    branchCall (ctxWord P) (enc P s) u.val = dispatch (brState P u s) 1 (rankQuery x (u.val+1)) := by simp [branchCall,brState,ctxWord,rank,rankQuery]
theorem dg_call (P : Plan x) (u : Fin P.N) (a : Vect P u) (s t : Res P) :
    digitCall (ctxWord P) (enc P s) u.val (branch P u) (vecWord a) (enc P t) = dispatch (dgState P u a s t) 2 (dgQuery P u a) := digitCall_eq ..
theorem step_br (P : Plan x) (L : ℕ) (u : Fin P.N) (s : Res P) :
    step L (pair (brState P u s) (branch P u)) = dispatch (dgState P u (zvec P u) s 0) 2 (dgQuery P u (zvec P u)) := by
  rw [←dg_call]; have hn : branch P u ≠ [] := by simp [branch,Encoding.encodeList]
  simp [brState,step,nval,hn,afterBranch]; congr 1
  · simp [sides,branch,BipartiteMultigraph.encode,vecWord,zvec]
  · simp [ctxWord]

theorem step_dg (P : Plan x) (L : ℕ) (v : DigitsData P) (u : Fin P.N) (a : Vect P u) (s t : Res P) :
    let ds := digitsOf a; let i := nextAt ds (J P u); let t' := t + summand P v u a
    let s' := s + P.w u * t'
    step L (pair (dgState P u a s t) (dgAns P v u a)) =
      if i < (P.R u).nV then digitCall (ctxWord P) (enc P s) u.val (branch P u) (advanceVec ds i) (enc P t')
      else if u.val+1 < P.N then branchCall (ctxWord P) (enc P s') (u.val+1) else readOut (ctxWord P) (enc P s') := by
  have hne : dgAns P v u a ≠ [] := by unfold dgAns encodeNatListBin; cases List.ofFn (v u a) <;> simp [Encoding.encodeList]
  simp only [step,pair_first,pair_more,hne,if_false]
  simp only [if_false,dgState,listWord_eq,nval,field_zero,decode_count,show (3:ℕ)≠0 by decide,show (3:ℕ)≠1 by decide,show (3:ℕ)≠2 by decide,afterDigit,field_cons,vecWord,w5_M6Sort.decode_encode,radix_eq,List.length_ofFn,dgAns,term_eq,add_eq,digitsOf,summand]
  have hw : field 1 (branch P u) = enc P (P.w u) := by simp [branch]
  have hN : nval 0 (field 1 (ctxWord P)) = P.N := by simp [nval,ctxWord,header]
  rw [hw,mul_eq,add_eq,show Groundwork.PolyT.bval (field 0 (field 1 (ctxWord P))) = P.N from hN]
  rfl
end
end DetDLP.D4BOuter

set_option autoImplicit false
namespace DetDLP.D4BOuter
open D4BEntry D4Plan D4Slice DetDLP_W1_Queries AppendixD4 ResidualScalarOracle
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
variable {C c : ℕ} {x : Input C c}
noncomputable section
private theorem emitCall {L H r j : ℕ} {O : PrimitiveMachine} {o : Fin O.tapeCount} {τ σ : ℝ} {st ans st' q y out : Bits}
    (e : step L (pair st ans) = dispatch st' j q) (hs : (pair st ans).length ≤ H)
    (hc : Call O o τ σ H st' j q y) (ht : TraceAt L O o τ σ H out r st' y) :
    TraceAt L O o τ σ H out (r+1) st ans := by
  right; refine ⟨st',tagWord j q,y,e,hs,hc.queryCap,?_,hc.run,ht⟩
  have h := hc.pairCap; unfold pair at h; simp only [List.length_append] at h; omega
private theorem halt {L H r : ℕ} {O : PrimitiveMachine} {o : Fin O.tapeCount} {τ σ : ℝ} {st ans out : Bits}
    (hr : 0 < r) (e : step L (pair st ans) = true :: out) (hs : (pair st ans).length ≤ H) (ho : out.length ≤ H) :
    TraceAt L O o τ σ H out r st ans := by cases r with | zero => omega | succ r => exact Or.inl ⟨e,hs,ho⟩

private theorem digitRuns (P : Plan x) (v : DigitsData P) (L : ℕ) {O o τ σ H B}
    (G : BranchOracle P v O o τ σ H B) (u : Fin P.N) (tail : ℕ)
    (next : ∀ h' : u.val+1<P.N, TraceAt L O o τ σ H (answer x) tail (brState P ⟨u.val+1,h'⟩ (outside P (u.val+1))) (branch P ⟨u.val+1,h'⟩))
    (a : Vect P u) (r : ℕ) (hr : J P u^(P.R u).nV - (finFunctionFinEquiv a).val + tail ≤ r) :
    TraceAt L O o τ σ H (answer x) r (dgState P u a (outside P u.val) (inside P v u (finFunctionFinEquiv a).val)) (dgAns P v u a) := by
  induction r generalizing a with
  | zero => have hh := (finFunctionFinEquiv a).isLt; omega
  | succ r ih =>
    let s := outside P u.val; let t := inside P v u (finFunctionFinEquiv a).val
    have hstep := step_dg P L v u a s t
    dsimp only at hstep
    have hcur := cursor_exact a
    have hb := (G.dg u a s t).pairCap
    by_cases hi : nextAt (digitsOf a) (J P u) < (P.R u).nV
    · obtain ⟨b,advance,rank⟩ := hcur.1 hi
      rw [if_pos hi,advance] at hstep
      change step L (pair _ _) = digitCall _ _ _ _ (vecWord b) _ at hstep
      rw [dg_call] at hstep
      have hba : t + summand P v u a = inside P v u (finFunctionFinEquiv b).val := by rw [rank,inside_succ]
      rw [hba] at hstep
      exact emitCall hstep hb (G.dg ..) (ih b (by have := (finFunctionFinEquiv a).isLt; omega))
    · rw [if_neg hi] at hstep
      have last := hcur.2 (Nat.le_of_not_gt hi)
      have hx : t + summand P v u a = BTNContract (P.R u) (P.V u) := by rw [←inside_succ,last,inside_all,G.exactValue]
      rw [hx,show s + P.w u * BTNContract (P.R u) (P.V u) = outside P (u.val+1) from (outside_succ P u).symm] at hstep
      by_cases hn : u.val+1 < P.N
      · rw [if_pos hn] at hstep
        have e := hstep.trans (br_call P ⟨u.val+1,hn⟩ (outside P (u.val+1)))
        have mono (k : ℕ) : ∀ st ans, TraceAt L O o τ σ H (answer x) k st ans → ∀ j, k ≤ j → TraceAt L O o τ σ H (answer x) j st ans := by
          induction k with
          | zero => intro st ans h; exact False.elim h
          | succ k ih => intro st ans h j hj; cases j with
                         | zero => omega
                         | succ j => rcases h with h|⟨st',q,y,e,hs,hq,hy,ho,ht⟩; exact Or.inl h; exact Or.inr ⟨st',q,y,e,hs,hq,hy,ho,ih _ _ ht j (by omega)⟩
        exact emitCall e hb (G.br ..) (mono tail _ _ (next hn) r (by have := (finFunctionFinEquiv a).isLt; omega))
      · have eq : u.val+1 = P.N := by have := u.isLt; omega
        rw [if_neg hn,eq,read_end] at hstep
        exact halt (Nat.succ_pos _) hstep hb G.output

theorem branchRuns (P : Plan x) (v : DigitsData P) (L : ℕ) {O o τ σ H B}
    (G : BranchOracle P v O o τ σ H B) (u : Fin P.N) :
    TraceAt L O o τ σ H (answer x) ((P.N-u.val)*(B+1)) (brState P u (outside P u.val)) (branch P u) := by
  let n := P.N-u.val
  have main (k : ℕ) : ∀ (u : Fin P.N), P.N-u.val=k → TraceAt L O o τ σ H (answer x) (k*(B+1)) (brState P u (outside P u.val)) (branch P u) := by
    intro u hk; induction k generalizing u with
    | zero => have := u.isLt; omega
    | succ k ih =>
      let a := zvec P u
      have hz : (finFunctionFinEquiv a).val = 0 := by simp [finFunctionFinEquiv_apply,a,zvec]
      have ht := digitRuns P v L G u (k*(B+1)) (fun h => ih ⟨u.val+1,h⟩ (by simp; omega)) a (k*(B+1)+B) (by rw [hz,Nat.sub_zero]; have := G.count u; omega)
      rw [hz,inside_zero] at ht
      rw [Nat.succ_mul,←Nat.add_assoc]
      exact emitCall (step_br P L u _) (G.br ..).pairCap (G.dg ..) ht
  exact main _ u rfl


theorem largeRuns (P : Plan x) (v : DigitsData P) (L : ℕ) {O o τ σ H B}
    (G : BranchOracle P v O o τ σ H B) (hL : L ≤ Nat.clog 2 x.S)
    (bin : ∀ i < P.f.natDegree, P.f.coeff i = 0 ∨ P.f.coeff i = 1)
    (h0 : (pair (input x) []).length ≤ H)
    (hd : ∀ buf : Bits, buf.length ≤ 2 * need P + 1 → Call O o τ σ H (hdState x buf) 1 (rankQuery x 0) (header P)) :
    ∃ r, 1 ≤ r ∧ r ≤ need P+3+P.N*(B+1) ∧ TraceAt L O o τ σ H (answer x) r (input x) [] := by
  have start (buf : Bits) : headerCall (input x) buf = dispatch (hdState x buf) 1 (rankQuery x 0) := by simp [hdState,headerCall,rankQuery,rank]
  have main (k : ℕ) : ∀ (buf : Bits), need P - buf.length ≤ k → buf.length ≤ 2*need P+1 →
      ∃ r, r ≤ k+1+P.N*(B+1) ∧ TraceAt L O o τ σ H (answer x) r (hdState x buf) (header P) := by
    intro buf hk hb; induction k generalizing buf with
    | zero =>
      have hbig : need P ≤ buf.length := by omega
      by_cases hN : P.N=0
      · exact ⟨1,by omega,halt (by decide) ((step_hd P L buf).trans (afterHeader_zero P buf hbig bin hN)) (hd buf hb).pairCap G.output⟩
      · let u : Fin P.N := ⟨0,by omega⟩
        have e := ((step_hd P L buf).trans (header_yes P buf hbig bin (by omega))).trans (br_call P u 0)
        have ht := branchRuns P v L G u
        simp only [u,Nat.sub_zero,outside_zero] at ht
        exact ⟨_,by omega,emitCall e (hd buf hb).pairCap (G.br ..) ht⟩
    | succ k ih =>
      by_cases more : buf.length < need P
      · let newbuf := true :: (buf++buf)
        have hn : newbuf.length = buf.length+buf.length+1 := by simp [newbuf]
        have hb' : newbuf.length ≤ 2*need P+1 := by omega
        obtain ⟨r,hr,ht⟩ := ih newbuf (by omega) hb'
        have e := ((step_hd P L buf).trans (afterHeader_more P buf more)).trans (start newbuf)
        exact ⟨_,by omega,emitCall e (hd buf hb).pairCap (hd newbuf hb') ht⟩
      · obtain ⟨r,hr,ht⟩ := ih buf (by omega) hb
        exact ⟨r,by omega,ht⟩
  obtain ⟨r,hr,ht⟩ := main (need P) [] (by simp) (by simp)
  exact ⟨r+1,by omega,by omega,emitCall ((init_large L hL).trans (start [])) h0 (hd [] (by simp)) ht⟩

theorem smallRuns (L : ℕ) {O o τ σ H} (hL : Nat.clog 2 x.S < L) (h0 : (pair (input x) []).length ≤ H)
    (h : Call O o τ σ H (listWord [countWord 0]) 0 (input x) (answer x)) : TraceAt L O o τ σ H (answer x) 2 (input x) [] := by
  refine emitCall (init_small L hL) h0 h (halt (by decide) (small_done L) h.pairCap ?_)
  have := h.pairCap; unfold pair at this; simp only [List.length_append] at this; omega
end
end DetDLP.D4BOuter

theorem solution {C c : ℕ} {x : Input C c} (P : Plan x) (v : DigitsData P) (L : ℕ) {O : PrimitiveMachine} {o : Fin O.tapeCount} {τ σ : ℝ} {H B : ℕ}
    (G : BranchOracle P v O o τ σ H B) (hL : L ≤ Nat.clog 2 x.S)
    (bin : ∀ i < P.f.natDegree, P.f.coeff i = 0 ∨ P.f.coeff i = 1)
    (h0 : (pair (input x) []).length ≤ H)
    (hd : ∀ buf : D4BOuter.Bits, buf.length ≤ 2 * need P + 1 → Call O o τ σ H (hdState x buf) 1 (rankQuery x 0) (header P)) :
    ∃ r, 1 ≤ r ∧ r ≤ need P+3+P.N*(B+1) ∧ TraceAt L O o τ σ H (answer x) r (input x) [] := largeRuns P v L G hL bin h0 hd
