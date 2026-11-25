-- Prove2me | solution 1 for DetDLP.m89_s1_ec_plan_prepare
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:20:05.239828+00:00
-- url     : https://prove2.me/submissions/f60ef17b-4b3a-4697-928f-0f18f7e1920e

import Theorems.Thm_DetDLP_hasse_ec_point_count_bound
import Definitions.Def_DetDLP_S8B_Descent
import Definitions.Def_DetDLP_S8B_Parameters
import Definitions.Def_DetDLP_M89_S1_Plans
import Definitions.Def_DetDLP_S8F_Controller
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Theorems.Thm_DetDLP_stage1_complexity_dominance
set_option autoImplicit false
namespace DetDLP.S8F
open S8B
open M89S1
theorem threshold_le {p m g : ℕ} (hm : 2 ≤ m) (h64 : 64 ≤ g) (h4096 : 4096*m ≤ g-1) :
    hashThreshold p (g-1) m g ≤ p := by
  let n := g-1
  have hn : (63:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 63 ≤ n by dsimp [n]; omega)
  have hn1 : (g:ℝ) = n+1 := by exact_mod_cast (show g=n+1 by dsimp [n]; omega)
  have hp : 0 < (n:ℝ) := by linarith
  have he : (1:ℝ)/(m:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm)
  have h16 : (16*(g:ℝ))^((1:ℝ)/(m:ℝ)) ≤ (n:ℝ) := by
    calc
      _ ≤ (16*(g:ℝ))^((1:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ ≤ ((n:ℝ)^2)^((1:ℝ)/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [mul_nonneg (by linarith : 0 ≤ (n:ℝ)-16) hp.le]) (by norm_num)
      _ = _ := by rw [← Real.rpow_natCast_mul hp.le]; norm_num
  have hq : qStar m g ≤ n := max_le h4096 (Nat.ceil_le.mpr h16)
  change Nat.ceil ((p:ℝ)*(qStar m g:ℝ)/(n:ℝ)) ≤ p
  apply Nat.ceil_le.mpr
  exact (div_le_iff₀ hp).mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by positivity))


noncomputable abbrev fpM (p : ℕ) := blockCount (bitLen p)
noncomputable abbrev order {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) := @Fintype.card _ (ecPointFintype E)
variable {p : ℕ} [hp : Fact p.Prime] (E : WeierstrassCurve (ZMod p))
noncomputable abbrev ecT := hashThreshold p (order E-1) (fpM p) (order E)
noncomputable def ecMom : Fin 4 → W → ℕ :=
  letI := ecPointFintype E
  let D := fun s : ECSeed p (fpM p) => ecFactorBlock E (ecT E) s
  moment ecBits (fun s => productSize (D s)) (fun s => collisionEnergyAdd (D s))
noncomputable def ecNext :=
  fromMoments (p^fpM p) (((order E-1)*ecT E)^fpM p) (order E) (ecMom E)

theorem ec_law (h64 : 64 ≤ order E) (h4096 : 4096*fpM p ≤ order E-1) :
    ∃ s : ECSeed p (fpM p), m89_ec_plan_ok E (some (ecT E,s)) ∧
      List.ofFn (ecBits s) = path (ecNext E) (fpM p*4*bitLen p) := by
  letI := ecPointFintype E
  have hg : 0 < order E-1 := by omega
  have pp := hp.out.pos
  have hn : 0 < p-1 := by have := hp.out.two_le; omega
  have hm : 2 ≤ fpM p := le_max_left ..
  have hq : 0 < qStar (fpM p) (order E) := lt_of_lt_of_le (by omega : 0 < 4096*fpM p) (le_max_left ..)
  have ht : 0 < ecT E := by unfold ecT hashThreshold; apply Nat.ceil_pos.mpr; positivity
  let _ : Nonempty (ECSeed p (fpM p)) := ⟨fun _ _ => (⟨0,hn⟩,⟨0,pp⟩)⟩
  have hμ : (qBlk p (order E-1) (ecT E))^(fpM p) = (↑(((order E-1)*ecT E)^fpM p) : ℝ)/↑(p^fpM p) := by simp [qBlk,div_pow,mul_pow]
  obtain ⟨s,hs,hw⟩ := path_winner (@ecBits p (fpM p)) (ecCost E (m:=fpM p)) (ecNext E) (by
    intro w _
    let D := fun s : ECSeed p (fpM p) => ecFactorBlock E (ecT E) s
    have HH := fromMoments_spec (@ecBits p (fpM p)) w (fun s => productSize (D s)) (fun s => collisionEnergyAdd (D s))
      (order E) (p^fpM p) (((order E-1)*ecT E)^fpM p) (by positivity) (by positivity)
    simpa only [ecNext,ecMom,ecCost,collisionPotentialAdd,←hμ,ecT,D,fpM] using HH)
  exact ⟨s,⟨h64,h4096,rfl,hs⟩,hw⟩
theorem order_le (h3 : 3 < p) [E.IsElliptic] : order E ≤ 4*p := by
  have h := (abs_le.mp (hasse_ec_point_count_bound p h3 E)).2
  change (order E : ℝ) - ((p:ℝ)+1) ≤ _ at h
  have h1 : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p)
  exact_mod_cast (show (order E:ℝ) ≤ 4*(p:ℝ) by nlinarith [sq_nonneg (Real.sqrt (p:ℝ)-1)])
end DetDLP.S8F
set_option autoImplicit false
namespace DetDLP.S8F
open S8B
open M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem block_le (b : ℕ) : blockCount b ≤ b+2 := by
  apply max_le (by omega) (Nat.ceil_le.mpr ?_)
  have u : Nat.clog 2 (b+2) ≤ b+2 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (Nat.lt_pow_self (by decide)).le
  have v : 1 ≤ Nat.clog 2 (b+2) := Nat.clog_pos (by decide) (by omega)
  exact (Real.rpow_le_self_of_one_le (by exact_mod_cast v) (by norm_num)).trans (by exact_mod_cast u)


theorem size_eq (p : ℕ) : (p-1).size = bitLen p := by
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
@[simp] theorem stage_eq (p g : ℕ) : stageT p g = hashThreshold p (g-1) (fpM p) g := by simp [stageT,threshold_eq,show 0 < fpM p from lt_of_lt_of_le (by decide : 0<2) (le_max_left ..)]
@[simp] theorem seedLen_eq (p : ℕ) : seedLen p = fpM p * 4 * bitLen p := by simp [seedLen,blocks_eq,size_eq,fpM]
@[simp] theorem bval_count (n : ℕ) : bval (countWord n) = n := by cases n with | zero => rfl | succ n => simp [countWord,bval_bits]
@[simp] theorem fields_nat (l : List ℕ) : fields (encodeNatListBin l) = l.map countWord := by
  have h : encodeNatListBin l = enc (l.map countWord) := by induction l with | nil => rfl | cons a l ih => change true :: (_ ++ encodeNatListBin l) = true :: (_ ++ enc (l.map countWord)); rw [ih]; rfl
  rw [h]; exact fields_encode _
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

@[simp] theorem prime_curve {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) : prime (encodeCurveInput p E) = p := by simp [prime,encodeCurveInput]
theorem step_init (t : Bool) (raw : Word) : step t (pair raw []) = orderAsk t raw := by unfold step; rw [parseInit]; rfl
theorem step_order (t : Bool) (raw : Word) (g : ℕ) : step t (pair (enc [raw]) (encodeNatListBin [g])) = init raw (curve t raw) (prime (curve t raw)) g := by unfold step; rw [parseAns]; simp [outerStep,resume,enc]
theorem step_ans (t : Bool) (raw w : Word) (g : ℕ) (vs : List Word) (n : ℕ) :
    step t (pair (enc (raw::countWord g::w::vs)) (encodeNatListBin [n])) = driver raw (curve t raw) (prime (curve t raw)) g w (vs++[countWord n]) := by
  unfold step; rw [parseAns]; simp [outerStep,resume,enc]
end DetDLP.S8F
set_option autoImplicit false
namespace DetDLP.S8F
open S8B M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem moment_bound {p : ℕ} [h : Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (h3 : 3 < p) (j : Fin 4) (w : W) :
    ecMom E j w ≤ (4*p)^(6*fpM p+1) := by
  classical
  letI := ecPointFintype E
  let P := 4*p
  let m := fpM p
  let D := fun s : ECSeed p m => ecFactorBlock E (ecT E) s
  have pp := h.out.pos
  have hp : 0 < P := by dsimp [P]; positivity
  have card : Fintype.card E.toAffine.Point ≤ P := order_le E h3
  have size (s : ECSeed p m) : productSize (D s) ≤ P^m := by
    simpa [productSize] using Finset.prod_le_prod' (s:=Finset.univ) (g:=fun _ : Fin m => P) (fun i _ => ((D s i).card_le_univ.trans card))
  have rep (s : ECSeed p m) (g : E.toAffine.Point) : repCountAdd (D s) g ≤ P^m := by
    unfold repCountAdd
    apply (Finset.card_le_univ _).trans; simpa using Nat.pow_le_pow_left card m
  have big (s : ECSeed p m) : collisionEnergyAdd (D s) ≤ P^(2*m+1) := by
    unfold collisionEnergyAdd
    calc
      _ ≤ ∑ _ : E.toAffine.Point, (P^m)^2 := Finset.sum_le_sum (fun g _ => Nat.pow_le_pow_left (rep s g) _)
      _ = Fintype.card E.toAffine.Point * (P^m)^2 := by simp
      _ ≤ P*(P^m)^2 := Nat.mul_le_mul_right _ card
      _ = P^(2*m+1) := by rw [pow_succ P (2*m), Nat.mul_comm 2 m,pow_mul]; ring
  have seeds : Fintype.card (ECSeed p m) ≤ P^(4*m) := by
    have ha : (p-1)*p ≤ P^2 := by dsimp [P]; rw [pow_two]; apply Nat.mul_le_mul <;> omega
    simp only [ECSeed,Fintype.card_fun,Fintype.card_bool,Fintype.card_prod,Fintype.card_fin]
    apply (Nat.pow_le_pow_left (Nat.pow_le_pow_left ha 2) m).trans
    rw [←pow_mul,←pow_mul,show 2*(2*m)=4*m by omega]
  change (∑ s ∈ slice ecBits w, (if j=0 then 1 else if j=1 then productSize (D s) else if j=2 then (productSize (D s))^2 else collisionEnergyAdd (D s))) ≤ _
  calc
    _ ≤ ∑ _ ∈ slice (@ecBits p m) w, P^(2*m+1) := by
      apply Finset.sum_le_sum; intro s _; split_ifs
      · exact Nat.one_le_pow _ _ hp
      · exact (size s).trans (Nat.pow_le_pow_right hp (by omega))
      · apply (Nat.pow_le_pow_left (size s) 2).trans
        rw [←pow_mul]; exact Nat.pow_le_pow_right hp (by omega)
      · exact big s
    _ ≤ P^(4*m)*P^(2*m+1) := by simp only [Finset.sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ ((Finset.card_le_univ _).trans seeds)
    _ = _ := by rw [←pow_add]; congr 1; dsimp [m]; omega

theorem cw_size (n : ℕ) : (countWord n).length ≤ n.size+1 := by by_cases h:n=0 <;> simp [countWord,h,Nat.size_eq_bits_len]

def cap (b : ℕ) := 10000*(b+3)^2

theorem field_bound {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (h3 : 3 < p) (j : Fin 4) (w : W) :
    (countWord (ecMom E j w)).length ≤ (bitLen p+2)*(6*fpM p+1)+2 := by
  let e := 6*fpM p+1
  have hbase : 4*p ≤ 2^(bitLen p+2) := by rw [pow_add]; have := Nat.le_pow_clog (by decide : 1<2) p; change p ≤ 2^(bitLen p) at this; omega
  have ht := (moment_bound E h3 j w).trans (Nat.pow_le_pow_left hbase e)
  rw [←pow_mul] at ht
  have hs := Nat.size_le.mpr (ht.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self _)))
  exact (cw_size _).trans (by dsimp [e] at hs; omega)
def unitCap (b : ℕ) := 100*(b+3)^2

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

theorem atomic_bounds {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (h3 : 3 < p) :
    let b := bitLen p; let z := unitCap b
    fpM p * 4 * b + 1 ≤ z ∧ b+8 ≤ z ∧ (∀ i w, (countWord (ecMom E i w)).length ≤ z) := by
  intro b z
  have hm := block_le b; change fpM p ≤ b+2 at hm
  have hprod := Nat.mul_le_mul_right b hm
  constructor
  · dsimp [z,unitCap]; nlinarith
  constructor
  · dsimp [z,unitCap]; nlinarith
  · intro i w; apply (field_bound E h3 i w).trans; change (b+2)*(6*fpM p+1)+2 ≤ _; dsimp [z,unitCap]; nlinarith

theorem gwidth {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (h3 : 3 < p) : (countWord (order E)).length ≤ bitLen p+3 := by
  have hh := order_le E h3
  have hpow : p ≤ 2^(bitLen p) := Nat.le_pow_clog (by decide) p
  have hlim : order E < 2^(bitLen p+3) := by rw [pow_add]; omega
  have hpos : order E ≠ 0 := by letI := ecPointFintype E; exact Fintype.card_ne_zero
  simpa [countWord,hpos,←Nat.size_eq_bits_len] using Nat.size_le.mpr hlim
end DetDLP.S8F
set_option autoImplicit false
namespace DetDLP.S8F
open S8B M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def tr (t : Bool) (O : PrimitiveMachine) (o : Fin O.tapeCount) (τ σ : ℝ) : ℕ → Word → Word → Word → ℕ → Prop :=
  Nat.rec (motive := fun _ => Word → Word → Word → ℕ → Prop) (fun _ _ _ _ => False)
    (fun _ prev st ans out z => (step t (pair st ans) = true :: out ∧ (pair st ans).length ≤ z ∧ out.length ≤ z) ∨
    ∃ st' q ans', step t (pair st ans) = false :: pair st' q ∧ (pair st ans).length ≤ z ∧ (pair st' q).length ≤ z ∧ ans'.length ≤ z ∧ RunsWithin O o q ans' τ σ ∧ prev st' ans' out z)

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
local notation "C" => encodeCurveInput p E
local notation "G" => order E
noncomputable def value (w : W) (i : ℕ) := ecMom E ⟨i%4,Nat.mod_lt _ (by decide)⟩ (w++[decide (4 ≤ i)])
noncomputable def table (w : W) : ℕ → List W
  | 0 => []
  | i+1 => table w i ++ [countWord (value E w i)]
@[simp] theorem table_length (w : W) (i : ℕ) : (table E w i).length=i := by induction i with | zero => rfl | succ i ih => simp [table,ih]

theorem select_table (w : W) : select p G (table E w 8) = ecNext E w := by
  simp [select,table,value,ecNext,fromMoments,paramLen,stage_eq,List.getD_cons_succ,List.getD_cons_zero]

noncomputable def packet (w : W) (i : ℕ) := queryWord 2 C [countWord (i%4),countWord (stageT p G),w++[decide (4 ≤ i)]]

theorem ask_table (raw : W) (w : W) (i : ℕ) : ask raw C p G w (table E w i) = false :: pair (enc (raw::countWord G::w::table E w i)) (packet E w i) := by simp [ask,packet]

theorem packet_run {O : PrimitiveMachine} {o : Fin O.tapeCount} {K : ℕ}
    (hO : ∀ w b n, Query w b n → RunsWithin O o w (encodeNatListBin [n]) (mainSpaceBound K b) (polyBound K b))
    [E.IsElliptic] (h3 : 3 < p) (w : W) (i : ℕ) (hw : w.length < seedLen p) (ht : ecT E ≤ p) :
    RunsWithin O o (packet E w i) (encodeNatListBin [value E w i]) (mainSpaceBound K (bitLen p)) (polyBound K (bitLen p)) := by
  apply hO
  unfold packet value; rw [stage_eq]; apply Query.ecMoment p h3 E (⟨i%4,Nat.mod_lt _ (by decide)⟩ : Fin 4) _ ht
  rw [seedLen_eq] at hw; simp; omega

/-- All lengths needed for one call, using the same polynomial cap for both machines. -/
theorem packet_bounds [E.IsElliptic] (h3 : 3 < p) (raw w : W) (i : ℕ) (hi : i < 8) (hr : raw.length ≤ unitCap (bitLen p)) (hc : (encodeCurveInput p E).length ≤ unitCap (bitLen p)) (hw : w.length < seedLen p) (ht : ecT E ≤ p) :
    let st := enc (raw::countWord G::w::table E w i); let q := packet E w i; let a := encodeNatListBin [value E w i]; let z := cap (bitLen p)
    (pair st q).length ≤ z ∧ a.length ≤ z ∧ (pair st a).length ≤ z := by
  intro st q a z
  let u := unitCap (bitLen p)
  obtain ⟨hL,hb,hv⟩ := atomic_bounds E h3
  have hg := gwidth E h3
  have hw' : w.length+1 ≤ u := by rw [seedLen_eq] at hw; dsimp [u]; omega
  have htable (k : ℕ) : ∀ x ∈ table E w k, x.length ≤ u := by
    induction k with
    | zero => simp [table]
    | succ k ih => intro x hx; simp only [table,List.mem_append,List.mem_singleton] at hx; rcases hx with h|rfl; exact ih _ h; exact hv _ _
  have hs := enc_len (raw::countWord G::w::table E w i) u (by simp only [List.mem_cons,forall_eq_or_imp]; exact ⟨hr,by dsimp [u]; omega,hw'.trans' (by omega),htable _⟩)
  change st.length ≤ _ at hs; simp only [List.length_cons,table_length] at hs
  have hs' : st.length ≤ 10*(2*u+2)+1 := hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)
  have hq : q.length ≤ 5*(2*u+2)+1 := by
    apply enc_len [countWord 2,C,countWord (i%4),countWord (stageT p G),w++[decide (4 ≤ i)]] u
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,List.length_append,List.length_singleton]; refine ⟨?_,?_,?_,?_,by rintro _ rfl; simpa using hw'⟩
    · change 2 ≤ _; dsimp [u]; omega
    · exact hc
    · have h' : i%4 ≤ 3 := by omega
      have := cw_le_prime _ 3 h'; change (countWord (i%4)).length ≤ 4 at this; dsimp [u]; omega
    · rw [stage_eq]; exact (cw_le_prime _ _ ht).trans (by dsimp [u]; omega)
  have ha : a.length ≤ 1*(2*u+2)+1 := enc_len [countWord (value E w i)] u (by simpa [value,u] using hv ⟨i%4,Nat.mod_lt _ (by decide)⟩ (w++[decide (4 ≤ i)]))
  have fit : 60*u+100 ≤ z := by dsimp [u,z,unitCap,cap]; nlinarith
  simp only [pair_len]; omega
end DetDLP.S8F
set_option autoImplicit false
namespace DetDLP.S8F
open S8B M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [hp : Fact p.Prime] (E : WeierstrassCurve (ZMod p))
local notation "C" => encodeCurveInput p E
local notation "G" => order E
noncomputable def chosen (k : ℕ) := path (ecNext E) k
noncomputable def largeOutput (raw : W) := enc [raw,true :: enc [countWord (ecT E),chosen E (seedLen p)]]

theorem large_run {O : PrimitiveMachine} {o : Fin O.tapeCount} {K : ℕ}
    (hO : ∀ w b n, Query w b n → RunsWithin O o w (encodeNatListBin [n]) (mainSpaceBound K b) (polyBound K b))
    [E.IsElliptic] (h3 : 3 < p) (t : Bool) (raw : W) (hr : raw.length ≤ unitCap (bitLen p)) (hpraw : curve t raw = C) (hc : (encodeCurveInput p E).length ≤ unitCap (bitLen p)) (hin : (pair (enc [raw]) (encodeNatListBin [G])).length ≤ cap (bitLen p))
    (h64 : 64 ≤ G) (h4096 : 4096*fpM p ≤ G-1) :
    tr t O o (mainSpaceBound K (bitLen p)) (polyBound K (bitLen p)) (8*seedLen p+1) (enc [raw]) (encodeNatListBin [G]) (largeOutput E raw) (cap (bitLen p)) := by
  let b := bitLen p; let N := seedLen p; let z := cap b; let u := unitCap b
  let R := tr t O o (mainSpaceBound K b) (polyBound K b)
  let out := largeOutput E raw
  have ht := threshold_le (p:=p) (show 2 ≤ fpM p from le_max_left ..) h64 h4096
  change ecT E ≤ p at ht
  have hpos : 0 < N := by
    have h := Nat.clog_pos (by decide : 1<2) hp.out.one_lt
    have hm : 2 ≤ fpM p := le_max_left ..
    dsimp [N]; rw [seedLen_eq]; change 0 < fpM p * 4 * Nat.clog 2 p; positivity
  have hw (k) : (chosen E k).length = k := path_len ..
  have fit : 60*u+100 ≤ z := by change 60*(100*(b+3)^2)+100 ≤ 10000*(b+3)^2; have H := Nat.pow_le_pow_left (show 3 ≤ b+3 by omega) 2; omega
  obtain ⟨hN,hb,_⟩ := atomic_bounds E h3
  have hout : out.length ≤ z := by
    have hT : (countWord (ecT E)).length ≤ u := (cw_le_prime _ _ ht).trans (by dsimp [u,b]; omega)
    have hW : (chosen E N).length ≤ u := by rw [hw]; dsimp [u,N,b]; rw [seedLen_eq]; omega
    have hw2 := enc_len [countWord (ecT E),chosen E N] u (by simp; exact ⟨hT,hW⟩)
    have hh := enc_len [raw,true :: enc [countWord (ecT E),chosen E N]] (4*u+6) (by simp; exact ⟨by change raw.length ≤ _; dsimp [u,b]; omega,by simp at hw2; omega⟩)
    change (enc [raw,true :: enc [countWord (ecT E),chosen E N]]).length ≤ _; simp at hh; omega
  have recRun (r k i : ℕ) (kN : k<N) (hi : i<8) (eq : r + 8*k + i + 1 = 8*N) :
      let w := chosen E k
      R (r+1) (enc (raw::countWord G::w::table E w i)) (encodeNatListBin [value E w i]) out z := by
    induction r generalizing k i with
    | zero =>
      have hki : k+1=N := by omega
      have hi7 : i=7 := by omega
      subst i; let w := chosen E k
      have hh := packet_bounds E h3 raw w 7 (by decide) hr hc (by rw [show w.length = k from hw k]; exact kN) ht
      apply Or.inl; refine ⟨?_,hh.2.2,hout⟩
      rw [step_ans,hpraw,prime_curve]; change driver raw C p G w (table E w 8) = _
      simp only [driver,table_length,show ¬ 8<8 by decide,if_false,select_table]
      change advance raw C p G (chosen E (k+1)) = _
      simp [advance,hw, hki,N,←hki,finish,out,largeOutput,stage_eq]
    | succ r ih =>
      let w := chosen E k
      have wl : w.length < seedLen p := (hw k).trans_lt kN
      have before := (packet_bounds E h3 raw w i hi hr hc wl ht).2.2
      by_cases more : i+1<8
      · have bounds := packet_bounds E h3 raw w (i+1) more hr hc wl ht
        apply Or.inr
        refine ⟨_,_,_,?_,before,bounds.1,bounds.2.1,packet_run E hO h3 w (i+1) wl ht,ih k (i+1) kN more (by omega)⟩
        rw [step_ans,hpraw,prime_curve]; change driver raw C p G w (table E w (i+1)) = _
        simp [driver,table_length,more,ask_table]
      · have hi7 : i=7 := by omega
        subst i; have hk : k+1<N := by omega
        let w' := chosen E (k+1)
        have wl' : w'.length < seedLen p := (hw _).trans_lt hk
        have bounds := packet_bounds E h3 raw w' 0 (by decide) hr hc wl' ht
        apply Or.inr
        refine ⟨_,_,_,?_,before,bounds.1,bounds.2.1,packet_run E hO h3 w' 0 wl' ht,ih (k+1) 0 hk (by decide) (by omega)⟩
        rw [step_ans,hpraw,prime_curve]; change driver raw C p G w (table E w 8) = _
        simp only [driver,table_length,show ¬ 8<8 by decide,if_false,select_table]
        change advance raw C p G w' = _
        rw [advance,if_neg (Nat.not_le.mpr wl')]; exact ask_table E raw w' 0
  have bounds := packet_bounds E h3 raw [] 0 (by decide) hr hc hpos ht
  have h0 := recRun (8*N-1) 0 0 hpos (by decide) (by omega)
  rw [show 8*N-1+1 = 8*N by omega] at h0
  apply Or.inr; refine ⟨_,_,_,?_,?_,bounds.1,bounds.2.1,packet_run E hO h3 [] 0 hpos ht,h0⟩
  · rw [step_order,hpraw,prime_curve]; unfold init
    have hh : blocks (p-1).size = fpM p := by
      rw [blocks_eq]; congr 1; apply le_antisymm
      · apply Nat.size_le.mpr; have := Nat.le_pow_clog (by decide : 1 < 2) p; change p-1 < 2^(Nat.clog 2 p); omega
      · apply (Nat.clog_le_iff_le_pow (by decide)).2; have := Nat.lt_size_self (p-1); omega
    rw [hh,if_pos ⟨h64,h4096⟩]; exact ask_table E raw [] 0
  · exact hin
end DetDLP.S8F
set_option autoImplicit false
set_option maxRecDepth 8192
namespace DetDLP.S8F
open S8B M89S1 Groundwork
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
  have hc : PB cap := (PB.const 10000).mul (pb_pow (PB.id'.add (PB.const 3)) 2)
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
end DetDLP.S8F
set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open DetDLP.S8F DetDLP.S8B

theorem solution : CountOracle → ∃ (U : PrimitiveMachine) (u : Fin U.tapeCount) (V : PrimitiveMachine) (v : Fin V.tapeCount) (J : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic], 
      let b := bitLen p; let m := blockCount b
      ∃ L : Option (ℕ × ECSeed p m), m89_ec_plan_ok E L ∧
        RunsWithin U u (encodeCurveInput p E) (Encoding.encodeList id [(encodeCurveInput p E),m89_ec_plan_word L]) (mainSpaceBound J b) (polyBound J b) ∧
        ∀ X : E.toAffine.Point, RunsWithin V v (Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)]) (Encoding.encodeList id [(Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)]),m89_ec_plan_word L]) (mainSpaceBound J b) (polyBound J b) := by
  rintro ⟨O,o,A,hO⟩
  obtain ⟨U,u,I,hu⟩ := machine false o A
  obtain ⟨V,v,H,hv⟩ := machine true o A
  refine ⟨U,u,V,v,max I H,?_⟩; intro p hp h3 E hE b m
  let c := encodeCurveInput p E; let g := order E; let z := cap b; let n := seedLen p; let u0 := unitCap b
  have h2 := hp.out.two_le
  have fit : 60*u0+100 ≤ z := by change 60*(100*(b+3)^2)+100 ≤ 10000*(b+3)^2; have h := Nat.pow_le_pow_left (show 3 ≤ b+3 by omega) 2; omega
  obtain ⟨hL,hb,_⟩ := atomic_bounds E h3
  have en (l : List ℕ) : encodeNatListBin l = enc (l.map countWord) := by induction l with | nil => rfl | cons a l ih => change true::(_ ++ encodeNatListBin l) = true::(_ ++ enc (l.map countWord)); rw [ih]; rfl
  have nb (l : List ℕ) (hl : ∀ a ∈ l, a ≤ p) : (encodeNatListBin l).length ≤ l.length*(2*(b+2)+2)+1 := by
    rw [en]; apply (enc_len _ (b+2) ?_).trans; · simp
    intro w hw; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw; exact cw_le_prime a p (hl _ ha)
  have hc0 : c.length ≤ 6*(2*(b+2)+2)+1 := by
    apply nb [p,E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val]; simp; exact ⟨(ZMod.val_lt _).le,(ZMod.val_lt _).le,(ZMod.val_lt _).le,(ZMod.val_lt _).le,(ZMod.val_lt _).le⟩
  have hc : c.length ≤ u0 := hc0.trans (by dsimp [u0,unitCap]; nlinarith)
  have hX (X : E.toAffine.Point) : (enc [c,encodeNatListBin (pointCoords X)]).length ≤ u0 := by
    have hx : (encodeNatListBin (pointCoords X)).length ≤ 3*(2*(b+2)+2)+1 := by
      cases X with
      | zero => apply nb [1,0,0]; simp; omega
      | some x y _ => apply nb [0,x.val,y.val]; simp; exact ⟨(ZMod.val_lt _).le,(ZMod.val_lt _).le⟩
    apply (enc_len _ (6*(2*(b+2)+2)+1) (by simp; exact ⟨hc0,by omega⟩)).trans; simp; dsimp [u0,unitCap]; nlinarith
  have hglen : (countWord g).length ≤ u0 := (gwidth E h3).trans (by dsimp [u0,b]; omega)
  have ha : (encodeNatListBin [g]).length ≤ 2*u0+3 := by change (enc [countWord g]).length ≤ _; simpa using enc_len [countWord g] u0 (by simpa using hglen)
  have hq : (queryWord 0 c []).length ≤ 4*u0+5 := by
    have h0 : (countWord 0).length ≤ u0 := by change 1 ≤ u0; dsimp [u0,b]; omega
    have hh := enc_len [countWord 0,c] u0 (by simp; exact ⟨h0,hc⟩)
    change (enc [countWord 0,c]).length ≤ 2*(2*u0+2)+1 at hh
    change (enc [countWord 0,c]).length ≤ _; omega
  have first (t : Bool) (raw out : W) (hr : raw.length ≤ u0) (he : curve t raw = c) (r : ℕ)
      (tail : tr t O o (mainSpaceBound A b) (polyBound A b) r (enc [raw]) (encodeNatListBin [g]) out z) :
      tr t O o (mainSpaceBound A b) (polyBound A b) (r+1) raw [] out z := by
    have hs := enc_len [raw] u0 (by simpa using hr); simp at hs
    apply Or.inr; refine ⟨enc [raw],queryWord 0 c [],encodeNatListBin [g],?_,?_,?_,by omega,hO _ _ _ (Query.ecOrder p h3 E),tail⟩
    · rw [step_init]; simp [orderAsk,he]
    · rw [pair_len]; simp; omega
    · rw [pair_len]; omega
  have input (raw : W) (hr : raw.length ≤ u0) : (pair (enc [raw]) (encodeNatListBin [g])).length ≤ z := by
    have hs := enc_len [raw] u0 (by simpa using hr); simp at hs; rw [pair_len]; omega
  have common : ∃ L : Option (ℕ × ECSeed p m), m89_ec_plan_ok E L ∧ ∃ r, 1 ≤ r ∧ r ≤ cap b ∧
      ∀ t raw, raw.length ≤ u0 → curve t raw = c → tr t O o (mainSpaceBound A b) (polyBound A b) r raw [] (enc [raw,m89_ec_plan_word L]) z := by
    by_cases hg : 64 ≤ g ∧ 4096*fpM p ≤ g-1
    · obtain ⟨s,hs,hw⟩ := ec_law E hg.1 hg.2
      refine ⟨some (ecT E,s),hs,8*n+1+1,by omega,?_,?_⟩
      · change 8*seedLen p+1+1 ≤ z; rw [seedLen_eq]; dsimp [u0,b] at fit; omega
      · intro t raw hr he; apply first t _ _ hr he
        have hh := large_run E hO h3 t raw hr he hc (input raw hr) hg.1 hg.2
        simpa only [n,z,b,g,largeOutput,chosen,m89_ec_plan_word,hw,seedLen_eq,enc] using hh
    · refine ⟨none,hg,2,by decide,by change 2 ≤ z; omega,?_⟩
      intro t raw hr he; apply first t _ _ hr he 1; apply Or.inl; refine ⟨?_,input raw hr,?_⟩
      · rw [step_order,he]; change init raw c (prime (encodeCurveInput p E)) g = _; rw [prime_curve]; unfold init; rw [blocks_eq,size_eq,if_neg hg]; rfl
      · have := enc_len [raw,[false]] u0 (by simp; exact ⟨hr,by dsimp [u0,b]; omega⟩); change (enc [raw,[false]]).length ≤ z; simp at this; omega
  obtain ⟨L,hL,r,hr1,hr2,trace⟩ := common
  refine ⟨L,hL,?_,?_⟩
  · have h := hu p r _ _ h2 hr1 hr2 (trace false _ hc rfl)
    exact weakenRun h (stage1_complexity_dominance.1 _ _ b (le_max_left I H)).1 (stage1_complexity_dominance.1 _ _ b (le_max_left I H)).2
  · intro X; have h := hv p r _ _ h2 hr1 hr2 (trace true _ (hX X) (by simp [curve,enc]))
    exact weakenRun h (stage1_complexity_dominance.1 _ _ b (le_max_right I H)).1 (stage1_complexity_dominance.1 _ _ b (le_max_right I H)).2
