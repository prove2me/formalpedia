-- Prove2me | solution 1 for DetDLP.m89_s1_ec_plan_decode
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T04:45:40.699838+00:00
-- url     : https://prove2.me/submissions/f5d01da8-1e93-4ef9-83e5-ac9ecd3f50be

import Definitions.Def_DetDLP_S8E_ECTrace
import Theorems.Thm_DetDLP_hasse_ec_point_count_bound
set_option autoImplicit false
namespace DetDLP.s8e
open M89S1 m89_decode_step m89_enum_words
open m89_decode_lengths (cw budget blocks econs enil pair_len)
open m89_decode (path_length)
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
variable {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)}
private theorem count_le [E.IsElliptic] (hp : 3 < p) {m : ℕ} (D : Fin m → Finset E.toAffine.Point) (X : E.toAffine.Point) (w : Word) : cnt D X w ≤ 2^(2*m*(2*bitLen p+1)) := by
  classical
  letI := ecPointFintype E
  have hu := (abs_le.mp (hasse_ec_point_count_bound p hp E)).2
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p)
  have hc0 : (Fintype.card E.toAffine.Point : ℝ) ≤ 2*(p:ℝ)+2 := by nlinarith [sq_nonneg (Real.sqrt (p:ℝ)-1)]
  have hc1 : Fintype.card E.toAffine.Point ≤ 2*p+2 := by exact_mod_cast hc0
  have hpow : p ≤ 2^(bitLen p) := Nat.le_pow_clog (by decide) p
  have hc : Fintype.card E.toAffine.Point ≤ 2^(2*bitLen p+1) := by rw [pow_succ,two_mul,Nat.pow_add]; nlinarith [Nat.mul_le_mul hpow hpow]
  have hh := Nat.pow_le_pow_left hc m
  calc cnt D X w ≤ Fintype.card ((Fin m → E.toAffine.Point) × (Fin m → E.toAffine.Point)) := Finset.card_le_univ _
       _ = (Fintype.card E.toAffine.Point)^m * (Fintype.card E.toAffine.Point)^m := by simp [Fintype.card_fun]
       _ ≤ (2^(2*bitLen p+1))^m * (2^(2*bitLen p+1))^m := Nat.mul_le_mul hh hh
       _ = _ := by rw [←Nat.pow_mul,←Nat.pow_add]; congr 1; ring

theorem bound0 (p : ℕ) : 128*(nbit p+4*bitLen p+12) ≤ budget (bitLen p) := by
  unfold nbit budget
  have h := Nat.mul_le_mul_right (2*bitLen p+1) (blocks (bitLen p)); nlinarith

private theorem valw (x : ZMod p) : (countWord x.val).length ≤ bitLen p+2 := cw _ _ ((ZMod.val_lt x).le.trans (Nat.le_pow_clog (by decide) p))
theorem plen (P : E.toAffine.Point) : (encodeNatListBin (pointCoords P)).length ≤ 6*bitLen p+19 := by
  cases P with
  | zero =>
    simp only [pointCoords,encodeNatListBin,econs,enil]
    have h : (countWord 0).length = 1 := by decide
    have h' : (countWord 1).length = 1 := by decide
    omega
  | some x y _ =>
    simp only [pointCoords,encodeNatListBin,econs,enil]
    have h : (countWord 0).length = 1 := by decide
    have := valw x; have := valw y; omega
private theorem clen : (encodeCurveInput p E).length ≤ 12*bitLen p+37 := by
  simp only [encodeCurveInput,encodeNatListBin,econs,enil]; have := cw (bitLen p) p (Nat.le_pow_clog (by decide) p); have := valw E.a₁; have := valw E.a₂; have := valw E.a₃; have := valw E.a₄; have := valw E.a₆; omega

theorem dlen (X : E.toAffine.Point) : (data X).length ≤ 36*bitLen p+117 := by unfold data; simp only [econs,enil,id_eq]; have := plen X; have := clen (E:=E); omega

variable [E.IsElliptic] {T : ℕ} (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point)
theorem lengths (hp3 : 3 < p) (hok : m89_ec_plan_ok E (some (T,S))) :
    (∀ k, k ≤ nbit p → (pair (st (T:=T) S X k) (ans (T:=T) S X k)).length ≤ budget (bitLen p)) ∧
    (∀ k, k < nbit p → (pair (st (T:=T) S X (k+1)) (query (T:=T) S X k)).length ≤ budget (bitLen p) ∧ (ans (T:=T) S X (k+1)).length ≤ budget (bitLen p)) := by
  let b := bitLen p; let n := nbit p
  have hpow : p ≤ 2^b := Nat.le_pow_clog (by decide) _
  have hx := plen X; have hc := clen (E:=E)
  have ht := cw b T (le_trans (hok.2.2.1 ▸ threshold_le (le_max_left ..) hok.1 hok.2.1) hpow)
  have hseed : (List.ofFn (ecBits S)).length ≤ n := by simp only [List.length_ofFn]; dsimp [n,nbit]; nlinarith
  have hd := dlen X
  have hplan : (plan (T:=T) S).length ≤ 2*b+2*n+10 := by unfold plan m89_ec_plan_word; simp only [List.length_cons,econs,enil,id_eq]; omega
  have hcnt (k : ℕ) := cw n _ (count_le hp3 (D (E:=E) (T:=T) S) X (pre (T:=T) S X k ++ [false]))
  have han (k : ℕ) : (ans (T:=T) S X (k+1)).length ≤ 2*n+7 := by unfold ans encodeNatListBin leftCount; simp only [econs,enil]; specialize hcnt k; omega
  change (data X).length ≤ 36*b+117 at hd
  change (encodeNatListBin (pointCoords X)).length ≤ 6*b+19 at hx
  change (encodeCurveInput p E).length ≤ 12*b+37 at hc
  have hst (k : ℕ) (hk : k ≤ n) : (st (T:=T) S X (k+1)).length ≤ 76*b+6*n+261 := by unfold st state; simp only [econs,enil,id_eq,pre,path_length]; omega
  have htag : (countWord 6).length = 3 := by decide
  have hq (k : ℕ) (hk : k ≤ n) : (query (T:=T) S X k).length ≤ 38*b+4*n+140 := by unfold query queryWord; simp only [econs,enil,id_eq,htag,List.length_append,List.length_cons,List.length_nil,pre,path_length]; omega
  have key : 128*(n+4*b+12) ≤ budget b := bound0 p
  constructor
  · intro k hk
    cases k with
    | zero => simp only [st,ans,pair_len,econs,enil,id_eq,List.length_nil]; change _ ≤ budget b; omega
    | succ k => have h1 := hst k (by change k+1 ≤ n at hk; omega); have h2 := han k; rw [pair_len]; change _ ≤ budget b; omega
  · intro k hk
    have h1 := hst k hk.le; have h2 := han k; have h3 := hq k hk.le; rw [pair_len]; change _ ≤ budget b ∧ _ ≤ budget b; omega

private theorem growth (b : ℕ) (hb : 20 ≤ b) : 8192*(b+2)+4 ≤ 2^(b-1) := by
  induction b, hb using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h : k+1-1 = (k-1)+1 := by omega
    rw [h, pow_succ]
    omega

private theorem prime_bound (p g : ℕ) (hg : p ≤ 2*g+4)
    (hs : ¬ (64 ≤ g ∧ 4096 * blockCount (bitLen p) ≤ g-1)) : p ≤ 2^20 := by
  let b := bitLen p
  have hm : 2 ≤ blockCount b := le_max_left ..
  change ¬(64 ≤ g ∧ 4096 * blockCount b ≤ g-1) at hs
  have hn : g ≤ 4096 * blockCount b := by by_contra! hn; apply hs; constructor <;> omega
  have h : p ≤ 8192*(b+2)+4 := by have := blocks b; omega
  have hl : b ≤ 20 := by
    by_contra! hl
    have hu : 2^(b-1) < p := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).1 (show b-1 < b by omega)
    have := growth b (by omega)
    omega
  exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).1 hl

private theorem ec_small_bound {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hsmall : letI := ecPointFintype E; let g := Fintype.card E.toAffine.Point
      ¬(64 ≤ g ∧ 4096 * blockCount (bitLen p) ≤ g-1)) : p ≤ 2^20 := by
  letI := ecPointFintype E
  let g := Fintype.card E.toAffine.Point
  apply prime_bound p g _ hsmall
  have lower := (abs_le.mp (hasse_ec_point_count_bound p hp E)).1
  change -(2 * √(p : ℝ)) ≤ (g : ℝ) - ((p : ℝ) + 1) at lower
  have sq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  have aux : (p : ℝ) ≤ 2*(g : ℝ)+4 := by nlinarith [sq_nonneg (√(p : ℝ)-2)]
  exact_mod_cast aux

private theorem small (hp : 3 < p) (hok : m89_ec_plan_ok E (m:=blockCount (bitLen p)) none) : blockCount (bitLen p) = 2 := by
  let b := bitLen p
  have hl : b ≤ 20 := (Nat.clog_le_iff_le_pow (by decide)).2 (ec_small_bound hp E hok)
  have hm : 2 ≤ blockCount b := le_max_left ..
  apply le_antisymm _ hm
  apply max_le le_rfl (Nat.ceil_le.mpr ?_)
  have hk : Nat.clog 2 (b+2) ≤ 16 := (Nat.clog_le_iff_le_pow (by decide)).2 (by norm_num; omega)
  have h16 : (16:ℝ)^((1:ℝ)/4) = 2 := by
    rw [show (16:ℝ) = (2:ℝ)^4 by norm_num,←Real.rpow_natCast_mul (by norm_num)]; norm_num
  change (Nat.clog 2 (b+2):ℝ)^((1:ℝ)/4) ≤ (2:ℝ)
  rw [←h16]; exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk) (by norm_num)


private theorem outBudget {m : ℕ} (hm : m = blockCount (bitLen p)) (A B : Fin m → E.toAffine.Point) : (encodeECDecomp A B).length ≤ budget (bitLen p) := by
  let b := bitLen p
  let f := fun P : E.toAffine.Point => encodeNatListBin (pointCoords P)
  have gen (l : List (Fin m)) : (Encoding.encodeList f (l.flatMap (fun i => [A i,B i]))).length ≤ l.length*(24*b+80)+1 := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.flatMap_cons,List.cons_append,List.nil_append,econs,List.length_cons,Nat.add_mul,Nat.one_mul]
      have ha : (f (A i)).length ≤ 6*b+19 := plen _
      have hb : (f (B i)).length ≤ 6*b+19 := plen _
      omega
  have h : (encodeECDecomp A B).length ≤ m*(24*b+80)+1 := by simpa [encodeECDecomp,f] using gen (List.finRange m)
  apply h.trans; unfold budget; change _ ≤ 1024*(b+2)*(b+2)
  have hm' : m ≤ b+2 := hm ▸ blocks b
  nlinarith [Nat.mul_le_mul_right (24*b+80) hm']
private theorem smallEnc {m : ℕ} [NeZero m] (hm : m=2) (X : E.toAffine.Point) :
    encodeECDecomp (fun i : Fin m => if i=0 then X else 0) (fun _ => 0) = Encoding.encodeList id [encodeNatListBin (pointCoords X),encodeNatListBin [1,0,0],encodeNatListBin [1,0,0],encodeNatListBin [1,0,0]] := by
  subst m
  simp [encodeECDecomp,List.finRange_succ]
  rfl
end DetDLP.s8e
open DetDLP DetDLP.M89S1 DetDLP.s8e
open DetDLP.m89_decode_lengths (budget cw econs enil pair_len)
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem solution : CountOracle → ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic], 
      let b := bitLen p; let m := blockCount b
      ∀ L : Option (ℕ × ECSeed p m), m89_ec_plan_ok E L → ∀ X : E.toAffine.Point,
        (∃ A B : Fin m → E.toAffine.Point, (∀ i, A i ∈ m89_ec_plan_block E L i ∧ B i ∈ m89_ec_plan_block E L i) ∧ (∑ i, (A i + B i)) = X) →
        ∃ A B : Fin m → E.toAffine.Point, (∀ i, A i ∈ m89_ec_plan_block E L i ∧ B i ∈ m89_ec_plan_block E L i) ∧ (∑ i, (A i + B i)) = X ∧
          RunsWithin M o (Encoding.encodeList id [(Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)]),m89_ec_plan_word L]) (encodeECDecomp A B) (mainSpaceBound K b) (polyBound K b) := by
  rintro ⟨O,o,j,oracle⟩
  obtain ⟨M,d,k,_,loop⟩ := m89_polyT_oracle_loop step step_poly O o
  obtain ⟨K,hK⟩ := m89_decode_cost.budgets k j
  refine ⟨M,d,K,?_⟩; intro p inst h3 E el b m L hok X hex
  have hp := (Fact.out : Nat.Prime p).two_le
  have run (r : ℕ) (hr : 1 ≤ r) (hrb : r ≤ budget b) (u v : List Bool)
      (h : LR O o (mainSpaceBound j b) (polyBound j b) r u [] v (budget b)) : RunsWithin M d u v (mainSpaceBound K b) (polyBound K b) := by
    have R := loop (mainSpaceBound j b) (polyBound j b) (by unfold mainSpaceBound; positivity) (by unfold polyBound; positivity) r (budget b) u v hr h
    exact PolyTBridge.runsWithin_mono_local R (hK p hp r hrb).1 (hK p hp r hrb).2
  cases L with
  | none =>
    have hm : m=2 := small h3 hok
    haveI : NeZero m := ⟨by omega⟩
    let A := fun i : Fin m => if i=0 then X else 0
    let B := fun _ : Fin m => (0 : E.toAffine.Point)
    refine ⟨A,B,by simp [m89_ec_plan_block],by simp [A,B],?_⟩
    let z := encodeNatListBin [1,0,0]
    have enc : encodeECDecomp A B = Encoding.encodeList id [encodeNatListBin (pointCoords X),z,z,z] := by
      exact smallEnc hm X
    apply run 1 le_rfl (by unfold budget; nlinarith [Nat.zero_le (b*b)])
    refine Or.inl ⟨enc ▸ step_none _ _,?_,outBudget rfl A B⟩
    have hd : (data X).length ≤ 36*b+117 := dlen X
    change (m89_decode_step.pair (Encoding.encodeList id [data X,[false]]) []).length ≤ budget b
    have hx := plen X; have hc := clen (E:=E)
    change (encodeNatListBin (pointCoords X)).length ≤ 6*b+19 at hx
    change (encodeCurveInput p E).length ≤ 12*b+37 at hc
    simp only [pair_len,econs,enil,id_eq,List.length_cons,List.length_nil]; unfold budget; nlinarith
  | some z =>
    rcases z with ⟨T,S⟩
    obtain ⟨A,B,hm',hp',ht⟩ := path_witness (D (E:=E) (T:=T) S) X hex
    refine ⟨A,B,hm',hp',?_⟩
    let n := nbit p
    have hbud : n+1 ≤ budget b := by have h := bound0 p; change 128*(n+4*b+12) ≤ budget b at h; omega
    apply run (n+1) (by omega) hbud
    obtain ⟨hlen,hqs⟩ := lengths S X h3 hok
    apply linearTrace (n:=n) (st (T:=T) S X) (ans (T:=T) S X) (query (T:=T) S X)
    · intro k hk; rw [stage,advance_eq,if_pos hk]
    · rw [stage,advance_eq,if_neg (Nat.lt_irrefl _),←finish_tuple A B,ht]
    · exact hlen
    · exact outBudget rfl A B
    · intro k hk; obtain ⟨hq,ha⟩ := hqs k hk
      exact ⟨hq,ha,oracle _ _ _ (next_query S X h3 hok k hk)⟩

#print axioms solution
