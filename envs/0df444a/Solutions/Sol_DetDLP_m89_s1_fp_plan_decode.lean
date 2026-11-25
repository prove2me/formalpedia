-- Prove2me | solution 1 for DetDLP.m89_s1_fp_plan_decode
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T04:34:22.884222+00:00
-- url     : https://prove2.me/submissions/2dd54229-2ecd-4d47-a804-6450932ffa4b

import Definitions.Def_DetDLP_S8A_FpDecodeBounds
set_option autoImplicit false
open DetDLP DetDLP.M89S1 DetDLP.m89_decode DetDLP.m89_decode_step DetDLP.m89_decode_finish DetDLP.m89_decode_trace DetDLP.m89_decode_lengths DetDLP.m89_enum_words
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
namespace DetDLP.m89_decode_final
private theorem grow (b : ℕ) (hb : 20 ≤ b) : 8192*(b+2)+4 ≤ 2^(b-1) := by
  induction b, hb using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [show k+1-1 = (k-1)+1 by omega,pow_succ]; omega

theorem small (p : ℕ) (hs : ¬(64 ≤ p-1 ∧ 4096*blockCount (bitLen p) ≤ p-1)) : blockCount (bitLen p) = 2 := by
  let b := bitLen p
  have hm : 2 ≤ blockCount b := le_max_left ..
  have hp : p ≤ 4096*blockCount b+1 := by change ¬(64 ≤ p-1 ∧ 4096*blockCount b ≤ p-1) at hs; omega
  have h : p ≤ 4096*(b+2)+1 := by have := blocks b; omega
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


private theorem outputLength {p m : ℕ} [Fact p.Prime] (A B : Fin m → (ZMod p)ˣ) : (encodeFpDecomp A B).length ≤ m*(4*bitLen p+12)+1 := by
  let f := fun i : Fin m => [(A i : ZMod p).val,(B i : ZMod p).val]
  have gen (l : List (Fin m)) : (encodeNatListBin (l.flatMap f)).length ≤ l.length*(4*bitLen p+12)+1 := by
    induction l with
    | nil => simp [encodeNatListBin]
    | cons i l ih =>
      have h (z : (ZMod p)ˣ) := cw (bitLen p) _ ((ZMod.val_lt (z : ZMod p)).le.trans (Nat.le_pow_clog (by decide) p))
      change (Encoding.encodeList countWord ((A i : ZMod p).val::(B i : ZMod p).val::l.flatMap f)).length ≤ _
      simp only [econs,List.length_cons,Nat.add_mul,Nat.one_mul]; change (encodeNatListBin (l.flatMap f)).length ≤ _ at ih
      have ha := h (A i); have hb := h (B i); unfold encodeNatListBin at ih; omega
  simpa [encodeFpDecomp,f] using gen (List.finRange m)

private theorem outBudget {p : ℕ} [Fact p.Prime] (A B : Fin (blockCount (bitLen p)) → (ZMod p)ˣ) : (encodeFpDecomp A B).length ≤ budget (bitLen p) := by
  apply (outputLength A B).trans; unfold budget
  have h := Nat.mul_le_mul_right (4*bitLen p+12) (blocks (bitLen p)); nlinarith
end DetDLP.m89_decode_final
open DetDLP.m89_decode_final
theorem solution : CountOracle → ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 
      let b := bitLen p; let m := blockCount b
      ∀ L : Option (ℕ × FpSeed p m), m89_fp_plan_ok L → ∀ X : (ZMod p)ˣ,
        (∃ A B : Fin m → (ZMod p)ˣ, (∀ i, A i ∈ m89_fp_plan_block L i ∧ B i ∈ m89_fp_plan_block L i) ∧ (∏ i, (A i * B i)) = X) →
        ∃ A B : Fin m → (ZMod p)ˣ, (∀ i, A i ∈ m89_fp_plan_block L i ∧ B i ∈ m89_fp_plan_block L i) ∧ (∏ i, (A i * B i)) = X ∧
          RunsWithin M o (Encoding.encodeList id [(encodeNatListBin [p,(X : ZMod p).val]),m89_fp_plan_word L]) (encodeFpDecomp A B) (mainSpaceBound K b) (polyBound K b) := by
  rintro ⟨O,o,j,oracle⟩
  obtain ⟨M,d,k,_,loop⟩ := m89_polyT_oracle_loop step step_poly O o
  obtain ⟨K,hK⟩ := m89_decode_cost.budgets k j
  refine ⟨M,d,K,?_⟩; intro p inst b m L hok X hex
  have hp := (Fact.out : Nat.Prime p).two_le
  have run (r : ℕ) (hr : 1 ≤ r) (hrb : r ≤ budget b) (u v : Word)
      (h : LR O o (mainSpaceBound j b) (polyBound j b) r u [] v (budget b)) : RunsWithin M d u v (mainSpaceBound K b) (polyBound K b) := by
    have R := loop (mainSpaceBound j b) (polyBound j b) (by unfold mainSpaceBound; positivity) (by unfold polyBound; positivity) r (budget b) u v hr h
    exact PolyTBridge.runsWithin_mono_local R (hK p hp r hrb).1 (hK p hp r hrb).2
  cases L with
  | none =>
    have hm : m=2 := small p hok
    haveI : NeZero m := ⟨by omega⟩
    let A := fun i : Fin m => if i=0 then X else 1
    let B := fun _ : Fin m => (1 : (ZMod p)ˣ)
    refine ⟨A,B,by simp [m89_fp_plan_block],by simp [A,B],?_⟩
    have enc : encodeFpDecomp A B = encodeNatListBin [(X : ZMod p).val,1,1,1] := by
      have aux (z : ℕ) [NeZero z] (hz : z=2) : encodeFpDecomp (fun i : Fin z => if i=0 then X else 1) (fun _ => 1) = encodeNatListBin [(X : ZMod p).val,1,1,1] := by
        subst z; simp [encodeFpDecomp,List.finRange_succ,ZMod.val_one]
      exact aux m hm
    apply run 1 le_rfl (by unfold budget; nlinarith)
    refine Or.inl ⟨enc ▸ step_none p _,?_,outBudget A B⟩
    have hpw := cw b p (Nat.le_pow_clog (by decide) p)
    have hxw := cw b _ ((ZMod.val_lt (X : ZMod p)).le.trans (Nat.le_pow_clog (by decide) p))
    simp only [pair_len,encodeNatListBin,m89_fp_plan_word,econs,enil,id_eq,List.length_cons,List.length_nil]; unfold budget; nlinarith
  | some z =>
    rcases z with ⟨T,S⟩
    obtain ⟨A,B,hm',hp',ht⟩ := path_witness (D (T:=T) S) X hex
    refine ⟨A,B,hm',hp',?_⟩
    let n := nbit p
    have hbud : n+1 ≤ budget b := by have h := bound0 p; change 128*(n+b+2) ≤ budget b at h; omega
    apply run (n+1) (by omega) hbud
    obtain ⟨hlen,hqs⟩ := lengths S X hok
    apply linearTrace (n:=n) (st (T:=T) S X) (ans (T:=T) S X) (query (T:=T) S X)
    · intro k hk; rw [stage,advance_eq,if_pos hk]
    · rw [stage,advance_eq,if_neg (Nat.lt_irrefl _),←finish_tuple A B,ht]
    · exact hlen
    · exact outBudget A B
    · intro k hk; obtain ⟨hq,ha⟩ := hqs k hk
      exact ⟨hq,ha,oracle _ _ _ (next_query hok X k hk)⟩

#print axioms solution
