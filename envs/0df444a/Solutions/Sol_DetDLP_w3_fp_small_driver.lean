-- Prove2me | solution 1 for DetDLP.w3_fp_small_driver
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T00:41:31.747914+00:00
-- url     : https://prove2.me/submissions/f918f1c2-8e2a-4612-874d-1a476e603665

import Definitions.Def_DetDLP_W3_Driver
import Definitions.Def_DetDLP_PolyTBridge
import Theorems.Thm_DetDLP_w3_bounded_word_machine
import Theorems.Thm_DetDLP_w3_small_prime_bound

set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private def DetDLP.w3_unframe : List Bool → List Bool × List Bool
  | true::b::xs => let q := w3_unframe xs; (b::q.1,q.2)
  | false::xs => ([],xs)
  | _ => ([],[])

private theorem DetDLP.w3_unframe_spec (v s : List Bool) :
    w3_unframe (Encoding.frame v ++ s) = (v,s) := by
  induction v with
  | nil => rfl
  | cons b v ih => change (b::(w3_unframe (Encoding.frame v ++ s)).1,(w3_unframe (Encoding.frame v ++ s)).2) = _; rw [ih]

private theorem DetDLP.w3_bitfold (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => rw [Nat.bits_append_bit _ _ h,List.foldr_cons,ih]

private theorem DetDLP.w3_countfold (n : ℕ) : (countWord n).foldr Nat.bit 0 = n := by
  by_cases h : n = 0
  · subst n; rfl
  · simpa [countWord,h] using w3_bitfold n

private def DetDLP.w3_threeNat (w : List Bool) : ℕ × ℕ × ℕ :=
  let a := w3_unframe w.tail; let b := w3_unframe a.2.tail; let c := w3_unframe b.2.tail
  (a.1.foldr Nat.bit 0,b.1.foldr Nat.bit 0,c.1.foldr Nat.bit 0)

private theorem DetDLP.w3_threeNat_spec (p g a : ℕ) : w3_threeNat (encodeFpDLPInput p g a) = (p,g,a) := by
  simp [w3_threeNat,encodeFpDLPInput,encodeNatListBin,Encoding.encodeList,w3_unframe_spec,w3_countfold]

private noncomputable def DetDLP.w3_scanWord (w : List Bool) : List Bool :=
  let (p,g,a) := w3_threeNat w
  countWord (((List.range (p-1)).find? (fun j => decide (g^j % p = a))).getD 0)

private theorem DetDLP.w3_scan_ex {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V]
    {M : ℕ} [NeZero M] (P Q : V) (hcard : Nat.card V = M) (hg : addOrderOf P = M) :
    ∃ u, (List.range M).find? (fun j => decide (j • P = Q)) = some u := by
  have ht : AddSubgroup.zmultiples P = ⊤ := (AddSubgroup.zmultiples P).eq_top_of_card_eq
    ((Nat.card_zmultiples P).trans (hg.trans hcard.symm))
  have all (g : V) : g ∈ AddSubgroup.zmultiples P := by rw [ht]; trivial
  let e := (zmodAddEquivOfGenerator all hcard).symm
  have he : e P = 1 := zmodAddEquivOfGenerator_symm_apply_generator all hcard
  have hu : (e Q).val • P = Q := by apply e.injective; simp [he,nsmul_eq_mul,ZMod.natCast_zmod_val]
  cases h : (List.range M).find? (fun j => decide (j • P = Q)) with
  | some u => exact ⟨u,rfl⟩
  | none => have z := List.find?_eq_none.mp h _ (List.mem_range.mpr (e Q).val_lt); simp [hu] at z

private theorem DetDLP.w3_frame_len (w : List Bool) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => change (Encoding.frame w).length+1+1 = 2*(w.length+1)+1; omega

private theorem DetDLP.w3_count_len (n : ℕ) : (countWord n).length ≤ n+1 := by
  by_cases h : n = 0
  · simp [countWord,h]
  · simp only [countWord,if_neg h,Nat.size_eq_bits_len]; exact (Nat.size_le.mpr n.lt_two_pow_self).trans (Nat.le_succ _)

private theorem DetDLP.w3_fixed_cost (T : ℕ) : ∃ C, ∀ b : ℕ, 1 ≤ b → b ≤ 32 →
    (T : ℝ) ≤ mainTimeBound C b ∧ (T : ℝ) ≤ mainSpaceBound C b := by
  classical
  let d := fun b : ℕ => max (Real.sqrt (logLogSafe b)) ((logSafe b)^((1:ℝ)/4))
  let c := fun b : ℕ => ⌈(T:ℝ)*d b⌉₊
  let C := (Finset.range 33).sup c
  refine ⟨C,fun b hb hb' => ?_⟩
  have hc : c b ≤ C := Finset.le_sup (f := c) (Finset.mem_range.mpr (by omega))
  have hprod : (T:ℝ)*d b ≤ C := (Nat.le_ceil _).trans (by exact_mod_cast hc)
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hCb : (C:ℝ) ≤ C*b := by simpa using mul_le_mul_of_nonneg_left hbR (Nat.cast_nonneg C)
  have hbase : (T:ℝ) ≤ (2:ℝ)^(T:ℝ) := by rw [Real.rpow_natCast]; exact_mod_cast (Nat.lt_two_pow_self (n := T)).le
  have hl : (0:ℝ) < logSafe b := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have hll : (0:ℝ) < logLogSafe b := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  constructor
  · refine hbase.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ((le_div_iff₀ (Real.sqrt_pos.2 hll)).mpr ?_))
    exact (mul_le_mul_of_nonneg_left (le_max_left ..) (Nat.cast_nonneg T)).trans (hprod.trans hCb)
  · refine hbase.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ((le_div_iff₀ (Real.rpow_pos_of_pos hl _)).mpr ?_))
    exact (mul_le_mul_of_nonneg_left (le_max_right ..) (Nat.cast_nonneg T)).trans (hprod.trans hCb)

theorem solution : ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
    ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ), orderOf h = p-1 → ¬w3_large p (p-1) →
      w3_scanOutput (p-1) (Additive.ofMul h) (Additive.ofMul a) (fun u => RunsWithin D out
        (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val) (countWord u)
        (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))) := by
  classical
  let H : ℕ := 2^32; let L := 10*(H+2); let T := 100*(L+H+20)
  obtain ⟨D,out,hr⟩ := w3_bounded_word_machine L w3_scanWord
  obtain ⟨C,hC⟩ := w3_fixed_cost T
  refine ⟨D,out,C,?_⟩
  intro p hp h a hg hs
  have hpH : p ≤ H := w3_small_prime_bound.1 p hs
  letI : NeZero (p-1) := ⟨by have := hp.out.one_lt; omega⟩
  have hcard : Nat.card (Additive (ZMod p)ˣ) = p-1 := by change Nat.card (ZMod p)ˣ = p-1; rw [Nat.card_eq_fintype_card,ZMod.card_units]
  obtain ⟨u,hu⟩ := w3_scan_ex (Additive.ofMul h) (Additive.ofMul a) hcard hg
  refine ⟨u,hu,?_⟩
  have huM := List.mem_range.mp (List.mem_of_find?_eq_some hu)
  let w := encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val
  have he (j : ℕ) : ((h : ZMod p).val^j%p = (a : ZMod p).val) ↔ j • Additive.ofMul h = Additive.ofMul a := by
    change _ ↔ h^j = a
    rw [←Units.val_inj, ← (ZMod.val_injective p).eq_iff,Units.val_pow_eq_pow_val]
    have hj : ((h : ZMod p)^j).val = (h : ZMod p).val^j % p := by
      calc _ = (((((h : ZMod p).val^j : ℕ) : ZMod p))).val := by simp
           _ = _ := ZMod.val_natCast _ _
    rw [hj]
  have hf : w3_scanWord w = countWord u := by
    simp only [w3_scanWord,w,w3_threeNat_spec,he,hu,Option.getD_some]
  have hw : w.length ≤ L := by
    simp only [w,encodeFpDLPInput,encodeNatListBin,Encoding.encodeList,List.length_cons,List.length_append,List.length_nil,w3_frame_len]
    dsimp [L]; have := w3_count_len p; have := w3_count_len (h:ZMod p).val; have := w3_count_len (a:ZMod p).val
    have := (h:ZMod p).val_lt; have := (a:ZMod p).val_lt; omega
  have hrun := hr w hw
  rw [hf] at hrun
  have hub := w3_count_len u
  obtain ⟨ht,hsp⟩ := hC (bitLen p) (Nat.clog_pos (by decide) hp.out.one_lt) (Nat.clog_le_of_le_pow hpH)
  apply PolyTBridge.runsWithin_mono_local hrun
  · exact le_trans (by exact_mod_cast (show 7*(3*L+2*(countWord u).length+1) ≤ T by dsimp [T]; omega)) ht
  · exact le_trans (by exact_mod_cast (show 2*L+(3*L+2*(countWord u).length+1)+15 ≤ T by dsimp [T]; omega)) hsp
