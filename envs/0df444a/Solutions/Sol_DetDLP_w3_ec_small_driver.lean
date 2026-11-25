-- Prove2me | solution 1 for DetDLP.w3_ec_small_driver
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T00:43:33.772634+00:00
-- url     : https://prove2.me/submissions/d9196924-7a1f-4340-8c80-748cac1e892a

import Definitions.Def_DetDLP_W3_Driver
import Definitions.Def_DetDLP_PolyTBridge
import Theorems.Thm_DetDLP_w3_bounded_word_machine
import Theorems.Thm_DetDLP_w3_small_prime_bound

import Theorems.Thm_DetDLP_hasse_ec_point_count_bound

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

private def DetDLP.w3_readN : ℕ → List Bool → List ℕ
  | 0, _ => []
  | n+1, w => let q := w3_unframe w.tail; q.1.foldr Nat.bit 0 :: w3_readN n q.2

private theorem DetDLP.w3_readN_spec (l : List ℕ) : w3_readN l.length (encodeNatListBin l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons,w3_readN,encodeNatListBin,Encoding.encodeList,List.tail_cons,w3_unframe_spec,w3_countfold]
    exact congrArg (List.cons a) ih

private theorem DetDLP.w3_coords_len {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)} (P : E.toAffine.Point) :
    (pointCoords P).length = 3 := by cases P <;> rfl

private theorem DetDLP.w3_coords_inj {p : ℕ} [NeZero p] (E : WeierstrassCurve (ZMod p)) :
    Function.Injective (pointCoords (E := E)) := by
  intro X Y h
  cases X <;> cases Y <;> simp_all [pointCoords,(ZMod.val_injective p).eq_iff]

private noncomputable def DetDLP.w3_ecBody {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (tail : List ℕ) : List Bool := by
  classical
  letI := ecPointFintype E
  let P := Function.invFun (pointCoords (E := E)) (tail.take 3)
  let Q := Function.invFun (pointCoords (E := E)) (tail.drop 3)
  exact countWord (((List.range (Fintype.card E.toAffine.Point)).find? (fun j => decide (j • P = Q))).getD 0)

private noncomputable def DetDLP.w3_ecWord (w : List Bool) : List Bool := by
  classical
  exact match w3_readN 12 w with
  | p::a1::a2::a3::a4::a6::tail => if hp : p.Prime then
      letI : Fact p.Prime := ⟨hp⟩
      let E : WeierstrassCurve (ZMod p) := ⟨a1,a2,a3,a4,a6⟩
      w3_ecBody E tail
    else []
  | _ => []

private theorem DetDLP.w3_ecWord_spec (p : ℕ) [hp : Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (P Q : E.toAffine.Point) : letI := ecPointFintype E
    w3_ecWord (encodeECDLPInput p E P Q) = countWord (((List.range (Fintype.card E.toAffine.Point)).find?
      (fun j => decide (j • P = Q))).getD 0) := by
  classical
  let vals := [p,E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val] ++ pointCoords P ++ pointCoords Q
  have hv : vals.length = 12 := by simp [vals,w3_coords_len]
  have hh := w3_readN_spec vals; rw [hv] at hh
  unfold w3_ecWord; change w3_readN 12 (encodeECDLPInput p E P Q) = vals at hh
  rw [hh]; simp only [vals,List.cons_append,List.nil_append,dif_pos hp.out,ZMod.natCast_zmod_val]
  have htk : (pointCoords P ++ pointCoords Q).take 3 = pointCoords P := by conv_lhs => rw [←w3_coords_len P]; simp
  have hdr : (pointCoords P ++ pointCoords Q).drop 3 = pointCoords Q := by conv_lhs => rw [←w3_coords_len P]; simp


  simp only [w3_ecBody,htk,hdr,Function.leftInverse_invFun (w3_coords_inj E) P,Function.leftInverse_invFun (w3_coords_inj E) Q]

private theorem DetDLP.w3_encoded_len {H : ℕ} (l : List ℕ) (h : ∀ x ∈ l, x ≤ H) :
    (encodeNatListBin l).length ≤ l.length*(2*(H+1)+2)+1 := by
  induction l with
  | nil => simp [encodeNatListBin,Encoding.encodeList]
  | cons a l ih =>
    have hh := ih (fun x hx => h x (by simp [hx])); have ha := h a (by simp); have := w3_count_len a
    change (true::(Encoding.frame (countWord a) ++ encodeNatListBin l)).length ≤ _
    rw [List.length_cons,List.length_append,w3_frame_len,List.length_cons,Nat.add_mul]; omega

theorem solution : ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      letI := ecPointFintype E; let M := Fintype.card E.toAffine.Point
      ∀ P Q : E.toAffine.Point, addOrderOf P = M → ¬w3_large p M →
      w3_scanOutput M P Q (fun u => RunsWithin D out (encodeECDLPInput p E P Q) (countWord u)
        (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))) := by
  classical
  let H : ℕ := 2^32; let L := 25*(H+2); let T := 100*(L+4*H+20)
  obtain ⟨D,out,hr⟩ := w3_bounded_word_machine L w3_ecWord
  obtain ⟨C,hC⟩ := w3_fixed_cost T
  refine ⟨D,out,C,?_⟩
  intro p hp hp3 E hE
  letI := ecPointFintype E
  let M := Fintype.card E.toAffine.Point
  dsimp only; intro P Q hg hs
  have hpH : p ≤ H := w3_small_prime_bound.2 p hp3 E hs
  have hMpos : 0 < M := Fintype.card_pos
  letI : NeZero M := ⟨hMpos.ne'⟩
  obtain ⟨u,hu⟩ := w3_scan_ex (M := M) P Q Nat.card_eq_fintype_card hg
  refine ⟨u,hu,?_⟩
  have huM := List.mem_range.mp (List.mem_of_find?_eq_some hu)
  have hupper := (abs_le.mp (hasse_ec_point_count_bound p hp3 E)).2
  change (M:ℝ)-((p:ℝ)+1) ≤ 2*Real.sqrt (p:ℝ) at hupper
  have hMR : (M:ℝ) ≤ 2*(p:ℝ)+2 := by nlinarith [sq_nonneg (Real.sqrt (p:ℝ)-1),Real.sq_sqrt (Nat.cast_nonneg p)]
  have hMn : M ≤ 2*p+2 := by exact_mod_cast hMR
  let w := encodeECDLPInput p E P Q
  have hf : w3_ecWord w = countWord u := by dsimp only [w]; rw [w3_ecWord_spec]; simpa [M] using congrArg (fun o : Option ℕ => countWord (o.getD 0)) hu
  have coords (X : E.toAffine.Point) : ∀ x ∈ pointCoords X, x ≤ p := by
    cases X with
    | zero => simp [pointCoords]; omega
    | some x y _ => simp [pointCoords]; exact ⟨x.val_lt.le,y.val_lt.le⟩
  have hw : w.length ≤ L := by
    let l := [p,E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val] ++ pointCoords P ++ pointCoords Q
    have hl : l.length = 12 := by simp [l,w3_coords_len]
    have hh : ∀ x ∈ l, x ≤ H := by
      intro x hx; simp only [l,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with ((rfl|rfl|rfl|rfl|rfl|rfl)|h)|h
      · exact hpH
      all_goals first | exact (coords P _ h).trans hpH | exact (coords Q _ h).trans hpH | exact (ZMod.val_lt _).le.trans hpH
    have hz := w3_encoded_len l hh; rw [hl] at hz
    change (encodeNatListBin l).length ≤ L
    dsimp [L]; omega
  have hrun := hr w hw; rw [hf] at hrun
  have hub := w3_count_len u
  obtain ⟨ht,hsp⟩ := hC (bitLen p) (Nat.clog_pos (by decide) hp.out.one_lt) (Nat.clog_le_of_le_pow hpH)
  apply PolyTBridge.runsWithin_mono_local hrun
  · exact le_trans (by exact_mod_cast (show 7*(3*L+2*(countWord u).length+1) ≤ T by dsimp [T]; omega)) ht
  · exact le_trans (by exact_mod_cast (show 2*L+(3*L+2*(countWord u).length+1)+15 ≤ T by dsimp [T]; omega)) hsp

