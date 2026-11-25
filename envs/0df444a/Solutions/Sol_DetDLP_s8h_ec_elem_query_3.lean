-- Prove2me | solution 3 for DetDLP.s8h_ec_elem_query
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T02:46:24.89807+00:00
-- url     : https://prove2.me/submissions/b2eb4cfa-49b8-4d53-a2a1-3fb5aace8b4b

import Definitions.Def_DetDLP_S8H4_ElemMake
import Definitions.Def_DetDLP_S8H4_PortEval
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open DetDLP DetDLP.M89S1 DetDLP.S8C DetDLP.S8H0 DetDLP.S8H4
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
namespace ElemProof
variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
private theorem listLen (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ p) :
    (encodeNatListBin xs).length ≤ xs.length*(2*bitLen p+4)+1 := by
  induction xs with
  | nil => simp [encodeNatListBin,Encoding.encodeList]
  | cons x xs ih =>
    have h1 := S8G.FpMoment.binaryLen (h x List.mem_cons_self)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [encodeNatListBin,Encoding.encodeList,List.length_cons,List.length_append,w3_frameLength,Nat.succ_mul] at *
    omega

private theorem budgets {T : ℕ} (S : ECSeed p (blockCount (bitLen p))) (i : Fin (blockCount (bitLen p))) (η : List Bool) (hT : T ≤ p) (hη : η.length ≤ 2*bitLen p+1) :
    let b := bitLen p; let m := blockCount b; let w := ElemDecoder.word E T S i η
    OrderPacket.scale b+w.length ≤ OrderPacket.constant*m*b ∧ OrderPacket.scale b+w.length ≤ OrderPacket.constant*(b+1)^OrderPacket.constant := by
  dsimp only; let b := bitLen p; let m := blockCount b
  have hm : 2 ≤ m := le_max_left ..
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have hc : (encodeCurveInput p E).length ≤ 6*(2*b+4)+1 := by
    apply listLen; simp only [List.mem_cons,List.not_mem_nil,or_false]; rintro x (rfl|rfl|rfl|rfl|rfl|rfl) <;> first | exact le_rfl | exact (ZMod.val_lt _).le
  have ht : (countWord T).length ≤ b+1 := S8G.FpMoment.binaryLen hT
  have hi := w3_queryIndexLength i.val; have him : i.val < m := i.isLt
  have hmb : b ≤ m*b := Nat.le_mul_of_pos_left _ (by omega)
  have hmb' : m ≤ m*b := Nat.le_mul_of_pos_right _ hb
  have h4 : (countWord 4).length = 3 := by decide
  have hw : (ElemDecoder.word E T S i η).length ≤ 256*(m*b) := by
    simp only [ElemDecoder.word,queryWord,Encoding.encodeList,id_eq,List.length_cons,List.length_append,w3_frameLength,List.length_nil,h4,List.length_ofFn]
    rw [show blockCount (bitLen p)*4*bitLen p = 4*(m*b) by change m*4*b = 4*(m*b); ring]; change η.length ≤ 2*b+1 at hη; omega
  have hf : OrderPacket.scale b+(ElemDecoder.word E T S i η).length ≤ OrderPacket.constant*(m*b) := by unfold OrderPacket.scale OrderPacket.constant; omega
  refine ⟨by simpa only [Nat.mul_assoc] using hf,hf.trans (Nat.mul_le_mul_left _ ?_)⟩
  calc m*b ≤ (b+2)*b := Nat.mul_le_mul_right _ (S8G.FpMoment.blockUpper b)
       _ ≤ (b+1)^2 := by nlinarith
       _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

theorem realizes [E.IsElliptic] (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (i : Fin (blockCount (bitLen p))) (η : List Bool) (hT : T ≤ p) (hη : η.length ≤ 2*bitLen p+1) :
    Realizes ElemMake.make DetDLP.S8H4.PortEval.port OrderPacket.constant (ElemDecoder.word E T S i η) (bitLen p) (elemCount (ecFactorBlock E T S i) (ecWord (bitLen p)) η) := by
  letI := ecPointFintype E
  let a := (S i false).1.val+1; let c := (S i false).2.val
  let a' := (S i true).1.val+1; let c' := (S i true).2.val
  let A := Semantics.layout p T a c a' c' (GateSemantics.coeff E) η
  let t := Semantics.tests p T a c a' c' (GateSemantics.coeff E) η
  let b := bitLen p; let s := OrderPacket.scale b; let w := ElemDecoder.word E T S i η
  have cnt : Fintype.card {P : E.toAffine.Point // S8H.ECPointGadget.elemPin b T S i η P = true} = elemCount (ecFactorBlock E T S i) (ecWord b) η := by
    rw [Fintype.card_subtype]; simp [elemCount,ecFactorBlock,S8H.ECPointGadget.elemPin,Finset.filter_filter]
  have hs : b+2 ≤ s := Nat.le_mul_of_pos_left _ (by decide)
  have hg : A.ng ≤ s := Semantics.gateBudget p T a c a' c' (GateSemantics.coeff E) η hη
  have edges : 2*A.ne < s := Semantics.edgeBudget p T a c a' c' (GateSemantics.coeff E) η hη
  have hn : A.nb ≤ A.ne := by simpa using Fintype.card_le_of_injective A.rep (Function.RightInverse.injective A.rep_bit)
  have hv : A.ng+A.nb+A.ne ≤ 2*s := by omega
  have wb := budgets E S i η hT hη
  rw [← cnt]; apply wireRealizes ElemMake.make DetDLP.S8H4.PortEval.port OrderPacket.constant s b w (w3_factorGraph A) (w3_factorChecks A t) ((w3_factorEquiv A t).trans (Semantics.points hT S i η)) (by omega) (by omega) edges
  · change A.ng+A.nb+A.ne ≤ s^OrderPacket.constant
    calc _ ≤ s^2 := by nlinarith
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  · apply (max_le (Finset.sup_le (fun v _ => Semantics.degree p T a c a' c' (GateSemantics.coeff E) η v)) (le_trans (by decide : 2 ≤ 12) (le_max_left _ _))).trans (OrderPacket.degreeBudget b)
  · exact wb.1
  · exact wb.2
  · exact ElemMake.make_word E T S i η hη
  · intro v av; refine ⟨?_,DetDLP.S8H4.PortEval.port_eval E T S i η v av⟩
    have hi : v.val < 2*s := v.isLt.trans_le hv
    have hd : ((w3_factorGraph A).subdivision.deg v) ≤ 2*A.ne := (List.length_filter_le ..).trans (List.length_finRange.le.trans ((w3_factorGraph A).subdivision_nE.le))
    have hc := w3_queryIndexLength v.val
    rw [w3_queryExactLength,List.length_ofFn]
    calc _ ≤ 16*(s+w.length+1) := by omega
         _ ≤ OrderPacket.constant*(s+w.length+1)^OrderPacket.constant := Nat.mul_le_mul (by decide) (Nat.le_self_pow (by decide : OrderPacket.constant ≠ 0) _)
theorem tagIntro (make port : List Bool → List Bool) (L : ℕ) (hm : Groundwork.PolyT make) (hp : Groundwork.PolyT port)
    (h : ∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (i : Fin (blockCount (bitLen p))) (η : List Bool), T ≤ p → η.length ≤ 2*bitLen p+1 → Realizes make port L (ElemDecoder.word E T S i η) (bitLen p) (elemCount (ecFactorBlock E T S i) (ecWord (bitLen p)) η)) : TagSpec [4] := by
  refine ⟨make,port,L,hm,hp,?_⟩
  rintro t ht base payload b n hq
  obtain rfl : t = 4 := by simpa using ht
  generalize hw : queryWord 4 base payload = w at hq ⊢
  have tag : Groundwork.PolyT.bval (DetDLP_W1_Queries.first w) = 4 := by subst w; simp [queryWord]
  cases hq <;> simp only [queryWord,DetDLP_W1_Queries.first_cons,id_eq,DetDLP_W1_Queries.decode_count] at tag
  all_goals first | contradiction | exact h _ _ _ _ _ _ (by assumption) (by assumption)
end ElemProof

theorem solution : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [4] := by
  intro _
  apply ElemProof.tagIntro ElemMake.make DetDLP.S8H4.PortEval.port OrderPacket.constant
  · exact ElemMake.make_poly
  · exact DetDLP.S8H4.PortEval.port_poly
  · intro p hp E hE; exact ElemProof.realizes E
