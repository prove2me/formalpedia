-- Prove2me | solution 1 for BCFGJPSSV26.Stable.exists_accN_inO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:02:54.869197+00:00
-- url     : https://prove2.me/submissions/711933da-16a0-4992-9a6f-51cc2337d29b

module

public import Definitions.Def_BuhaiPapers_Background_BlackBox
public import Definitions.Def_BuhaiPapers_Background_Encoding
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Rat.Floor
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Accuracy
import all Definitions.Def_BCFGJPSSV26_Stable_Time_Accuracy

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Turing.MultiTapeTM
open Encoding (encRat)

/-- **Computing `N` from `ε`**, in time linear in the encoding of `ε` plus a polynomial in `N`. -/
theorem exists_accN_inO : ∃ D : ℕ, ComputableInO accN encRat encUnary
    (fun ε ↦ (encRat ε).length + accN ε ^ D) (fun ε ↦ (encRat ε).length + accN ε ^ D) := by
  set L : ℚ → ℕ := fun ε ↦ (encRat ε).length
  have hnd : ComputableInO (fun ε : ℚ ↦ (ε.num, ε.den)) encRat
      (encPair Encoding.encInt encNat) L L :=
    ComputableInO.of_eq fun _ ↦ rfl
  have hnum : ComputableInO (fun ε : ℚ ↦ Encoding.encInt ε.num) encRat encBits L L :=
    (ComputableInO.of_eq (encIn := Encoding.encInt) (encMid := encBits)
      (f := fun z ↦ Encoding.encInt z)
      fun _ ↦ rfl).comp_linear ((ComputableInO.fst Encoding.encInt encNat).comp_linear hnd)
  have hden : ComputableInO (fun ε : ℚ ↦ encNat ε.den) encRat encBits L L :=
    (ComputableInO.of_eq (encIn := encNat) (encMid := encBits) (f := fun n ↦ encNat n)
      fun _ ↦ rfl).comp_linear ((ComputableInO.snd Encoding.encInt encNat).comp_linear hnd)
  have hmapE := Universal.computableTidilyInDegree_map_eBit.inO_one.computableInO
  have hsgn : ComputableInO sgnBit encRat encUnary L L :=
    (ComputableInO.headD' (enc := encUnary) 0).comp_linear (hmapE.comp_linear hnum)
  have hc : ComputableInO (fun ε ↦ decide (sgnBit ε = 0)) encRat encBool L L :=
    ComputableTidilyInDegree.unary_isZero.inO_one.computableInO.comp_linear hsgn
  have hlen : ComputableInO (fun ε : ℚ ↦ (Encoding.encInt ε.num).length) encRat encUnary L L :=
    ComputableInO.lengthUnary.comp_linear hnum
  have hdrop := ComputableInO.drop' (hmapE.comp_linear hden) hlen
  have hdrop' : ComputableInO (fun ε : ℚ ↦
      ((encNat ε.den).map Universal.eBit).drop (Encoding.encInt ε.num).length) encRat
      (encList encUnary) L L := by
    refine hdrop.mono 8 (fun ε ↦ ?_) (fun ε ↦ ?_)
    all_goals
      simp only [L, length_encPair, encUnary_apply, List.length_replicate, Function.comp_apply]
      have h1 : (encList encUnary ((encNat ε.den).map Universal.eBit)).length ≤
          3 * (encNat ε.den).length := by
        refine (length_encList_unary_le fun c hc ↦ ?_).trans (by rw [List.length_map])
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc
        exact eBit_le_one b
      have h2 : (encRat ε).length =
          2 * (Encoding.encInt ε.num).length + 1 + (encNat ε.den).length :=
        length_encPair (enc₁ := Encoding.encInt) (enc₂ := encNat) (ε.num, ε.den)
      omega
  have hgap : ComputableInO gapList encRat (encList encUnary) L L := by
    refine (ComputableInO.iteDecide hc hdrop' (ComputableInO.const [])).mono 3
      (fun ε ↦ ?_) (fun ε ↦ ?_) <;>
    · split_ifs <;> simp only [L] <;> omega
  -- `2^(g + 8)` from the list
  obtain ⟨c, d, hpow⟩ := exists_inO_pow (ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.length_list encUnary) (ComputableInPolyTime.const (encIn :=
      encList encUnary) 8))
  have h := (ComputableInO.unary_two_pow.comp' hpow).comp' hgap
  have hb : ∀ ε, L ε + (c * ((encList encUnary (gapList ε)).length + 1) ^ d +
      ((gapList ε).length + 8 + 1) * 2 ^ ((gapList ε).length + 8)) ≤
      (2 + c * 3 ^ d) * (L ε + accN ε ^ (d + 2) + 1) := by
    intro ε
    set g := (gapList ε).length
    set N := accN ε with hN
    have hN1 : 1 ≤ N := (le_accN ε).trans' (by norm_num)
    have hgN : g + 9 ≤ N := by
      have := Nat.lt_two_pow_self (n := g + 8)
      have hN' : N = 2 ^ (g + 8) := rfl
      omega
    have hl : (encList encUnary (gapList ε)).length + 1 ≤ 3 * N := by
      have := length_encList_unary_le (gapList_le_one ε)
      omega
    have h1 : ((encList encUnary (gapList ε)).length + 1) ^ d ≤ 3 ^ d * N ^ (d + 2) :=
      calc _ ≤ (3 * N) ^ d := Nat.pow_le_pow_left hl _
        _ = 3 ^ d * N ^ d := mul_pow _ _ _
        _ ≤ 3 ^ d * N ^ (d + 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN1 (by omega))
    have h2 : (g + 8 + 1) * 2 ^ (g + 8) ≤ N ^ (d + 2) :=
      calc (g + 8 + 1) * 2 ^ (g + 8) ≤ N * N := Nat.mul_le_mul (by omega) le_rfl
        _ = N ^ 2 := (sq N).symm
        _ ≤ N ^ (d + 2) := Nat.pow_le_pow_right hN1 (by omega)
    have h3 : c * ((encList encUnary (gapList ε)).length + 1) ^ d ≤ c * 3 ^ d * N ^ (d + 2) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left c h1
    generalize c * ((encList encUnary (gapList ε)).length + 1) ^ d = X at h3 ⊢
    generalize (g + 8 + 1) * 2 ^ (g + 8) = Y at h2 ⊢
    generalize N ^ (d + 2) = P at h2 h3 ⊢
    generalize c * 3 ^ d = Q at h3 ⊢
    nlinarith [Nat.zero_le (Q * L ε), Nat.zero_le Q]
  refine ⟨d + 2, ?_⟩
  refine h.mono _ hb fun ε ↦ (hb ε).trans' ?_
  have : 2 ^ ((gapList ε).length + 8) ≤ ((gapList ε).length + 8 + 1) *
      2 ^ ((gapList ε).length + 8) := Nat.le_mul_of_pos_left _ (by omega)
  omega

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.exists_accN_inO := @BCFGJPSSV26.Stable.exists_accN_inO
