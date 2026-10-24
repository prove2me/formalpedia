-- Prove2me | solution 1 for BellDetEff.TwoParty.eqs_13_14_witness
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:22:42.242612+00:00
-- url     : https://prove2.me/submissions/c594555e-35f9-479f-8838-5df14d93588b

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_BellInequality

namespace BellDetEff.TwoParty.WitnessProof

lemma fin_cast_injective {P : ℕ} : Function.Injective (fun a : Fin P => (a.val : ZMod P)) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using hv

lemma row_sum (P MA MB : ℕ) [NeZero P] (a : Fin P) (x : Fin MA) (y : Fin MB) :
    ∑ b, witnessBox P MA MB a b x y = 1 / (P : ℝ) := by
  classical
  let t : ZMod P := ((x.val + 1 : ℕ) : ZMod P) * ((y.val + 1 : ℕ) : ZMod P) - a.val
  let b₀ : Fin P := ⟨t.val, ZMod.val_lt t⟩
  have hb₀ : bellCong P a b₀ x y := by
    change (a.val : ZMod P) + (t.val : ZMod P) = _
    rw [ZMod.natCast_zmod_val]
    dsimp [t]
    ring
  have hiff (b : Fin P) : bellCong P a b x y ↔ b = b₀ := by
    constructor
    · intro hb
      exact fin_cast_injective (add_left_cancel (hb.trans hb₀.symm))
    · rintro rfl
      exact hb₀
  simp only [witnessBox, hiff]
  simp

lemma column_sum (P MA MB : ℕ) [NeZero P] (b : Fin P) (x : Fin MA) (y : Fin MB) :
    ∑ a, witnessBox P MA MB a b x y = 1 / (P : ℝ) := by
  classical
  let t : ZMod P := ((x.val + 1 : ℕ) : ZMod P) * ((y.val + 1 : ℕ) : ZMod P) - b.val
  let a₀ : Fin P := ⟨t.val, ZMod.val_lt t⟩
  have ha₀ : bellCong P a₀ b x y := by
    change (t.val : ZMod P) + (b.val : ZMod P) = _
    rw [ZMod.natCast_zmod_val]
    dsimp [t]
    ring
  have hiff (a : Fin P) : bellCong P a b x y ↔ a = a₀ := by
    constructor
    · intro ha
      exact fin_cast_injective (add_right_cancel (ha.trans ha₀.symm))
    · rintro rfl
      exact ha₀
  simp only [witnessBox, hiff]
  simp

end BellDetEff.TwoParty.WitnessProof

open BellDetEff.TwoParty

theorem solution (P MA MB : ℕ) [Fact P.Prime] :
    IsBehaviour (witnessBox P MA MB) ∧ NoSignaling (witnessBox P MA MB) ∧
      (∀ a x y, ∑ b, witnessBox P MA MB a b x y = 1 / (P : ℝ)) ∧
      (∀ b x y, ∑ a, witnessBox P MA MB a b x y = 1 / (P : ℝ)) := by
  have hP : P ≠ 0 := (Fact.out : P.Prime).ne_zero
  have hrows := WitnessProof.row_sum P MA MB
  have hcols := WitnessProof.column_sum P MA MB
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hrows, hcols⟩
  · intro a b x y
    unfold witnessBox
    split_ifs <;> positivity
  · intro x y
    simp only [hrows, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel (Nat.cast_ne_zero.mpr hP)
  · intro a x y y'
    rw [hrows, hrows]
  · intro b x x' y
    rw [hcols, hcols]
