-- Prove2me | solution 1 for BBBV.RandomPermutation.prob_membership_differs
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T06:37:01.038739+00:00
-- url     : https://prove2.me/submissions/65b6b053-609a-4212-904f-fc055a7e6e7e

import Definitions.Def_BBBV_RandomPermutation_Chain

noncomputable section
open Classical Finset BBBV.RandomPermutation
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace WentaoBBBVBit

private lemma chain_key {n T : ℕ} (ω : Ω n T) (i : ℕ) :
    piChain ω i (x ω i) = BBBV.RandomOracle.ones n := by
  induction i with
  | zero => exact ω.1.apply_symm_apply _
  | succ i ih =>
    change piChain ω i (Equiv.swap (x ω i) (x ω (i + 1)) (x ω (i + 1))) = _
    simpa using ih

private lemma key_inv {n T : ℕ} (ω : Ω n T) (i : ℕ) :
    (piChain ω i).symm (BBBV.RandomOracle.ones n) = x ω i := by
  rw [← chain_key ω i, Equiv.symm_apply_apply]

private lemma x_positive {n T : ℕ} (ω : Ω n T) (i : ℕ)
    (hi0 : 0 < i) (hi : i ≤ T + 1) :
    x ω i = ω.2 ⟨i - 1, by omega⟩ := by
  cases i with
  | zero => omega
  | succ i => simp [x, show i < T + 1 by omega]

private lemma flip_bit (a b : ZMod 2) :
    (((a + 1 = 1) ↔ ¬ (b = 1)) ↔ ¬ ((a = 1) ↔ ¬ (b = 1))) := by
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hb : b = 0 ∨ b = 1 := by
    fin_cases b <;> first | exact Or.inl rfl | exact Or.inr rfl
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num <;>
    simpa only [htwo] using (zero_ne_one : (0 : ZMod 2) ≠ 1)

end WentaoBBBVBit

open WentaoBBBVBit

theorem solution {n T : ℕ} (hn : 0 < n) (hT : 1 ≤ T) :
    ((Finset.univ.filter fun ω : Ω n T =>
      (firstBit hn ((piChain ω T).symm (BBBV.RandomOracle.ones n)) = 1) ↔
        ¬ (firstBit hn ((piChain ω (T - 1)).symm (BBBV.RandomOracle.ones n)) = 1)).card : ℝ) /
      (Fintype.card (Ω n T) : ℝ) = 1 / 2 := by
  classical
  let P : Ω n T → Prop := fun ω =>
    (firstBit hn ((piChain ω T).symm (BBBV.RandomOracle.ones n)) = 1) ↔
      ¬ (firstBit hn ((piChain ω (T - 1)).symm (BBBV.RandomOracle.ones n)) = 1)
  let a : Fin (T + 1) := ⟨T - 1, by omega⟩
  let e : Ω n T ≃ Ω n T := Equiv.prodCongr (Equiv.refl _)
    (Equiv.addRight (Pi.single a (BBBV.RandomOracle.ones n)))
  have hxT (ω : Ω n T) : x (e ω) T = x ω T + BBBV.RandomOracle.ones n := by
    rw [x_positive (e ω) T (by omega) (by omega),
      x_positive ω T (by omega) (by omega)]
    simp [e, a, Pi.single_apply]
  have hxprev (ω : Ω n T) : x (e ω) (T - 1) = x ω (T - 1) := by
    by_cases ht1 : T = 1
    · subst T; rfl
    · have hpos : 0 < T - 1 := by omega
      rw [x_positive (e ω) (T - 1) hpos (by omega),
        x_positive ω (T - 1) hpos (by omega)]
      have hba : (⟨T - 1 - 1, by omega⟩ : Fin (T + 1)) ≠ a := by
        intro h
        have hh := congrArg Fin.val h
        dsimp [a] at hh
        omega
      simp [e, Pi.single_apply, hba]
  have hflip (ω : Ω n T) : P (e ω) ↔ ¬ P ω := by
    dsimp [P]
    simp_rw [key_inv]
    rw [hxT, hxprev]
    simpa only [firstBit, Pi.add_apply, BBBV.RandomOracle.ones] using
      flip_bit (firstBit hn (x ω T)) (firstBit hn (x ω (T - 1)))
  have hcard : (univ.filter fun ω : Ω n T => ¬ P ω).card = (univ.filter P).card := by
    let ep : {ω : Ω n T // ¬ P ω} ≃ {ω : Ω n T // P ω} :=
      e.subtypeEquiv (fun ω => (hflip ω).symm)
    simpa only [Fintype.card_subtype] using Fintype.card_congr ep
  have hpart := card_filter_add_card_filter_not (s := (univ : Finset (Ω n T))) P
  rw [hcard] at hpart
  simp only [card_univ] at hpart
  have hΩ : (0 : ℝ) < Fintype.card (Ω n T) := by exact_mod_cast Fintype.card_pos
  change ((univ.filter P).card : ℝ) / (Fintype.card (Ω n T) : ℝ) = 1 / 2
  apply (div_eq_iff hΩ.ne').mpr
  have hpartR : ((univ.filter P).card : ℝ) + (univ.filter P).card =
      Fintype.card (Ω n T) := by exact_mod_cast hpart
  linarith
