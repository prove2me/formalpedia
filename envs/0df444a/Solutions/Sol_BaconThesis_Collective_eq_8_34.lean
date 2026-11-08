-- Prove2me | solution 1 for BaconThesis.Collective.eq_8_34
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:45:30.387942+00:00
-- url     : https://prove2.me/submissions/41a11690-5d78-43ab-9b56-9776403f7e8f

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_hammingWeight

open scoped Matrix

open BaconThesis.Collective in
theorem solution (n : ℕ) (x : Fin n → Fin 2) :
    collS n .z *ᵥ Pi.single x (1 : ℂ) =
      (((n : ℂ) - 2 * (hammingWeight x : ℂ)) / 2) • Pi.single x (1 : ℂ) := by
  have hdiag : ∀ b : Fin 2, BBPSSW.Distill.pauli .z b b = 1 - 2 * (if b = 1 then 1 else 0) := by
    intro b; fin_cases b <;> simp [BBPSSW.Distill.pauli] <;> norm_num
  have hoff : ∀ b c : Fin 2, b ≠ c → BBPSSW.Distill.pauli .z b c = 0 := by
    intro b c h; fin_cases b <;> fin_cases c <;> simp [BBPSSW.Distill.pauli] at h ⊢
  rw [Matrix.mulVec_single_one]
  ext y
  rw [Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
  unfold collS
  rw [Matrix.sum_apply]
  by_cases hxy : y = x
  · subst hxy
    rw [Pi.single_eq_same, mul_one]
    have hterm : ∀ i : Fin n, ((1 / 2 : ℂ) • onQubit i (BBPSSW.Distill.pauli .z)) y y
        = (1 / 2) * (1 - 2 * (if y i = 1 then 1 else 0)) := by
      intro i
      rw [Matrix.smul_apply, smul_eq_mul]
      unfold onQubit
      rw [if_pos (fun _ _ => rfl), hdiag]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_boole]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold hammingWeight
    ring
  · rw [Pi.single_eq_of_ne hxy, mul_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
    unfold onQubit
    split_ifs with h
    · have hi : y i ≠ x i := by
        intro hyi
        apply hxy
        funext k
        by_cases hk : k = i
        · rw [hk]; exact hyi
        · exact h k hk
      rw [hoff _ _ hi, mul_zero]
    · rw [mul_zero]
