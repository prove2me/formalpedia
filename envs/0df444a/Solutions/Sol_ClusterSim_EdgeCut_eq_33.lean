-- Prove2me | solution 1 for ClusterSim.EdgeCut.eq_33
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:08:33.573574+00:00
-- url     : https://prove2.me/submissions/eb4f885b-d17e-42fd-a08f-f3e58b5dcecc

import Definitions.Def_ClusterSim_EdgeCut_Cut
import Theorems.Thm_ClusterSim_EdgeCut_eqs_31_32

open ClusterSim.EdgeCut

private lemma abs_coef (i : Fin 8) : |coef i| = 1 / 2 := by
  fin_cases i <;> norm_num [coef]

theorem solution (G : TensorNetwork) (C : Finset G.E) :
    value G = ∑ s : C → Fin 8,
        ((8 : ℂ) ^ C.card)⁻¹ * ((8 : ℂ) ^ C.card * (coefS s : ℂ) * value (cut G C s)) ∧
      ∀ s : C → Fin 8, |coefS s| = 1 / 2 ^ C.card := by
  constructor
  · rw [eqs_31_32 G C]
    apply Finset.sum_congr rfl
    intro s _
    have h8 : (8 : ℂ) ^ C.card ≠ 0 := pow_ne_zero C.card (by norm_num)
    rw [mul_assoc ((8 : ℂ) ^ C.card), inv_mul_cancel_left₀ h8]
  · intro s
    unfold coefS
    rw [Finset.abs_prod]
    have hconst : (∏ x : C, |coef (s x)|) = ∏ _x : C, (1 / 2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro x _
      exact abs_coef (s x)
    rw [hconst, Finset.prod_const, Finset.card_univ, Fintype.card_coe, one_div_pow]
