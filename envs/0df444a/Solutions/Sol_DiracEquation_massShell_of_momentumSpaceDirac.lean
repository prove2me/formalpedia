-- Prove2me | solution 1 for DiracEquation.massShell_of_momentumSpaceDirac
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:18:37.594713+00:00
-- url     : https://prove2.me/submissions/4bf761da-6c95-41df-b1d1-822bd61f5775

import Definitions.Def_DiracEquation_fields

open DiracEquation

namespace Ag1Aux_DiracMass

theorem slash_sq_core (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (p : Fin 4 → ℂ) :
    slash g p * slash g p = (∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hg' : ∀ mu nu, g mu * g nu + g nu * g mu = (2 * eta mu nu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := hg
  set S := ∑ mu, ∑ nu, (p mu * p nu) • (g mu * g nu) with hS
  have e1 : slash g p * slash g p = S := by
    simp only [hS, slash, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    exact Finset.sum_comm
  have e2 : S = ∑ mu, ∑ nu, (p mu * p nu) • (g nu * g mu) := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun mu _ => Finset.sum_congr rfl (fun nu _ => ?_))
    rw [mul_comm]
  have key : S + S = (2 : ℂ) • ((∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    nth_rewrite 2 [e2]
    rw [hS, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, ← smul_add, hg']
    simp only [Fin.sum_univ_four, eta]
    simp only [smul_smul, Finset.smul_sum, Finset.sum_smul]
    simp
    module
  have h2 : (2 : ℂ) • S = (2 : ℂ) • ((∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    rw [two_smul]; exact key
  rw [e1]
  exact smul_right_injective _ (two_ne_zero) h2

end Ag1Aux_DiracMass

open Ag1Aux_DiracMass

theorem solution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : IsGammaFamily g) (m : ℝ) (p : Fin 4 → ℝ) (u : Fin 4 → ℂ) (hu0 : u ≠ 0)
    (hu : (slash g fun mu => (p mu : ℂ)).mulVec u + (m : ℂ) • u = 0) :
    ∑ mu, eta mu mu * (p mu : ℂ) ^ 2 = (m : ℂ) ^ 2 := by
  set s := slash g fun mu => (p mu : ℂ)
  have h1 : s.mulVec u = -((m : ℂ) • u) := eq_neg_of_add_eq_zero_left hu
  have h2 : (s * s).mulVec u = ((m : ℂ) ^ 2) • u := by
    rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_neg, Matrix.mulVec_smul, h1]
    rw [smul_neg, neg_neg, smul_smul, pow_two]
  rw [slash_sq_core g hg, Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  have h3 : ((∑ mu, eta mu mu * (p mu : ℂ) * (p mu : ℂ)) - (m : ℂ) ^ 2) • u = 0 := by
    rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.1 h3 with h | h
  · rw [← sub_eq_zero.1 h]
    exact Finset.sum_congr rfl (fun mu _ => by ring)
  · exact absurd h hu0
