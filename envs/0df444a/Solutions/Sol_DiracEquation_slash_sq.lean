-- Prove2me | solution 1 for DiracEquation.slash_sq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:18:24.711609+00:00
-- url     : https://prove2.me/submissions/a491c063-f40f-452f-8cfe-caf37e61b8ce

import Definitions.Def_DiracEquation_fields

open DiracEquation

namespace Ag1Aux_DiracSlash

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

end Ag1Aux_DiracSlash

open Ag1Aux_DiracSlash

theorem solution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g) (p : Fin 4 → ℂ) :
    slash g p * slash g p = (∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  slash_sq_core g hg p
