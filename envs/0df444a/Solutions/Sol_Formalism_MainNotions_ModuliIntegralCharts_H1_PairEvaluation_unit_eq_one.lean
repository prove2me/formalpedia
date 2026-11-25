-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:48.212972+00:00
-- url     : https://prove2.me/submissions/ecd0fb1d-52d6-4b4d-aed4-05060495880b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eval_pair_sub
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_mem_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_sub_C_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_xs_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_lin_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
open MvPolynomial
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A 0 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab 1 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (aW : Fin d → MvPolynomial (Fin 1 × Fin d) S) (hW : ∀ i, aW i - lin A 0 i ∈ Io S (Fin 1 × Fin d) ^ 2)
    (hdiag : ev2 P (xs S d 0) aW - 1 ∈ Io S (Fin 1 × Fin d) ^ (m + 1)) :
    P - 1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1) := by
  have hbase : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 1 := by
    have haW : ∀ i, aW i ∈ Io S _ := fun i => by
      have := add_mem (Ideal.pow_le_self two_ne_zero (hW i)) (lin_mem A 0 i); simpa using this
    set c := coeff 0 P with hcdef
    have h1 : ev2 (P - C c) (xs S d (0 : Fin 1)) aW ∈ Io S _ := by
      have h0 : P - C c ∈ Io S (Fin 2 × Fin d) ^ 1 := by simpa using sub_C_mem P
      have := aeval_mem_pow (fun p : Fin 2 × Fin d => ![xs S d (0 : Fin 1), aW] p.1 p.2)
        (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [xs_mem, haW]) 1 h0
      rw [pow_one] at this
      exact this
    have e : ev2 P (xs S d (0 : Fin 1)) aW = ev2 (P - C c) (xs S d (0 : Fin 1)) aW + C c := by
      rw [eval_pair_sub]; simp [ev2]
    have h3 : C (c - 1) ∈ Io S (Fin 1 × Fin d) := by
      have := sub_mem (Ideal.pow_le_self (by omega : m + 1 ≠ 0) hdiag) h1
      have e2 : ev2 P (xs S d (0 : Fin 1)) aW - 1 - ev2 (P - C c) (xs S d (0 : Fin 1)) aW = C (c - 1) := by
        rw [e, map_sub, map_one]; ring
      rw [e2] at this; exact this
    have hc : c - 1 = 0 := by
      have := (C_mem_pow_idealOfVars_iff 1 (c - 1)).1 (by rw [pow_one]; exact h3)
      simpa using this
    have hc1 : c = 1 := by linear_combination hc
    have : P - 1 = P - C c := by rw [hc1, map_one]
    rw [this, pow_one]; exact sub_C_mem P
  have key : ∀ j, 1 ≤ j → j ≤ m + 1 → P - 1 ∈ Io S (Fin 2 × Fin d) ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact hbase
    | succ n hn ih =>
      intro hn'
      exact step hn (by omega) fF hF hph1 hsym A Ab hAA aW0 aB1 hW0 hB1 hbal aW hW hdiag (ih (by omega))
  exact key (m + 1) (by omega) le_rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
