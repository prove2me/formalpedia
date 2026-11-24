-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_sub_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:59.485856+00:00
-- url     : https://prove2.me/submissions/bbdfdd31-ce29-408c-951d-0b39307e5e39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_mem_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_sub_aeval_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_sub_mem_sq

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
variable {σ τ : Type}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) : ∀ (k : ℕ) (p : MvPolynomial σ S), p ∈ Io S σ ^ k →
    aeval g p - aeval g' p ∈ Io S τ ^ (k + 1)
  | 0, p, _ => by simpa using aeval_sub_aeval_mem g g' hg hg' p
  | k + 1, p, hp => by
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on (C := fun p => aeval g p - aeval g' p ∈ Io S τ ^ (k + 1 + 1)) hp ?_ ?_
    · intro a ha b hb
      have e : aeval g (a * b) - aeval g' (a * b) =
          (aeval g a - aeval g' a) * aeval g b + aeval g' a * (aeval g b - aeval g' b) := by
        simp only [map_mul]; ring
      rw [e]
      refine add_mem ?_ ?_
      · rw [pow_succ]
        have hb1 : b ∈ Io S σ ^ 1 := by simpa using hb
        exact Ideal.mul_mem_mul (solution g g' hg hg' hgg k a ha)
          (by simpa using aeval_mem_pow g hg 1 hb1)
      · have e2 : Io S τ ^ (k + 1 + 1) = Io S τ ^ k * Io S τ ^ 2 := by rw [← pow_add]
        rw [e2]
        exact Ideal.mul_mem_mul (aeval_mem_pow g' hg' k ha) (aeval_sub_mem_sq g g' hg hg' hgg hb)
    · intro x y hx hy
      have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
        simp only [map_add]; ring
      rw [e]; exact add_mem hx hy
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
