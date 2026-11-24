-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_sub_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:00.104109+00:00
-- url     : https://prove2.me/submissions/b0040b38-daa1-455e-96c3-35eed718b647

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_mem_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_sub_aeval_mem

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
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) {p : MvPolynomial σ S} (hp : p ∈ Io S σ) :
    aeval g p - aeval g' p ∈ Io S τ ^ 2 := by
  have hp' : p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ S)) := hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa using hgg i
  | zero => simp
  | add x y _ _ hx hy =>
    have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
      simp only [map_add]; ring
    rw [e]; exact add_mem hx hy
  | smul r x hxm hx =>
    have e : aeval g (r • x) - aeval g' (r • x) =
        (aeval g r - aeval g' r) * aeval g x + aeval g' r * (aeval g x - aeval g' x) := by
      simp only [smul_eq_mul, map_mul]; ring
    rw [e]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hx)
    rw [pow_two]
    have hx1 : x ∈ Io S σ ^ 1 := by simpa using hxm
    exact Ideal.mul_mem_mul (aeval_sub_aeval_mem g g' hg hg' r) (by simpa using aeval_mem_pow g hg 1 hx1)
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
