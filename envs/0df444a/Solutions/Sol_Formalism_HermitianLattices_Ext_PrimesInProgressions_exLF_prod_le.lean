-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:25.515182+00:00
-- url     : https://prove2.me/submissions/e06f82d1-865e-4f87-9acb-801bd757396c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
variable {M : ℕ} [NeZero M]
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by
  have h1 : ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ ∏ p ∈ M.primeFactors, (p : ℝ) := by
    rw [norm_prod]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (by omega : 1 ≤ p)
      · simp only [Complex.neg_re]; linarith
    calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ ≤ p := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
  have h2 : ∏ p ∈ M.primeFactors, (p : ℝ) ≤ M := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.prod_primeFactors_dvd M)
    calc ∏ p ∈ M.primeFactors, (p : ℝ) = ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ M := by exact_mod_cast this
  exact h1.trans h2
end Formalism.HermitianLattices.Ext.PrimesInProgressions
