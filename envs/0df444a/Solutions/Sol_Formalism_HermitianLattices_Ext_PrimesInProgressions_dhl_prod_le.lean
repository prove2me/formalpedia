-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:24:10.605442+00:00
-- url     : https://prove2.me/submissions/86f2f594-800a-40b8-99a1-8bcba81f5f56

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocalA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by
  rw [norm_prod]
  have h1 : ∀ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    have hn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp'.pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      simpa using hs
    calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ p := by rw [norm_one]; linarith
  calc ∏ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ ∏ p ∈ M.primeFactors, (p : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) h1
    _ = ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ M := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos M) (Nat.prod_primeFactors_dvd M)
end Formalism.HermitianLattices.Ext.PrimesInProgressions
