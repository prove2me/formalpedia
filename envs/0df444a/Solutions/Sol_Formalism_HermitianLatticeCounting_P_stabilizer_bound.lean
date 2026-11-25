-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.stabilizer_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:01:51.970636+00:00
-- url     : https://prove2.me/submissions/038e5f81-b0d7-47d0-bb24-38f469086a2f

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : StBound := by
  intro j
  have h1 : Stirling.stirlingSeq (j + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le j)
  rw [Stirling.stirlingSeq_one] at h1
  unfold Stirling.stirlingSeq at h1
  have hk : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  set k : ℝ := ((j + 1 : ℕ) : ℝ) with hkdef
  have he := Real.exp_pos 1
  have hfac : ((j + 1).factorial : ℝ) = k * (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, hkdef]; push_cast; ring
  have hk1 : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)

  have hs2 : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by positivity)
  have e1 : (Real.exp 1 / k) ^ (j + 1) * (j.factorial : ℝ) =
      ((j + 1).factorial : ℝ) / (Real.sqrt (2 * k) * (k / Real.exp 1) ^ (j + 1)) * (Real.sqrt (2 * k) / k) := by
    rw [hfac, div_pow, div_pow]; field_simp
  rw [e1]
  have h2 : Real.sqrt (2 * k) / k ≤ Real.sqrt 2 := by
    rw [div_le_iff₀ hk, Real.sqrt_mul (by norm_num)]
    have : Real.sqrt k ≤ k := by
      rw [Real.sqrt_le_left hk.le]
      nlinarith
    have h0 := Real.sqrt_nonneg 2
    nlinarith
  have h3 : 0 ≤ Real.sqrt (2 * k) / k := by positivity
  have h4 : 0 ≤ Real.exp 1 / Real.sqrt 2 := by positivity
  calc _ ≤ Real.exp 1 / Real.sqrt 2 * Real.sqrt 2 := by
        apply mul_le_mul h1 h2 h3 h4
    _ = Real.exp 1 := by field_simp
    _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
end Formalism.HermitianLatticeCounting.P
