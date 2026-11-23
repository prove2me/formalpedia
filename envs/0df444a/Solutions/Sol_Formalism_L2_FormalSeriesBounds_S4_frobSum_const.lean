-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.frobSum_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:49.42911+00:00
-- url     : https://prove2.me/submissions/00b52b2e-b772-4a90-8ed3-c020e7c0da0a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution {d : ℕ} {l : ℕ} (hl : 1 < l) (P : ℕ) (p : ZMod d → ℕ) (hp : ∀ τ, p τ = P)
    (a : ZMod d) : frobSum l p a = (P : ℝ) / ((l : ℝ) - 1) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl
  have h0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  have h1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have h2 : (l : ℝ) - 1 ≠ 0 := by
    intro h
    linarith
  have hlne : (l : ℝ) ≠ 0 := by positivity
  unfold frobSum
  have hk : ∀ k : ℕ, ((l : ℝ) ^ (k + 1))⁻¹ * (p (a + ((k + 1 : ℕ) : ZMod d)) : ℝ) =
      ((P : ℝ) * (l : ℝ)⁻¹) * ((l : ℝ)⁻¹) ^ k := by
    intro k
    rw [hp, ← inv_pow, pow_succ]
    ring
  simp only [hk, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp
  try ring
end Formalism.L2.FormalSeriesBounds.S4
