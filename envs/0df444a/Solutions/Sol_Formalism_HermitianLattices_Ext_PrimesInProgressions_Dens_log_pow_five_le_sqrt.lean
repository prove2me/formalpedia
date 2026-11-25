-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.log_pow_five_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:48:42.499001+00:00
-- url     : https://prove2.me/submissions/e0f80f06-3e71-4847-8e1e-fcbe3e786282

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DyadicSizeLePowTwelveSecond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution (c : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 5 ≤ Real.sqrt q := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 10)).bound
    (c := 1 / (c ^ 2 + 1)) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 h
  refine ⟨⌈x₀⌉₊, fun q hq => ?_⟩
  have hqx : x₀ ≤ (q : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hq)
  have h1 := hx₀ q hqx
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hq0] at h1
  have h2 : Real.log q ^ 10 ≤ 1 / (c ^ 2 + 1) * q := (le_abs_self _).trans h1
  have h3 : (c ^ 2 + 1) * Real.log q ^ 10 ≤ q := by
    have hp : (0 : ℝ) < c ^ 2 + 1 := by positivity
    calc (c ^ 2 + 1) * Real.log q ^ 10 ≤ (c ^ 2 + 1) * (1 / (c ^ 2 + 1) * q) := by gcongr
      _ = (q : ℝ) := by field_simp
  have h4 : (c * Real.log q ^ 5) ^ 2 ≤ q := by
    have : (0 : ℝ) ≤ Real.log q ^ 10 := by positivity
    nlinarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt h4)
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
