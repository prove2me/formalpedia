-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.sharp_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:44.17995+00:00
-- url     : https://prove2.me/submissions/ab683f52-0bd0-4144-99ce-12a6cd8949d9

import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sharp_identity
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sharp_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ‖((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y‖ ≤
      (u - y + 1) * Real.log u := by
  rw [sharp_identity χ hy hu]
  have hu1 : 1 ≤ u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
          ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, Real.log u := Finset.sum_le_sum (fun n hn => sharp_term χ hy hu hn)
    _ = ((⌊u⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) * Real.log u := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ (u - y + 1) * Real.log u := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have h1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
        have h2 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
        have h3 : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
        rw [Nat.cast_sub h3]
        linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
