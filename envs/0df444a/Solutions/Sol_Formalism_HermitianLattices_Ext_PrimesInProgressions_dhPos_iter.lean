-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhPos_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:46:48.789461+00:00
-- url     : https://prove2.me/submissions/d315aeb1-8124-4700-b331-4813c0cfe4e5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPos_abscissa

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
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    (-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s = LSeries (logMul^[k] (↗ψ * ↗Λ)) s := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hEq : ∀ z : ℂ, 1 < z.re → negLD ψ z = LSeries (↗ψ * ↗Λ) z := by
    intro z hz
    have hev : DirichletCharacter.LFunction ψ =ᶠ[nhds z] LSeries (fun n => ψ n) := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    unfold negLD
    rw [hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries ψ hz,
      DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hz]
    ring
  have heq : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hEq z hz
  rw [heq.iteratedDeriv_eq, LSeries_iteratedDeriv k (dhPos_abscissa ψ hs), ← mul_assoc, ← mul_pow]
  norm_num
end Formalism.HermitianLattices.Ext.PrimesInProgressions
