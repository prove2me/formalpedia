-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhPos_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:02:59.329888+00:00
-- url     : https://prove2.me/submissions/45919fd1-d78e-4915-beba-5430d30f2b12

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPos_abscissa
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPos_iter

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
    HasSum (fun n ↦ (term (logMul^[k] (↗ψ * ↗Λ)) s n).re)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s).re := by
  rw [dhPos_iter ψ k hs]
  have habs : abscissaOfAbsConv (logMul^[k] (↗ψ * ↗Λ)) < s.re := by
    have e : ∀ j : ℕ, abscissaOfAbsConv (logMul^[j] (↗ψ * ↗Λ)) = abscissaOfAbsConv (↗ψ * ↗Λ) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]
    rw [e]
    exact dhPos_abscissa ψ hs
  have hs2 := (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum
  exact Complex.reCLM.hasSum hs2
end Formalism.HermitianLattices.Ext.PrimesInProgressions
