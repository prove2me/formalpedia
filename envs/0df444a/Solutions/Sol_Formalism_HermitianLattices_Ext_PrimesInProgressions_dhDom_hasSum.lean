-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhDom_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:05.488567+00:00
-- url     : https://prove2.me/submissions/2acf4121-bfc6-4b0f-ad8a-8938413ea49d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHDom

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
    HasSum (fun n ↦ term (logMul^[k] (↗ψ * ↗Λ)) s n)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s) := by
  have habs : abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
    refine lt_of_le_of_lt (abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) ?_) ?_
    · intro y hy
      exact LSeriesSummable_twist_vonMangoldt ψ hy
    · exact_mod_cast hs
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hU : LFunction ψ =ᶠ[nhds z] LSeries (↗ψ) := by
      filter_upwards [hopen.mem_nhds hz'] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    simp only [negLD]
    rw [Filter.EventuallyEq.deriv_eq hU, DirichletCharacter.LFunction_eq_LSeries ψ hz',
      LSeries_twist_vonMangoldt_eq ψ hz', neg_div]
  have hit : iteratedDeriv k (negLD ψ) s = iteratedDeriv k (LSeries (↗ψ * ↗Λ)) s := by
    simp only [← iteratedDerivWithin_univ]
    refine Filter.EventuallyEq.iteratedDerivWithin_eq ?_ hev.eq_of_nhds
    simpa [nhdsWithin_univ] using hev
  rw [hit, LSeries_iteratedDeriv k habs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (by simpa using habs)).LSeriesHasSum
end Formalism.HermitianLattices.Ext.PrimesInProgressions
