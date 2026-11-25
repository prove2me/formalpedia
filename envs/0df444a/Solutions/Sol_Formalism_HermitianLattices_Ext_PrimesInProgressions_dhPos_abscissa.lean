-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhPos_abscissa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:32:22.605714+00:00
-- url     : https://prove2.me/submissions/91657467-16f0-44ef-9b35-16fa47cddc88

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos

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
theorem _root_.solution {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
  have h : abscissaOfAbsConv (↗ψ * ↗Λ) ≤ ((1 : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ (by simp only [Complex.ofReal_re]; exact_mod_cast hy)
  exact lt_of_le_of_lt h (by exact_mod_cast hs)
end Formalism.HermitianLattices.Ext.PrimesInProgressions
