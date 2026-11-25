-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.sum_cAP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:10.070909+00:00
-- url     : https://prove2.me/submissions/e6750c87-67b9-405b-827f-7f9f6f3e6e18

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA

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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M b : ℕ) (t : ℝ) : ∑ n ∈ Icc 0 ⌊t⌋₊, cAP M b n = psiAP M b t := by
  unfold cAP Formalism.ZeroFreeDirichlet.psiAP
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨Nat.zero_le _, hx.1.2⟩, hx.2⟩
  · intro x hx hnx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx hnx
    have hx0 : x = 0 := by
      by_contra h
      exact hnx ⟨⟨Nat.pos_of_ne_zero h, hx.1.2⟩, hx.2⟩
    subst hx0
    simp
end Formalism.HermitianLattices.Ext.PrimesInProgressions
