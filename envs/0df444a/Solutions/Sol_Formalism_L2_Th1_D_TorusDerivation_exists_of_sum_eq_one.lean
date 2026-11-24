-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.exists_of_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:17.806331+00:00
-- url     : https://prove2.me/submissions/87a5e0ce-561e-45da-a9df-4a450fa7bcfe

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)
open TorusDerivation
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.TorusDerivation
theorem _root_.solution {α : Type} [Fintype α] (f : α → ℕ) (h : ∑ s, f s = 1) :
    ∃ s, f s = 1 ∧ ∀ t, t ≠ s → f t = 0 := by
  classical
  have h0 : ∃ s, f s ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at h
  obtain ⟨s, hs⟩ := h0
  have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ s)
  rw [h] at h2
  have h3 : ∑ t ∈ Finset.univ.erase s, f t = 0 := by omega
  exact ⟨s, by omega, fun t ht =>
    (Finset.sum_eq_zero_iff.1 h3) t (Finset.mem_erase.2 ⟨ht, Finset.mem_univ t⟩)⟩
end Formalism.L2.Th1.D.TorusDerivation
