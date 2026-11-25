-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:39:19.071184+00:00
-- url     : https://prove2.me/submissions/d95de394-4226-4a09-aedb-1d4d65cd1bd8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution {nf : ℕ} {L : Finset (Fin (r + 2))} {e₁ e : CT k r nf × List (Mat k r)} (h₁ : Good L e₁)
    (h : Good L e) : Good L (mulCT e₁.1 e.1, e.2) := by
  unfold Good at h₁ h ⊢
  obtain ⟨ha1, hs1, -⟩ := h₁
  obtain ⟨ha, hs, hw⟩ := h
  refine ⟨fun l hl => ?_, fun x hx => ?_, hw⟩
  · by_cases h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0
    · exact ha1 l h1
    · apply ha l
      push_neg at h1
      simpa [mulCT, h1.1, h1.2] using hl
  · simp only [mulCT, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hs1 x hx
    · exact hs x hx
end Formalism.FourierDecayAlt.P.MinorPolynomials
