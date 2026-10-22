-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:09:44.525651+00:00
-- url     : https://prove2.me/submissions/82f4c007-62cd-4015-909f-80b614e18f93

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general_inc
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
import Theorems.Thm_BookProof_ChapterSpectralDirectSum_spectral_multiplication_model_general_inc
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterStoneResolvent
open BookProof.UnboundedSpectralModel



noncomputable section

open MeasureTheory Complex
open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H) {mu : Measure (spectrum ℂ (resOp T))}
  (V : Lp ℂ 2 mu →ₗᵢ[ℂ] H)
  (hV : ∀ u : Lp ℂ 2 mu, V (mulRep mu (coordFn (resOp T)) u) = resOp T (V u))

set_option maxHeartbeats 1000000 in
theorem solution (T : UnboundedSelfAdjoint H) :
    ∃ (S : Set H) (mu : S → Measure (spectrum ℂ (resOp T)))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ x : S, ∀ᵐ z ∂(mu x), z.1 ≠ 0 ∧ ‖z.1‖ ^ 2 = z.1.im) ∧
      (∀ (x : S) (u : Lp ℂ 2 (mu x)),
        ∃ h : V x (mulRep (mu x) (coordFn (resOp T)) u) ∈ T.domain,
          T.op ⟨V x (mulRep (mu x) (coordFn (resOp T)) u), h⟩
            = V x (u + Complex.I • mulRep (mu x) (coordFn (resOp T)) u)) := by

  obtain ⟨S, mu, V, hprob, hsum, hint⟩ :=
    spectral_multiplication_model_general_inc (resOp T) (isStarNormal_resOp T)
  refine ⟨S, mu, V, hprob, hsum, ?_, ?_⟩
  · intro x
    have := hprob x
    exact (model_ae_ne_zero T (V x) (hint x)).and (model_ae_circle T (V x) (hint x))
  · intro x u
    exact ⟨model_mem T (V x) (hint x) u, model_apply T (V x) (hint x) u⟩
