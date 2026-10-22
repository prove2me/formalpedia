-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.unbounded_multiplication_model_cyclic_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:09:43.046343+00:00
-- url     : https://prove2.me/submissions/4ac0d0b9-a333-405e-a273-88ff29ec5303

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.unbounded_multiplication_model_cyclic_inc
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
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
theorem solution (T : UnboundedSelfAdjoint H) (xi : H)
    (hxi : ‖xi‖ = 1)
    (hcyc : DenseRange (cfcVec (resOp T) (isStarNormal_resOp T) xi)) :
    ∃ (mu : Measure (spectrum ℂ (resOp T))) (_ : IsProbabilityMeasure mu)
      (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),
      (∀ᵐ z ∂mu, z.1 ≠ 0 ∧ ‖z.1‖ ^ 2 = z.1.im) ∧
      (∀ u : Lp ℂ 2 mu, ∃ h : U (mulRep mu (coordFn (resOp T)) u) ∈ T.domain,
        T.op ⟨U (mulRep mu (coordFn (resOp T)) u), h⟩
          = U (u + Complex.I • mulRep mu (coordFn (resOp T)) u)) ∧
      (∀ x ∈ T.domain, ∃ u : Lp ℂ 2 mu, x = U (mulRep mu (coordFn (resOp T)) u)) := by

  obtain ⟨mu, hmu, U, h1, _h2⟩ :=
    spectral_multiplication_model (resOp T) (isStarNormal_resOp T) xi hcyc hxi
  have hV : ∀ u : Lp ℂ 2 mu,
      U.toLinearIsometry (mulRep mu (coordFn (resOp T)) u) = resOp T (U.toLinearIsometry u) :=
    h1
  refine ⟨mu, hmu, U, ?_, ?_, ?_⟩
  · exact (model_ae_ne_zero T U.toLinearIsometry hV).and
      (model_ae_circle T U.toLinearIsometry hV)
  · intro u
    exact ⟨model_mem T U.toLinearIsometry hV u, model_apply T U.toLinearIsometry hV u⟩
  · intro x hx
    obtain ⟨y, hy⟩ := exists_resOp_eq T hx
    refine ⟨U.symm y, ?_⟩
    have := hV (U.symm y)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply]
      at this
    rw [this, hy]
