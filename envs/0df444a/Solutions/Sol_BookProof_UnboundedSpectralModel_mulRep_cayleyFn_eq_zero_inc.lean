-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.mulRep_cayleyFn_eq_zero_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:08:18.079985+00:00
-- url     : https://prove2.me/submissions/7c712fc7-e96e-4ae6-9b84-aca14a695a9a

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.mulRep_cayleyFn_eq_zero_inc
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

variable (T : UnboundedSelfAdjoint H) {mu : Measure (spectrum ℂ (resOp T))}
  (V : Lp ℂ 2 mu →ₗᵢ[ℂ] H)
  (hV : ∀ u : Lp ℂ 2 mu, V (mulRep mu (coordFn (resOp T)) u) = resOp T (V u))

set_option maxHeartbeats 1000000 in
include hV in
theorem solution [IsFiniteMeasure mu] : mulRep mu (cayleyFn T) = 0 := by

  have hdecomp : (2 * Complex.I) • mulRep mu (cayleyFn T)
      = mulRep mu (coordFn (resOp T)) - star (mulRep mu (coordFn (resOp T)))
        - (2 * Complex.I)
            • (star (mulRep mu (coordFn (resOp T))) * mulRep mu (coordFn (resOp T))) := by
    have h := congrArg (mulRepHom mu) (cayley_symbol_identity T)
    simp only [map_sub, map_smul, map_mul, map_star, mulRepHom_apply] at h
    exact h.symm
  have hstar : (star (mulRep mu (coordFn (resOp T))) : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      = ContinuousLinearMap.adjoint (mulRep mu (coordFn (resOp T))) :=
    ContinuousLinearMap.star_eq_adjoint _
  have hform : ∀ u : Lp ℂ 2 mu,
      (inner ℂ u (((2 * Complex.I) • mulRep mu (cayleyFn T)) u) : ℂ) = 0 := by
    intro u
    rw [hdecomp, hstar]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply, inner_sub_right, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
    linear_combination model_symmetry_relation T V hV u
  have hP0 : (2 * Complex.I) • mulRep mu (cayleyFn T) = 0 := by
    have hlin : (((2 * Complex.I) • mulRep mu (cayleyFn T) :
        Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu) = 0 := by
      refine (inner_map_self_eq_zero _).mp fun u => ?_
      have hc := congrArg (starRingEnd ℂ) (hform u)
      rwa [inner_conj_symm, map_zero] at hc
    exact ContinuousLinearMap.coe_injective hlin
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  rcases smul_eq_zero.mp hP0 with h | h
  · exact absurd h h2I
  · exact h
