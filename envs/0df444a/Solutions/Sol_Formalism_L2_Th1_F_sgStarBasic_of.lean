-- Prove2me | solution 1 for Formalism.L2.Th1.F.sgStarBasic_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:25:35.694592+00:00
-- url     : https://prove2.me/submissions/4578a6f9-2685-4b2f-9eb2-995a6dc63d7f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds
namespace Formalism.L2.Th1.F
theorem _root_.solution (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (h1 : SigmaSimple)
    (h3 : ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0) :
    SgStarBasic := by
  intro L
  set e : ℂ → ℂ := fun z => Complex.exp (-(s2 L) * z ^ 2 / 2) with he_def
  have hed : Differentiable ℂ e := by
    rw [he_def]; fun_prop
  have hfun : sgStar L = wSigma L * e := rfl
  have hs0 : wSigma L 0 = 0 := (hz L 0).mpr L.lattice.zero_mem
  have he0 : e 0 = 1 := by simp [he_def]
  have hde : deriv e = fun z => -(s2 L) * z * e z := by
    funext z
    have h : HasDerivAt (fun z : ℂ => -(s2 L) * z ^ 2 / 2) (-(s2 L) * (2 * z) / 2) z := by
      have := ((hasDerivAt_pow 2 z).const_mul (-(s2 L))).div_const 2
      simpa using this
    rw [h.cexp.deriv]
    ring
  have he1 : deriv e 0 = 0 := by rw [hde]; simp
  have he2 : iteratedDeriv 2 e 0 = -(s2 L) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hde]
    have h : HasDerivAt (fun z : ℂ => -(s2 L) * z * e z)
        (-(s2 L) * e 0 + -(s2 L) * 0 * deriv e 0) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).const_mul (-(s2 L))).fun_mul (hed 0).hasDerivAt
      simpa using this
    rw [h.deriv, he0]
    ring
  refine ⟨(he L).mul hed, ?_, ?_, ?_, ?_⟩
  · intro z
    simp [sgStar, ho L z]
  · intro z
    simp [sgStar, hz L z, Complex.exp_ne_zero]
  · rw [hfun, deriv_mul (he L 0) (hed 0), (h1 L).1, he0, hs0, he1]
    ring
  · rw [hfun, iteratedDeriv_mul (he L).contDiff.contDiffAt hed.contDiff.contDiffAt]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, iteratedDeriv_zero,
      iteratedDeriv_one, hs0, (h1 L).1, (h3 L).1, (h3 L).2, he2]
    norm_num [Nat.choose]
end Formalism.L2.Th1.F
