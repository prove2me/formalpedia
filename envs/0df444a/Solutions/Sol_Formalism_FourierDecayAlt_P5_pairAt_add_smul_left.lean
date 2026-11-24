-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.pairAt_add_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:48.369582+00:00
-- url     : https://prove2.me/submissions/040b9576-7f81-4d1c-be50-600ccc962fb3

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Theorems.Thm_Formalism_FourierDecayAlt_P5_hsInner_add_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (μ : Measure (Mt k r)) (Φ Φ' Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ)
    (h1 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ)
    (h2 : Integrable (fun g : Mt k r => B.hsInner ((Φ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ) :
    pairAt μ (Φ + a • Φ') Ψ c = pairAt μ Φ Ψ c + a * pairAt μ Φ' Ψ c := by
  unfold pairAt
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hsInner_add_smul_left]
  rw [integral_add h1 (h2.const_mul a), integral_const_mul]
end Formalism.FourierDecayAlt.P5
