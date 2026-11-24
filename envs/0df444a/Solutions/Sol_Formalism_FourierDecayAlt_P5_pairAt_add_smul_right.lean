-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.pairAt_add_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:26.700794+00:00
-- url     : https://prove2.me/submissions/bc1c691f-25b3-45fa-8474-8f6d3f317522

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Theorems.Thm_Formalism_FourierDecayAlt_P5_hsInner_add_smul_right

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
theorem _root_.solution (μ : Measure (Mt k r)) (Φ Ψ Ψ' : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ)
    (h1 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ)
    (h2 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ) :
    pairAt μ Φ (Ψ + a • Ψ') c = pairAt μ Φ Ψ c + conj a * pairAt μ Φ Ψ' c := by
  unfold pairAt
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hsInner_add_smul_right]
  rw [integral_add h1 (h2.const_mul (conj a)), integral_const_mul]
end Formalism.FourierDecayAlt.P5
