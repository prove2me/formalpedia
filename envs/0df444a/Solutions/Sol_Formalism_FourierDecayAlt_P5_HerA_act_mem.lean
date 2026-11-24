-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerA.act_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:37:50.741672+00:00
-- url     : https://prove2.me/submissions/72c4dafa-bcc5-4c48-a690-dc1a4dabdde3

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumPairAtStarMul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_mem_adjAlg

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
variable {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}
namespace Formalism.FourierDecayAlt.P5.HerA
theorem _root_.solution {hU : IntOn μ U} (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ adjAlg μ U hU)
    (x : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (a : Ix S) : act M x a ∈ U := by
  show (∑ b, (M a b).1 (x b)) ∈ U
  exact U.sum_mem fun b _ => (mem_adjAlg.mp (hM a b)).1 _ (hx b)
end Formalism.FourierDecayAlt.P5.HerA
