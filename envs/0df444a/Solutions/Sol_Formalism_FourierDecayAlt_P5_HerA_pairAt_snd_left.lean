-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerA.pairAt_snd_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:44:04.896262+00:00
-- url     : https://prove2.me/submissions/75e81d7d-cc8a-4df3-ab66-27d63bb59986

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
theorem _root_.solution {hU : IntOn μ U} {a : Pr (RadSp k r z z' π π')} (ha : a ∈ adjAlg μ U hU) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {Φ Ψ : RadSp k r z z' π π'} (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) :
    pairAt μ (a.2.unop Φ) Ψ c = pairAt μ Φ (a.1 Ψ) c := by
  have h := (mem_adjAlg.mp ha).2.2 c hc Ψ hΨ Φ hΦ
  rw [pairAt_swap μ Ψ (a.2.unop Φ) c, ← h]
  exact (pairAt_swap μ (a.1 Ψ) Φ c).symm
end Formalism.FourierDecayAlt.P5.HerA
