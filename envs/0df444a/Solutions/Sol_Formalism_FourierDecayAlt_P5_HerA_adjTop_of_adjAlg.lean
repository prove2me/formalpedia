-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerA.adjTop_of_adjAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:49:46.865019+00:00
-- url     : https://prove2.me/submissions/178083fb-4cdf-4163-a7d5-fcaa687b8d9a

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumPairAtStarMul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_form_last
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_act_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_mul_mem_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_sum_pairAt_star_mul

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5.HerA
theorem _root_.solution (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hF : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ e e',
      (Fr.ofWord L st w).F e e' ∈ adjAlg μ U hU ∧ (Fr.ofWord L st w).d L e e' ∈ adjAlg μ U hU) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  intro w hw x y hx hy c hc
  have hFF : ∀ e e', (Fr.ofWord L st w).F e e' ∈ adjAlg μ U hU := fun e e' => (hF w hw e e').1
  have hFd : ∀ e e', (Fr.ofWord L st w).d L e e' ∈ adjAlg μ U hU := fun e e' => (hF w hw e e').2
  have hxU : ∀ a, x a ∈ U := fun a => hK (hx a)
  have hyU : ∀ a, y a ∈ U := fun a => hK (hy a)
  have hDF := mul_mem_entries _ _ hFd hFF
  have hu := act_mem _ hDF x hxU
  have hv := act_mem _ hFF y hyU
  have hint := fun e => hU c hc _ (hu e) _ (hv e)
  refine ⟨?_, ?_⟩
  · simp only [topDens]
    exact integrable_finsetSum Finset.univ fun e _ => hint e
  · rw [form_last, mul_assoc, sum_pairAt_star_mul _ _ hFF hDF x y hxU hyU hc]
    simp only [topDens]
    rw [integral_finsetSum Finset.univ fun e _ => hint e]
    rfl
end Formalism.FourierDecayAlt.P5.HerA
