-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerA.sum_pairAt_star_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:30:35.268684+00:00
-- url     : https://prove2.me/submissions/73c401d1-6dc6-4945-bac9-2db1d6ddb688

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumPairAtStarMul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_pairAt_sum_left
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_pairAt_sum_right
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_mem_adjAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_pairAt_snd_left
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_act_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_mul


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
theorem _root_.solution {hU : IntOn μ U} (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')))
    (hM : ∀ a b, M a b ∈ adjAlg μ U hU) (hN : ∀ a b, N a b ∈ adjAlg μ U hU)
    (x y : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (hy : ∀ a, y a ∈ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    ∑ a, pairAt μ (act (star M * N) x a) (y a) c = ∑ e, pairAt μ (act N x e) (act M y e) c := by
  have hu : ∀ e, act N x e ∈ U := act_mem N hN x hx
  have hL : ∀ a, act (star M * N) x a = ∑ e, (M e a).2.unop (act N x e) := by
    intro a
    rw [act_mul]
    rfl
  calc ∑ a, pairAt μ (act (star M * N) x a) (y a) c
      = ∑ a, ∑ e, pairAt μ (act N x e) ((M e a).1 (y a)) c := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hL a, pairAt_sum_left hU hc _ _ (fun e => (mem_adjAlg.mp (hM e a)).2.1 _ (hu e)) (hy a)]
        exact Finset.sum_congr rfl fun e _ => pairAt_snd_left (hM e a) hc (hu e) (hy a)
    _ = ∑ e, ∑ a, pairAt μ (act N x e) ((M e a).1 (y a)) c := Finset.sum_comm
    _ = ∑ e, pairAt μ (act N x e) (act M y e) c := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact (pairAt_sum_right hU hc _ (hu e) _ (fun a => (mem_adjAlg.mp (hM e a)).1 _ (hy a))).symm
end Formalism.FourierDecayAlt.P5.HerA
