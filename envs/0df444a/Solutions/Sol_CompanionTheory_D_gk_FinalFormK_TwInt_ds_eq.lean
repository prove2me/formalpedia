-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.TwInt.ds_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:43:53.543437+00:00
-- url     : https://prove2.me/submissions/e1c0b071-3ede-450d-be0e-4e5b7941d41e

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_smul
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_hasDerivAt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_hasDerivAt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.FinalFormK
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Mat n → (H →L[ℂ] H)} {τ : Mat n → (H' →L[ℂ] H')}
variable {L : Mat n → Prop}
variable [CompleteSpace H] [CompleteSpace H']
variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → ι → ι → ℂ} {T : ι → H → H'}
namespace CompanionTheory.D.gk.FinalFormK
namespace TwInt
theorem _root_.solution (h : TwInt G L σ τ M T) (hσ : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hd : Dense {v | IsSm G σ v}) (hL : ∀ X, L X → ∀ t, ex X t ∈ G) (hM1 : ∀ c d, M 1 c d = if c = d then 1 else 0)
    {X : Mat n} (hX : ∀ t, ex X t ∈ G) {M' : ι → ι → ℂ}
    (hM' : ∀ c d, HasDerivAt (fun t => M (ex X t) c d) (M' c d) 0) (c : ι) {v : H} (hv : IsSm G σ v) :
    ds τ X (T c v) = T c (ds σ X v) + ∑ d, M' c d • T d v := by
  have h1 : HasDerivAt (fun t => ∑ d, M (ex X t) c d • T d (σ (ex X t) v))
      (∑ d, (M (ex X 0) c d • T d (ds σ X v) + M' c d • T d (σ (ex X 0) v))) 0 :=
    HasDerivAt.fun_sum fun d _ => (hM' c d).smul ((h.bdd d).hasDerivAt (h.lin d) hσ hiso hd hL hv hX)
  have e : (fun t => τ (ex X t) (T c v)) = fun t => ∑ d, M (ex X t) c d • T d (σ (ex X t) v) :=
    funext fun t => h.eqv _ (hX t) c v hv
  unfold ds
  rw [e, h1.deriv]
  simp [ex_zero, hM1, hσ.map_one, Finset.sum_add_distrib, ite_smul, ds]
end TwInt
end CompanionTheory.D.gk.FinalFormK
