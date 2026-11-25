-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.TwInt.bdd_dsW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:19.631693+00:00
-- url     : https://prove2.me/submissions/7dd3d9c2-7958-4131-8bd4-ff2b3f0a1a30

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_congr
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_add
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_zero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_smul
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_sum
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_dsW_append
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_comp_dsW
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_hasDerivAt_matrix_exp_zero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_TwInt_isSm
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_TwInt_ds_eq
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_smul
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
theorem _root_.solution (h : TwInt G L σ τ M T) (hσ : RepOn G σ) (hτ : RepOn G τ)
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hd : Dense {v | IsSm G σ v}) (hL : ∀ X, L X → ∀ t, ex X t ∈ G)
    (hM : ∀ c d, SmOn G fun g => M g c d) (hM1 : ∀ c d, M 1 c d = if c = d then 1 else 0)
    {W : List (Mat n)} (hW : ∀ X ∈ W, L X) (c : ι) : Bdd G L σ fun v => dsW τ W (T c v) := by
  induction W using List.reverseRecOn generalizing c with
  | nil => exact h.bdd c
  | append_singleton W X ih =>
    have hW' : ∀ Y ∈ W, L Y := fun Y hY => hW Y (List.mem_append_left _ hY)
    have hLX : L X := hW X (by simp)
    have hX := hL X hLX
    have hWG : LieW G W := fun Y hY => hL Y (hW' Y hY)
    have hM' : ∀ c d, ∃ m, HasDerivAt (fun t => M (ex X t) c d) m 0 := fun c d => by
      obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hM c d 1 hσ.one_mem
      exact ⟨_, hasDerivAt_local (f := fun g => M g c d) hX (ex_zero X) (hasDerivAt_matrix_exp_zero X)
        hU h1U hF hfF⟩
    choose M' hM' using hM'
    have h1 := (ih hW' c).comp_dsW hσ hL (W' := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hLX
    refine (h1.add (Bdd.sum Finset.univ fun d _ => (ih hW' d).smul (M' c d))).congr fun v hv => ?_
    have hs : IsSm G σ (ds σ X v) := hv.dsW hσ (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
    have hsum : ∀ s : Finset ι, IsSm G τ (∑ d ∈ s, M' c d • T d v) ∧
        dsW τ W (∑ d ∈ s, M' c d • T d v) = ∑ d ∈ s, M' c d • dsW τ W (T d v) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨by simpa using IsSm.zero, by simpa using dsW_smul hτ (IsSm.zero (G := G) (σ := τ)) 0 hWG⟩
      | insert i s hi ih' =>
        have hi' := h.isSm hσ hL hM i hv
        rw [Finset.sum_insert hi, Finset.sum_insert hi, dsW_add hτ (hi'.smul _) ih'.1 hWG, ih'.2,
          dsW_smul hτ hi' _ hWG]
        exact ⟨(hi'.smul _).add ih'.1, rfl⟩
    rw [dsW_append]
    show dsW τ W (ds τ X (T c v)) = dsW τ W (T c (ds σ X v)) + _
    rw [h.ds_eq hσ hiso hd hL hM1 hX hM' c hv, dsW_add hτ (h.isSm hσ hL hM c hs) (hsum _).1 hWG, (hsum _).2]
end TwInt
end CompanionTheory.D.gk.FinalFormK
