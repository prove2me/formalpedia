-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.hasDerivAt_dsW_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:59:02.471799+00:00
-- url     : https://prove2.me/submissions/1d8fd43a-135c-45c4-94d2-adb204d4bd7b

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_hasDerivAt_matrix_exp_zero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_smOn_orbit
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_hasDerivAt_ds
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_exists_adj
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
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
namespace CompanionTheory.D.gk.FinalFormK
theorem _root_.solution (hσ : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hd : Dense {v | IsSm G σ v})
    {v : H} (hv : IsSm G σ v) {W : List (Mat n)} (hW : LieW G W) {X : Mat n} (hX : ∀ t, ex X t ∈ G) :
    HasDerivAt (fun t => dsW σ W (σ (ex X t) v)) (dsW σ W (ds σ X v)) 0 := by
  obtain ⟨U, F, hU, h1U, hF, hfF⟩ := smOn_orbit hσ hv hW 1 hσ.one_mem
  have h0 := hasDerivAt_local (f := fun x => dsW σ W (σ x v)) hX (ex_zero X)
    (hasDerivAt_matrix_exp_zero X) hU h1U hF hfF
  have hs : IsSm G σ (ds σ X v) := hv.dsW hσ (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
  convert h0 using 1
  refine hd.eq_of_inner_right (𝕜 := ℂ) fun u hu => ?_
  obtain ⟨u', hu'⟩ := exists_adj hσ hiso hW hu
  have a1 := (hasDerivAt_const (0 : ℝ) u).inner ℂ h0
  have a2 := (hasDerivAt_const (0 : ℝ) u').inner ℂ (hasDerivAt_ds hσ hv hX)
  have e : (fun t => ⟪u, dsW σ W (σ (ex X t) v)⟫_ℂ) = fun t => ⟪u', σ (ex X t) v⟫_ℂ :=
    funext fun t => hu' _ (hv.apply hσ (hX t))
  rw [e] at a1
  have := a1.unique a2
  simp only [inner_zero_left, add_zero] at this
  rw [hu' _ hs, this]
end CompanionTheory.D.gk.FinalFormK
