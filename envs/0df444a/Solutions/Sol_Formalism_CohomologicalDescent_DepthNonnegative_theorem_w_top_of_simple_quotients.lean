-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.theorem_w_top_of_simple_quotients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:21.218844+00:00
-- url     : https://prove2.me/submissions/30430f41-f680-46f2-8189-ffe6b5729b71

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_pow_smul_weighted_component_mem_weyl
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_application_window
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_factor_action_on_tensor_product_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_theorem_w_central_of_simple_quotients
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_dualWeyl_module_finite
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_finite_quotient_of_pow_smul_mem
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_incl_R_of_Z
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowGraded
import Theorems.Thm_Formalism_RankGapBounds_FormsTensorLocalization_tensor_reduction_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution (hSS : SimpleSubquotOfPower) (hIso : SubquotIso) : TheoremWTop := by
  intro hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L
    _ _ _ _ _ hwt hT
  obtain ⟨hl, hu, hfin, hdvd, hh, ht, hshape, hecl, hex, hstab, he, hHS, hHN, hclass, hhw, hIN1⟩ := hT
  haveI : ∀ τ : ι, Module.Finite O (dualWeyl O N N (res N (lam τ))) :=
    fun τ => dualWeyl_module_finite O N N _
  let pr : ∀ τ : ι, (Fin N → ℕ) →
      dualWeyl O N N (res N (lam τ)) →ₗ[O] dualWeyl O N N (res N (lam τ)) := fun τ w =>
    (weightedHomogeneousComponent (rowW N N) w).restrict
      (fun x hx => dualWeylRowGraded O N N (res N (lam τ)) w x hx)
  have hexO : ∀ τ, LatIncl (l : O) (deltaIn O N lam τ) (ex τ) := fun τ x =>
    LA.la_incl_R_of_Z O N N le_rfl (res N (lam τ)) l (ex τ) hu (hex τ) x x.2
  have hNoe : IsNoetherian O (NablaT O N lam) := inferInstance
  have hArt : IsArtinian O (NablaT O N lam ⧸ tensSub (deltaIn O N lam)) := by
    haveI := finite_quotient_of_pow_smul_mem O (NablaT O N lam) (l : O) (∑ τ, ex τ) (tensSub (deltaIn O N lam)) hfin
      (tensor_reduction_holds O ι _ (deltaIn O N lam) (l : O) ex hexO)
    exact isArtinian_of_finite
  have he' : ∀ τ w (x : NablaT O N lam), e τ w • x = atFactor τ (pr τ w) x := by
    intro τ w x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [smul_comm, map_smul, he τ w u (pr τ w (u τ)) rfl, factor_action_on_tensor_product_holds]
    | add a b ha hb => rw [smul_add, map_add, ha, hb]
  have hIN2 : ∀ τ ∈ T2, ∀ w, depthAt N k j lam τ w ≤ ((i τ : ℕ) : ℤ) →
      ∀ x : dualWeyl O N N (res N (lam τ)),
        (l : O) ^ cFloor l N k t h lam j q xm xp ecl i τ • pr τ w x ∈ deltaIn O N lam τ := by
    intro τ hτ w hw x
    obtain ⟨hrows, hanti, hblock, hspread, hcloud, hlows, habove, hle, htop⟩ := hshape τ hτ
    have hA := application_window hD l k (j τ) t (q τ) h (lam τ) (xm τ) (xp τ) hl ht
    rw [hrows] at hA
    have hE := hA hanti hblock hspread hh hcloud hlows habove hle htop (ecl τ) (hecl τ hτ) (i τ) w hw
    exact pow_smul_weighted_component_mem_weyl O l N (res N (lam τ)) w _ hu hE x x.2
  have hmain := theorem_w_central_of_simple_quotients hSS hIso O A G Γ K jK ι (fun τ => dualWeyl O N N (res N (lam τ)))
    (deltaIn O N lam) T S (l : O) ϖ n₀ (Fin N → ℕ) pr e Λ L hwt (depthAt N k j lam)
    (fun τ => (i τ : ℤ)) T2 ex (cFloor l N k t h lam j q xm xp ecl i) hNoe hArt hdvd hstab he' hHS hHN
    hclass hhw hIN1 hexO hIN2
  exact ⟨hmain, Nat.sInf_le hmain⟩
end Formalism.CohomologicalDescent.DepthNonnegative
