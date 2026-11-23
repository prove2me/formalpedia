-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_norm_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:24.827688+00:00
-- url     : https://prove2.me/submissions/1138b6ac-4c16-407c-b27e-41f66cd8a942

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_norm_proj_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_norm_iteratedFDeriv_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution {n : ℕ} (c : ℕ) (k : Fin n) (x : Fin n → ℂ) (hx : x k ≠ 0) :
    ‖iteratedFDeriv ℂ c (fun y : Fin n → ℂ => (y k)⁻¹) x‖ ≤ c.factorial * (‖x k‖⁻¹ * ‖x k‖⁻¹ ^ c) := by
  have hs : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  obtain ⟨g, hg⟩ : ∃ g : (Fin n → ℂ) →L[ℂ] ℂ, g = ContinuousLinearMap.proj k := ⟨_, rfl⟩
  have hgx : g x = x k := by rw [hg]; rfl
  have hs' : IsOpen (g ⁻¹' ({0}ᶜ : Set ℂ)) := hs.preimage g.continuous
  have hmem : g x ∈ ({0}ᶜ : Set ℂ) := by rw [hgx]; simpa using hx
  have hcd : ContDiffOn ℂ c (Inv.inv : ℂ → ℂ) {0}ᶜ :=
    fun w hw => (contDiffAt_inv ℂ (by simpa using hw)).contDiffWithinAt
  have h := g.iteratedFDerivWithin_comp_right hcd hs.uniqueDiffOn hs'.uniqueDiffOn (x := x) hmem
    (i := c) le_rfl
  rw [iteratedFDerivWithin_of_isOpen c hs' hmem, iteratedFDerivWithin_of_isOpen c hs hmem] at h
  have h2 : (fun y : Fin n → ℂ => (y k)⁻¹) = Inv.inv ∘ g := by rw [hg]; rfl
  rw [h2, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [hgx, norm_iteratedFDeriv_inv c _ hx]
  have h3 : ∏ _i : Fin c, ‖g‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hg ▸ a_norm_proj_le k)
  exact mul_le_of_le_one_right (by positivity) h3
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
