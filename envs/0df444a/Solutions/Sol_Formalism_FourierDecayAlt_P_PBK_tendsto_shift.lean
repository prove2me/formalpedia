-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:23:35.345443+00:00
-- url     : https://prove2.me/submissions/0e43dbf8-9f66-4f19-8949-47052b2697bc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_eventually_ne_zero_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_eps
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_rhoR_eq_eventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (s : ℕ) (hs : 1 ≤ s) (σ : ℂ) :
    Tendsto (fun x => (s : ℂ) * (rhoR s σ x * (x + σ) - x)) (cocompact ℂ) (𝓝 σ) := by
  set a : ℂ := ((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹ with ha
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hsa : (s : ℂ) * (1 - a) = 1 := by
    rw [ha, Nat.cast_sub hs]
    field_simp
    ring
  rcases eq_or_ne σ 0 with rfl | hσ
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually s 0] with x hx
    rw [hx]
    simp
  ·
    have hφ : HasDerivAt (fun e : ℂ => (1 - e) ^ a) (-a) 0 := by
      have h1 : HasDerivAt (fun e : ℂ => 1 - e) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
      have h2 := h1.cpow_const (c := a) (by simp)
      simpa using h2
    have hslope := hasDerivAt_iff_tendsto_slope.mp hφ
    have hε : Tendsto (fun x : ℂ => σ / (x + σ)) (cocompact ℂ) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨Formalism.FourierDecayAlt.P.PBK.tendsto_eps σ, ?_⟩
      filter_upwards [Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add σ] with x hx
      exact div_ne_zero hσ hx.2
    have hlim := (((hslope.comp hε).const_mul σ).add_const σ).const_mul (s : ℂ)
    have hval : (s : ℂ) * (σ * -a + σ) = σ := by linear_combination σ * hsa
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually s σ, Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add σ] with x hx hx2
    rw [hx, ← ha]
    simp only [Function.comp_apply, slope_def_field, sub_zero, Complex.one_cpow]
    generalize (1 - σ / (x + σ)) ^ a = φv
    field_simp [hx2.2]
    ring
end Formalism.FourierDecayAlt.P.PBK
