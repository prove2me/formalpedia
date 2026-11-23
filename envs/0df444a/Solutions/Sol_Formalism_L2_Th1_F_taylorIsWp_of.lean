-- Prove2me | solution 1 for Formalism.L2.Th1.F.taylorIsWp_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:56.857174+00:00
-- url     : https://prove2.me/submissions/d3633631-e556-481e-9af8-056609b0da8b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_const
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_id
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_pow
import Theorems.Thm_Formalism_L2_Th1_F_weierstrass_p_series_coeff
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_G_LogCR_Agree_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PowerSeries
open TaylorWp
namespace Formalism.L2.Th1.F
theorem _root_.solution (hr : TaylorRing) (hd : TaylorDeriv) : TaylorIsWp := by
  intro L
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, weierstrass_p_series_coeff L 0]; simp
  · intro n hn
    rw [weierstrass_p_series_coeff L n, L.G_eq_zero_of_odd (n + 2) (by
      obtain ⟨k, rfl⟩ := hn; exact ⟨k + 1, by ring⟩)]
    simp
  · have hp : T (L.weierstrassPExcept 0) (pSeries L) := ⟨L.analyticAt_weierstrassPExcept 0, rfl⟩
    have hp' : T (deriv (L.weierstrassPExcept 0)) (Formalism.L2.Th1.B.dz (pSeries L)) :=
      ⟨hp.1.deriv, hd.1 _ hp.1⟩
    have hq := T.add hr (T.const hr 1) (T.mul hr (T.pow hr (T.id hr) 2) hp)
    have h1 := T.pow hr (T.add hr (T.const hr (-2)) (T.mul hr (T.pow hr (T.id hr) 3) hp')) 2
    have h2 := T.add hr (T.add hr (T.mul hr (T.const hr 4) (T.pow hr hq 3))
      (T.mul hr (T.mul hr (T.const hr (-L.g₂)) (T.pow hr (T.id hr) 4)) hq))
      (T.mul hr (T.const hr (-L.g₃)) (T.pow hr (T.id hr) 6))
    have key := hr.2.2.2 _ _ (?_ : (fun z => (-2 + z ^ 3 * deriv (L.weierstrassPExcept 0) z) ^ 2)
      =ᶠ[nhds 0] fun z => 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) ^ 3
        + -L.g₂ * z ^ 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) + -L.g₃ * z ^ 6)
    · rw [h1.2, h2.2] at key
      simp only [map_neg, map_ofNat, map_one] at key
      rw [key]; ring
    · filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
      rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz]
      by_cases hz0 : z = 0
      · simp [hz0]; norm_num
      replace hz : z ∉ L.lattice := by simp_all
      have hE := L.derivWeierstrassP_sq z hz
      have e1 := L.weierstrassPExcept_def 0 z
      have e2 := L.derivWeierstrassPExcept_def 0 z
      simp only [ZeroMemClass.coe_zero, sub_zero] at e1 e2
      rw [e1, e2]
      have e3 : (z ^ 3 * L.derivWeierstrassP z) ^ 2 = z ^ 6 * (4 * L.weierstrassP z ^ 3
          - L.g₂ * L.weierstrassP z - L.g₃) := by rw [← hE]; ring
      field_simp
      simp
      linear_combination e3
end Formalism.L2.Th1.F
