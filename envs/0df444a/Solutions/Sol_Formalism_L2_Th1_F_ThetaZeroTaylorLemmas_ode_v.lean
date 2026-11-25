-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.ode_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:16:02.471129+00:00
-- url     : https://prove2.me/submissions/f5a89209-84bd-4d93-9a09-69363de2c5a3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_dom_mem_nhds
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_hasDerivAt_v
import Theorems.Thm_Formalism_L2_Th1_F_halfShift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
namespace Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
theorem _root_.solution (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h2t : 2 * t ∈ L.lattice) :
    (fun z => (1 + z * z * L.weierstrassPExcept 0 z + -(L.weierstrassP t) * (z * z))
        * (deriv (v L t) z + L.weierstrassP t + s2 L))
      =ᶠ[𝓝 0] fun z => -(3 * L.weierstrassP t ^ 2 - L.g₂ / 4) * (z * z) := by
  filter_upwards [dom_mem_nhds L ht, L.compl_lattice_sdiff_singleton_mem_nhds 0] with z h1 h2
  rw [(hasDerivAt_v L h1).deriv]
  by_cases h0 : z = 0
  · simp only [h0, zero_add, mul_zero, zero_mul, add_zero, one_mul]
    ring
  have hzl : z ∉ L.lattice := fun h => h2 ⟨h, h0⟩
  have hs := halfShift L t z ht h2t hzl h1
  have h5 := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h5
  have hz2 : z * z * (1 / z ^ 2) = 1 := by field_simp
  linear_combination (-(z * z)) * hs - (z * z) * (L.weierstrassP (z + t) - L.weierstrassP t) * h5
    + (L.weierstrassP (z + t) - L.weierstrassP t) * hz2
end Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
