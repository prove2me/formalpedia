-- Prove2me | solution 1 for Formalism.L2.LamCM.valuation_eq_exp_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:19:27.063804+00:00
-- url     : https://prove2.me/submissions/7f0521bc-e14c-4b12-8d97-460752047a7d

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Theorems.Thm_P2M_Formalism_L2_LamCM_spanSingleton_ne_zero__ef0616425764
import Theorems.Thm_Formalism_L2_LamCM_valuation_algebraMap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (𝓞 K)⁰ x
  simp only at hrs
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hr : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hrs
    exact mul_ne_zero hx hs0 hrs
  have hv : v.valuation K x * v.valuation K (algebraMap (𝓞 K) K s) = v.valuation K (algebraMap (𝓞 K) K r) := by
    rw [← map_mul, hrs]
  have hc : FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) +
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K s)) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r)) := by
    rw [← FractionalIdeal.count_mul K v (spanSingleton_ne_zero' hx) (spanSingleton_ne_zero' hs0),
      FractionalIdeal.spanSingleton_mul_spanSingleton, hrs]
  rw [valuation_algebraMap_eq v hs, valuation_algebraMap_eq v hr, ← hc, neg_add, WithZero.exp_add] at hv
  exact mul_right_cancel₀ WithZero.exp_ne_zero hv
end Formalism.L2.LamCM
