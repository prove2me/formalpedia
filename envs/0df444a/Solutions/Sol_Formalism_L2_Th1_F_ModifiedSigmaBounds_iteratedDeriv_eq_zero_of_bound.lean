-- Prove2me | solution 1 for Formalism.L2.Th1.F.ModifiedSigmaBounds.iteratedDeriv_eq_zero_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:25:06.439+00:00
-- url     : https://prove2.me/submissions/f830885b-f5e4-442a-8bb9-b7e1f8745127

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds
open Formalism.L2.Th1.F.ModifiedSigmaBounds
open SigmaConv
namespace Formalism.L2.Th1.F.ModifiedSigmaBounds
theorem _root_.solution {f : ℂ → ℂ} (hf : Differentiable ℂ f) {K r : ℝ} (hr : 0 < r)
    (hb : ∀ z, ‖z‖ < r → ‖f z‖ ≤ K * ‖z‖ ^ 4) (n : ℕ) (hn : n < 4) : iteratedDeriv n f 0 = 0 := by
  rw [← norm_le_zero_iff]
  have hev : ∀ᶠ R in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖iteratedDeriv n f 0‖ ≤ n.factorial * K * R ^ (4 - n) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with R hR
    have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR.1
      (c := 0) hf.diffContOnCl (C := K * R ^ 4) (fun z hz => by
        have hz' : ‖z‖ = R := by simpa using hz
        have := hb z (hz' ▸ hR.2)
        rwa [hz'] at this)
    refine h1.trans (le_of_eq ?_)
    have h2 : R ^ 4 = R ^ (4 - n) * R ^ n := by rw [← pow_add, Nat.sub_add_cancel hn.le]
    have h3 : R ^ n ≠ 0 := pow_ne_zero _ hR.1.ne'
    rw [h2]
    field_simp
  have hlim : Tendsto (fun R : ℝ => n.factorial * K * R ^ (4 - n)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    have hc : Continuous (fun R : ℝ => n.factorial * K * R ^ (4 - n)) := by fun_prop
    have h0 := hc.tendsto 0
    rw [zero_pow (by omega), mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim hev
end Formalism.L2.Th1.F.ModifiedSigmaBounds
