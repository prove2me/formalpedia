-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwa_val_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:14.440101+00:00
-- url     : https://prove2.me/submissions/3282b3e8-8248-402a-ba4e-352b40b8c8c4

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_nsmul_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution {M : Type} [AddCommGroup M] [Module LL M] [FiniteDimensional LL M]
    (v : AddValuation LL (WithTop ℚ)) (f : M →ₗ[LL] M) (k : ℕ) (hk : k ≠ 0)
    (hdim : finrank LL M = k) (c : LL) (r : ℚ) (hf : f ^ k = c • 1) (hc : v c = (r : WithTop ℚ)) :
    v (LinearMap.det f) = (r : WithTop ℚ) := by
  have h1 : (LinearMap.det f) ^ k = c ^ k := by
    rw [← map_pow, hf, LinearMap.det_smul, map_one, mul_one, hdim]
  have h2 : k • v (LinearMap.det f) = ((k • r : ℚ) : WithTop ℚ) := by
    rw [← AddValuation.map_pow, h1, AddValuation.map_pow, hc, WithTop.coe_nsmul]
  by_cases h : v (LinearMap.det f) = ⊤
  · rw [h, exwa_nsmul_top k hk] at h2
    exact absurd h2 WithTop.top_ne_coe
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp h
    rw [← hq] at h2 ⊢
    rw [ ← WithTop.coe_nsmul, WithTop.coe_inj] at h2
    rw [WithTop.coe_inj]
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    simp only [nsmul_eq_mul] at h2
    exact mul_left_cancel₀ hk' h2
end Formalism.WeaklyAdmissibleFiltrations
