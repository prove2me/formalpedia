-- Prove2me | solution 1 for Formalism.L2.Th1.F.Taylor.taylor0_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:24:56.986125+00:00
-- url     : https://prove2.me/submissions/2022f9d9-1c09-42e2-a04a-a2ada9126448

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_coeff_taylor0

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
open Formalism.L2.Th1.F.Taylor
open PowerSeries
namespace Formalism.L2.Th1.F.Taylor
theorem _root_.solution {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : taylor0 f = taylor0 g) : f =ᶠ[nhds 0] g := by
  have hd : AnalyticAt ℂ (fun z => f z - g z) 0 := hf.fun_sub hg
  have h0 : ∀ n, iteratedDeriv n (fun z => f z - g z) 0 = 0 := by
    intro n
    have h1 := congrArg (coeff n) h
    rw [coeff_taylor0, coeff_taylor0] at h1
    have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h2 : iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
      field_simp at h1
      exact h1
    rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, h2, sub_self]
  have ht : analyticOrderAt (fun z => f z - g z) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hd).mpr fun i _ => h0 i
  rw [analyticOrderAt_eq_top] at ht
  filter_upwards [ht] with z hz
  exact sub_eq_zero.mp hz
end Formalism.L2.Th1.F.Taylor
