-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.aeval_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:15.839356+00:00
-- url     : https://prove2.me/submissions/32b377f7-d70e-4145-9373-8338bb48a5d9

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_congr
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_C_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_congr
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_GoodQ_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_GoodQ_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_freezeSub_good
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_sum_dv
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_aeval_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (LL : Letters (N + 1)) (ρ : Fin r) (hW : LL.vec (Fin.last N) = true)
    (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hf : f ∈ Pol p r LL) :
    AllMono (p := p) (GoodQ ρ) ((LL.snoc LL.total).deg) (aeval (freezeSub p LL ρ) f) := by
  rw [aeval_expand]
  apply AllMono.sum
  intro μ hμ
  have hmd : MultiDeg LL μ := by
    have hsub : (f.support : Set (Fin (N + 1) × Fin r →₀ ℕ)) ⊆ {m | MultiDeg LL m} := hf
    exact hsub (Finset.mem_coe.mpr hμ)
  apply AllMono.C_mul
  have h := AllMono.prod (p := p) (GoodQ ρ) (GoodQ_add ρ) (GoodQ_zero ρ) univ (fun v => μ v • dv v.1)
    (fun v => freezeSub p LL ρ v ^ μ v)
    (fun v _ => (freezeSub_good LL ρ hW v.1 v.2).pow (GoodQ ρ) (GoodQ_add ρ) (GoodQ_zero ρ) (μ v))
  exact h.congr (GoodQ ρ) (sum_dv LL μ hmd)
end Formalism.GM.gammaIntegralityLemmas
