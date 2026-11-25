-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_eta_lim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:58:22.436703+00:00
-- url     : https://prove2.me/submissions/956391f8-792d-4489-9d55-675ba603332f

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_Xpow
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_choose_lim__68d426c4c0ad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open Filter Topology Finset
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {σ : Type} [Fintype σ] [DecidableEq σ] (i : σ) (S d : ℕ) (g g' : MvPolynomial σ ℝ)
    (hg : ∀ M ∈ g.support, M i ≤ d) :
    Tendsto (fun n : ℕ => fk (MvPolynomial.X i ^ (n - S) * g) (MvPolynomial.X i ^ (n - S) * g') /
        (((n - S).factorial : ℝ) * (n : ℝ) ^ d)) atTop
      (𝓝 (∑ M ∈ g.support, g.coeff M * g'.coeff M * wf M * (if M i = d then 1 / (d.factorial : ℝ) else 0))) := by
  have hlim : ∀ M ∈ g.support, Tendsto (fun n : ℕ => g.coeff M * g'.coeff M * wf M *
      (((n + M i - S).choose (M i) : ℝ) / (n : ℝ) ^ d)) atTop
      (𝓝 (g.coeff M * g'.coeff M * wf M * (if M i = d then 1 / (d.factorial : ℝ) else 0))) :=
    fun M hM => (choose_lim' S (M i) d (hg M hM)).const_mul _
  refine (tendsto_finsetSum _ hlim).congr' ?_
  filter_upwards [eventually_ge_atTop (S + 1)] with n hn
  rw [fk_Xpow, Finset.sum_div]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  have hk : (n - S).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hc := Nat.descFactorial_eq_factorial_mul_choose (M i + (n - S)) (n - S)
  rw [← Nat.choose_symm_add, show M i + (n - S) = n + M i - S by omega] at hc
  rw [show M i + (n - S) = n + M i - S by omega, hc]
  push_cast
  have hk' : ((n - S).factorial : ℝ) ≠ 0 := by exact_mod_cast hk
  have hn0 : (n : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
  field_simp
end Formalism.GM.leadingTermLemmas
