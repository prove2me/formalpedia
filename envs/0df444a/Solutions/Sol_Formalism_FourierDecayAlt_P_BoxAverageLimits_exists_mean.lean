-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.exists_mean
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:32.055333+00:00
-- url     : https://prove2.me/submissions/c57bd9c1-7c07-4f35-b7ef-3e6745639afe

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_card_box
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_hyper_le_atTop
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_LIMf_eq_of_tendsto
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_tendsto_LIMf
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_avg_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_avg_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_avg_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_avg_real_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_invAt_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (e : ι → Λ) (he : AddSubgroup.closure (Set.range e) = ⊤) (c : ℕ → Λ) :
    IsMean (LIMf e c) ∧ ∀ g, Bdd g →
      (∀ ε > 0, ∀ᶠ n in atTop, ∀ m ∈ box ι (n + 1), ‖g (bpt e (c n) m)‖ ≤ ε) → LIMf e c g = 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g h hg hh
    apply LIMf_eq_of_tendsto
    rw [avg_add]
    exact (tendsto_LIMf e c g hg).add (tendsto_LIMf e c h hh)
  · intro a g hg
    apply LIMf_eq_of_tendsto
    rw [avg_smul]
    exact (tendsto_LIMf e c g hg).const_mul a
  · intro g hg hpos
    have hcl : IsClosed {z : ℂ | 0 ≤ z.re ∧ z.im = 0} :=
      (isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_eq Complex.continuous_im continuous_const)
    exact hcl.mem_of_tendsto (tendsto_LIMf e c g hg)
      (Filter.Eventually.of_forall (fun n => avg_real_nonneg e c g hpos n))
  · apply LIMf_eq_of_tendsto
    have : avg e c (fun _ => (1 : ℂ)) = fun _ => 1 := funext (avg_one e c)
    rw [this]; exact tendsto_const_nhds
  · intro g σ hg
    exact invAt_all e c he σ g hg
  · intro g hg hsmall
    apply LIMf_eq_of_tendsto
    apply Tendsto.mono_left _ hyper_le_atTop
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hsmall (ε / 2) (by positivity)] with n hn
    rw [dist_zero_right]
    have hpos : (0 : ℝ) < (n + 1 : ℝ) ^ Fintype.card ι := by positivity
    unfold avg
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 : ‖∑ m ∈ box ι (n + 1), g (bpt e (c n) m)‖ ≤ (box ι (n + 1)).card * (ε / 2) := by
      calc _ ≤ ∑ m ∈ box ι (n + 1), ‖g (bpt e (c n) m)‖ := norm_sum_le _ _
        _ ≤ ∑ _m ∈ box ι (n + 1), (ε / 2) := Finset.sum_le_sum (fun m hm => hn m hm)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [card_box] at h1
    push_cast at h1
    rw [one_div, inv_mul_lt_iff₀ hpos]
    nlinarith
end Formalism.FourierDecayAlt.P.BoxAverageLimits
