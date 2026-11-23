-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.LIMf_shift_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:00.353801+00:00
-- url     : https://prove2.me/submissions/b00a2512-2c97-46bb-b843-596104d09391

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_hyper_le_atTop
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_LIMf_eq_of_tendsto
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_tendsto_LIMf
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_avg_shift_small

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
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (hg : Bdd g) (j : ι) :
    LIMf e c (fun x => g (x + e j)) = LIMf e c g := by
  obtain ⟨B, hB⟩ := hg
  have hg' : Bdd g := ⟨B, hB⟩
  apply LIMf_eq_of_tendsto
  have h0 : Tendsto (fun n => avg e c (fun x => g (x + e j)) n - avg e c g n)
      (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    apply Tendsto.mono_left _ hyper_le_atTop
    apply squeeze_zero_norm (avg_shift_small e c g B hB j)
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * B)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [mul_one_div]
  have := h0.add (tendsto_LIMf e c g hg')
  simpa using this
end Formalism.FourierDecayAlt.P.BoxAverageLimits
