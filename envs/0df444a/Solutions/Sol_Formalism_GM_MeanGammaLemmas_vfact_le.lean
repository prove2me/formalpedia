-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.vfact_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:26.699805+00:00
-- url     : https://prove2.me/submissions/42c96956-5419-4970-bd69-c54c04a8c981

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (padicValNat p n.factorial : ℝ) ≤ n / ((p : ℝ) - 1) := by
  have hp1 := hp.out.one_lt
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  have h2 : (p - 1) * padicValNat p n.factorial ≤ n := by rw [h]; exact Nat.sub_le _ _
  have hp1r : (1 : ℝ) < p := by exact_mod_cast hp1
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [le_div_iff₀ hpm]
  have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp1.le]; simp
  have h4 : (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
  rw [Nat.cast_mul, h3] at h4
  linarith
end Formalism.GM.MeanGammaLemmas
