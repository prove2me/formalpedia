-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:32.813981+00:00
-- url     : https://prove2.me/submissions/1685887a-de91-4966-bfd4-89e43b7cea71

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_card_box

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
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (n : ℕ) : avg e c (fun _ => 1) n = 1 := by
  unfold avg
  rw [Finset.sum_const, card_box, nsmul_eq_mul, mul_one]
  have hpos : (0 : ℝ) < (n + 1 : ℝ) ^ Fintype.card ι := by positivity
  push_cast
  field_simp
end Formalism.FourierDecayAlt.P.BoxAverageLimits
