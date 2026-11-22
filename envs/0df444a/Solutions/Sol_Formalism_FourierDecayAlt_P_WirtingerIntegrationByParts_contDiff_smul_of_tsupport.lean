-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.contDiff_smul_of_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:18:12.654383+00:00
-- url     : https://prove2.me/submissions/59ef59ca-9ca3-455a-ba6e-1e62abb1adaf

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {φ : E → ℂ} {a : E → V} {Ω : Set E} {n : WithTop ℕ∞}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ n φ Ω) (ha : ContDiff ℝ n a) (hsupp : tsupport a ⊆ Ω) :
    ContDiff ℝ n (fun x => φ x • a x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact (hφ.contDiffAt (hΩ.mem_nhds hx)).smul ha.contDiffAt
  · have hx' : x ∉ tsupport a := fun h => hx (hsupp h)
    have h0 : (fun y => φ y • a y) =ᶠ[nhds x] fun _ => (0 : V) := by
      have := notMem_tsupport_iff_eventuallyEq.mp hx'
      filter_upwards [this] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
