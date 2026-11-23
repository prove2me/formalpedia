-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.epsilon_limit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:24.696962+00:00
-- url     : https://prove2.me/submissions/8b27bd27-6b0f-4352-bbc3-3a906e7f98f8

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.TA Finset Filter Topology TA1
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TA.EpsLimit := by
  intro E H _ _ W _ len k P Φ V w0 B0 Bc jn hw0 hb hE hV
  have h1 : ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      (gram k V P).re ≤ Bc * wsup len B0 (fun w => ‖Φ eps w []‖ ^ 2) := by
    have hall : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ p ∈ P, Φ eps w0 p = V p :=
      (Filter.eventually_all_finset P).2 hV
    filter_upwards [hall, self_mem_nhdsWithin] with eps h1 h2
    have h3 := hb eps h2
    have e : gram k (Φ eps w0) P = gram k V P := by
      unfold gram
      refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
      rw [h1 p hp, h1 p' hp']
    rwa [e] at h3
  have h2 : Tendsto (fun eps => wsup len B0 (fun w => ‖Φ eps w []‖ ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 jn) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [(tendsto_order.1 (hE w0 hw0)).1 a ha] with eps h
      exact lt_of_lt_of_le h (le_ciSup (f := fun w : {w // len w ≤ B0} => ‖Φ eps w.1 []‖ ^ 2)
        (Set.finite_range _).bddAbove ⟨w0, hw0⟩)
    · have : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ w : {w // len w ≤ B0}, ‖Φ eps w.1 []‖ ^ 2 < (a + jn) / 2 :=
        eventually_all.2 (fun w => (tendsto_order.1 (hE w.1 w.2)).2 _ (by linarith))
      filter_upwards [this] with eps h
      have : Nonempty {w // len w ≤ B0} := ⟨⟨w0, hw0⟩⟩
      exact lt_of_le_of_lt (ciSup_le fun w => (h w).le) (by linarith)
  exact ge_of_tendsto (h2.const_mul Bc) h1
end Formalism.FourierDecayAlt.P
