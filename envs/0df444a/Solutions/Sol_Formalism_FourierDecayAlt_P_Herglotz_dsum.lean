-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Herglotz.dsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:37.643815+00:00
-- url     : https://prove2.me/submissions/aed938cd-93b9-49ba-8d6e-24374c314d13

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Herglotz
open Real Filter Topology Finset
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.Herglotz
theorem _root_.solution (F : (Fin d → ℤ) → ℂ) (S : Finset (Fin d → ℤ)) :
    ∑ σ ∈ S, ∑ σ' ∈ S, F (σ - σ') =
      ∑' τ, (((S ×ˢ S).filter (fun p => p.1 - p.2 = τ)).card : ℂ) * F τ := by
  rw [tsum_eq_sum (s := (S ×ˢ S).image (fun p => p.1 - p.2))]
  · rw [← Finset.sum_product' (f := fun σ σ' => F (σ - σ')),
      ← Finset.sum_fiberwise_of_maps_to (g := fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 - p.2)
        (t := (S ×ˢ S).image (fun p => p.1 - p.2)) (fun p hp => Finset.mem_image_of_mem _ hp)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]), Finset.sum_const,
      nsmul_eq_mul]
  · intro τ hτ
    have : (S ×ˢ S).filter (fun p => p.1 - p.2 = τ) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun p hp h => hτ (Finset.mem_image.2 ⟨p, hp, h⟩)
    simp [this]
end Formalism.FourierDecayAlt.P.Herglotz
