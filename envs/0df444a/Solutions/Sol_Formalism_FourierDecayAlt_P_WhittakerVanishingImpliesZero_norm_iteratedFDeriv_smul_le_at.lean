-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.norm_iteratedFDeriv_smul_le_at
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:06.290605+00:00
-- url     : https://prove2.me/submissions/ba60e509-b4a1-4168-af37-4334e6f53eb9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} {g : E → F} {x : E} {n : ℕ}
    (hf : ContDiff ℝ n f) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  obtain ⟨u, hu, hxu, hgu⟩ := ContDiffWithinAt.contDiffOn' (m := n) (s := Set.univ) le_rfl (by simp)
    hg.contDiffWithinAt
  have hgu' : ContDiffOn ℝ n g u := by simpa using hgu
  have key := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (𝕜' := ℝ) (N := n) hf.contDiffOn hgu' hu.uniqueDiffOn hxu
    (n := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hu hxu] at key
  refine key.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [iteratedFDerivWithin_of_isOpen i hu hxu, iteratedFDerivWithin_of_isOpen (n - i) hu hxu]
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
