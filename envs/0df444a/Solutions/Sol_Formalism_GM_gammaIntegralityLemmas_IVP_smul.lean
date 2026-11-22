-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IVP.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:31.843828+00:00
-- url     : https://prove2.me/submissions/f81f295f-0942-48a9-aff9-67262b843659

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
namespace IVP
theorem _root_.solution {D : ℕ} {g : ℕ → ℚ_[p]} (q : ℚ_[p]) (hq : ‖q‖ ≤ 1) (hg : IVP p D g) :
    IVP p D (fun m => q * g m) := by
  obtain ⟨⟨P, hP, hPg⟩, hn⟩ := hg
  refine ⟨⟨Polynomial.C q * P, (natDegree_C_mul_le _ _).trans hP, fun m => by simp [hPg]⟩, fun m => ?_⟩
  rw [norm_mul]
  exact mul_le_one₀ hq (norm_nonneg _) (hn m)
end IVP
end Formalism.GM.gammaIntegralityLemmas
