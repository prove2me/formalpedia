-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IVP.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:24.143839+00:00
-- url     : https://prove2.me/submissions/d43c5db6-9c4f-489f-b34a-f364d7e4ac5c

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
theorem _root_.solution {D E : ℕ} {g h : ℕ → ℚ_[p]} (hg : IVP p D g) (hh : IVP p E h) :
    IVP p (D + E) (fun m => g m * h m) := by
  obtain ⟨⟨P, hP, hPg⟩, hn⟩ := hg
  obtain ⟨⟨Q, hQ, hQh⟩, hn'⟩ := hh
  refine ⟨⟨P * Q, (natDegree_mul_le).trans (add_le_add hP hQ), fun m => by simp [hPg, hQh]⟩, fun m => ?_⟩
  rw [norm_mul]
  exact mul_le_one₀ (hn m) (norm_nonneg _) (hn' m)
end IVP
end Formalism.GM.gammaIntegralityLemmas
