-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.intPol_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:18.290034+00:00
-- url     : https://prove2.me/submissions/fcdbc696-193e-4e4b-915e-5705535e5c63

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution {σ : Type} (f : MvPolynomial σ ℚ_[p]) (hf : f ∈ IntPol p σ) :
    ∀ μ, ‖coeff μ f‖ ≤ 1 := by
  obtain ⟨f0, rfl⟩ := hf
  intro μ
  simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]
  exact PadicInt.norm_le_one (coeff μ f0)
end Formalism.GM.gammaIntegralityLemmas
