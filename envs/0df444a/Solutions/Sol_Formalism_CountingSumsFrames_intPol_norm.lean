-- Prove2me | solution 1 for Formalism.CountingSumsFrames.intPol_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:25.288471+00:00
-- url     : https://prove2.me/submissions/d7c21dae-1026-4b33-9114-139e8a943330

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution {σ : Type} (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ IntPol p σ) (m : σ →₀ ℕ) :
    ‖coeff m x‖ ≤ 1 := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hx
  simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]
  exact PadicInt.norm_le_one _
end Formalism.CountingSumsFrames
