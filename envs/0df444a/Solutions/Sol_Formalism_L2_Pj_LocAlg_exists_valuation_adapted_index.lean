-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.exists_valuation_adapted_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:10:07.222136+00:00
-- url     : https://prove2.me/submissions/e01e0fc9-9f41-4991-b0af-0d84ee417cc3

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Theorems.Thm_Formalism_L2_Pj_LocAlg_yv_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace Formalism.L2.Pj.LocAlg
theorem _root_.solution (jc : Fin (N + 1)) (x : Fin N → Ω) (W : ValuationSubring Ω) :
    ∃ j0, yv jc x j0 ≠ 0 ∧ ∀ j, yv jc x j / yv jc x j0 ∈ W := by
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j => W.valuation (yv jc x j))
    ⟨jc, Finset.mem_univ _⟩
  have h1 : W.valuation (yv jc x jc) = 1 := by rw [yv_self, map_one]
  have hne : W.valuation (yv jc x j0) ≠ 0 := by
    intro h
    have hle := hj0 jc (Finset.mem_univ _)
    rw [h, h1] at hle
    exact one_ne_zero (le_antisymm hle zero_le')
  refine ⟨j0, fun h => hne (by rw [h, map_zero]), fun j => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
  exact (div_le_one₀ (zero_lt_iff.mpr hne)).mpr (hj0 j (Finset.mem_univ _))
end Formalism.L2.Pj.LocAlg
