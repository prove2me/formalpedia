-- Prove2me | solution 1 for Formalism.DivisionValues.divisor_into_dual_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:19.927171+00:00
-- url     : https://prove2.me/submissions/65485181-eb40-4963-800d-42ae85ad3d86

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Theorems.Thm_Formalism_DivisionValues_DualLatticeDivisor_mem_range_of_vw_nonneg
import Theorems.Thm_Formalism_DivisionValues_reduction_first_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : DivIntoDual := by
  intro K _ _ _ D R B n M π ι P ζ hζ hvζ hP hM hloc x hx
  by_cases hBx : B x = 0
  · rw [hBx]; exact ⟨0, map_zero _⟩
  · apply DualLatticeDivisor.mem_range_of_vw_nonneg _ hBx
    intro w
    have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R :=
      ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩
    rw [hloc w] at hxl
    rcases reduction_first_step K w (n w) D (M w) (π w) (ι w) B (P w) (ζ w) 0 (hζ w) (hvζ w) (hP w) (hM w) x
      hxl with h | h
    · exact absurd h hBx
    · exact h
end Formalism.DivisionValues
