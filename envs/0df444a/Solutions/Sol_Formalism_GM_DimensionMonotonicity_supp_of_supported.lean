-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.supp_of_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:55.318558+00:00
-- url     : https://prove2.me/submissions/d93bb1c8-9539-4023-a5ec-64c16cdd3dd4

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution {K σ : Type} [CommSemiring K] {s : Set σ} {q : MvPolynomial σ K}
    (hq : q ∈ MvPolynomial.supported K s) : ∀ m ∈ q.support, ∀ v, m v ≠ 0 → v ∈ s := by
  intro m hm v hv
  rw [mem_supported] at hq
  apply hq
  rw [Finset.mem_coe, mem_vars]
  exact ⟨m, hm, Finsupp.mem_support_iff.mpr hv⟩
end Formalism.GM.DimensionMonotonicity
