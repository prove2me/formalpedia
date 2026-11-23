-- Prove2me | solution 1 for Formalism.CyclotomicNorms.low_divide
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:54.341881+00:00
-- url     : https://prove2.me/submissions/6007b0c9-d055-4946-95a4-dbbed3143cee

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_LowDegreePowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.CyclotomicNorms
namespace Formalism.CyclotomicNorms
theorem _root_.solution {O : Type*} [CommRing O] (a : O) (f : PowerSeries O)
    (h : ∀ k, a ∣ coeff k f) : ∃ f', f = C a * f' := by
  refine ⟨mk fun k => (h k).choose, ?_⟩
  ext k
  rw [coeff_C_mul, coeff_mk]
  exact (h k).choose_spec
end Formalism.CyclotomicNorms
