-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.not_pow_dvd_mul_of_not_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:01.264555+00:00
-- url     : https://prove2.me/submissions/8a7a1178-85d4-4cce-b257-2e1713df8b70

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {R : Type} [CommRing R]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution [IsDomain R] {π x y : R} {a b : ℕ} (hπ : Prime π)
    (hx : ¬ π ^ (a + 1) ∣ x) (hy : ¬ π ^ (b + 1) ∣ y) : ¬ π ^ (a + b + 1) ∣ x * y := by
  rw [pow_dvd_iff_le_emultiplicity, not_le] at hx hy ⊢
  rw [emultiplicity_mul hπ]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hx)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hy)
  rw [← hm] at hx ⊢
  rw [← hk] at hy ⊢
  norm_cast at hx hy ⊢
  omega
end Formalism.CohomologicalDescent.HeightDescentMinors
