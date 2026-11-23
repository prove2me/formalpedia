-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r3_divisibility_of_unit_roots
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:03.550156+00:00
-- url     : https://prove2.me/submissions/7ba18dad-2570-481d-abc5-1787a5c006ed

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
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (h3 : UnitFactorQ) (hr : QRoots) : RootOfUnityRemainder := by
  intro l _ O _ _ _ ζ hl2 hζ b hb
  obtain ⟨g, hg, _⟩ := h3 l O hl2
  have h1 : (X - C (ζ ^ b - 1)) ∣ q l O := by
    rw [hr l O ζ hζ]
    exact Finset.dvd_prod_of_mem (fun b => (X : O⟦X⟧) - C (ζ ^ b - 1)) hb
  have h2 : pi0 l O - C (l : O) = q0 l O := rfl
  rw [h2, hg]
  exact Dvd.dvd.mul_left h1 _
end Formalism.CohomologicalDescent.HeightDescentMinors
