-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.rootsDescent_of_roots_and_fourth_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:07.433166+00:00
-- url     : https://prove2.me/submissions/94b54005-3d4d-4e93-9161-823becaa98a4

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_roots_product_holds

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
theorem _root_.solution (hr : QRoots) (h4 : R4) : RootsDescent := by
  intro l _ O _ _ _ I _ ζ hl hζ hI S m hdvd
  have h1 := roots_product_holds O I (Finset.Ioo 0 l) (fun b => ζ ^ b - 1) S (inc l O m)
    (fun b _ => by
      obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow ζ 1 b
      rw [one_pow] at hy
      rw [hy]; exact I.mul_mem_right _ hI)
    (by
      intro a ha b hb hab
      simp only [Finset.coe_Ioo, Set.mem_Ioo] at ha hb
      exact hζ.pow_inj ha.2 hb.2 (by simpa using hab))
    hdvd
  rw [← hr l O ζ hζ] at h1
  obtain ⟨y, hy⟩ := h1
  exact h4 l O hl S m y hy
end Formalism.CohomologicalDescent.HeightDescentMinors
