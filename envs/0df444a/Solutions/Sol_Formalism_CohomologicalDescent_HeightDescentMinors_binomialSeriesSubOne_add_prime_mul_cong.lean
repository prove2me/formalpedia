-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.binomialSeriesSubOne_add_prime_mul_cong
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:48.962145+00:00
-- url     : https://prove2.me/submissions/d391eecc-aaf3-4648-98be-270fd94c5482

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_subst_of_constantCoeff_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_br_zero

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (ha : ActLaws) (hq : QMul) (d e : ℤ_[l]) :
    ∃ s : O⟦X⟧, br l O (d + e * (l : ℤ_[l])) = br l O d + X * q l O * s := by
  obtain ⟨h1, -, -, h4, -⟩ := ha l O
  have hphi : br l O (e * (l : ℤ_[l])) = phi l O (br l O e) := by rw [h4, h1]
  have hs : HasSubst ((1 + X) ^ l - 1 : O⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  obtain ⟨t, ht⟩ := dvd_subst_of_constantCoeff_zero _ (br l O e) hs (constantCoeff_br_zero l O e)
  have hX := (hq l O).1
  refine ⟨binomialSeries O d * t, ?_⟩
  have h0 : br l O (e * (l : ℤ_[l])) = X * q l O * t := by rw [hphi, phi, ht, hX]
  have h2 : binomialSeries O (e * (l : ℤ_[l])) = 1 + X * q l O * t := by
    simp only [br] at h0
    linear_combination h0
  simp only [br]
  rw [binomialSeries_add, h2]
  ring
end Formalism.CohomologicalDescent.HeightDescentMinors
