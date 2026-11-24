-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwin_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:56.341307+00:00
-- url     : https://prove2.me/submissions/71288b15-e1d0-4c80-ac00-a1deccf0b3d1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwin_weight_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {g : MvPolynomial (Fin r × Fin n) R} {z : ℤ}
    (hg : g ≠ 0) (hz : IsWeightedHomogeneous (lhwinHt r n) g z) : 0 ≤ z := by
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hg
  rw [← hz hd]
  exact lhwin_weight_nonneg d
end Formalism.GradedWeylDivisibility
