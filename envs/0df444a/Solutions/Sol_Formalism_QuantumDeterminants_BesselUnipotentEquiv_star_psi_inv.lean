-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:39.440799+00:00
-- url     : https://prove2.me/submissions/0072cfbc-258b-433e-a8b4-1643c7e0f39d

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
import Theorems.Thm_Formalism_QuantumDeterminants_BesselUnipotentEquiv_psi_one
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_additive_character_holds
import Theorems.Thm_Formalism_QuantumDeterminants_unipotent_subgroup_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BesselUnipotentEquiv
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.BesselUnipotentEquiv
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z)
    (n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hn : n ∈ Nset k r) :
    star (psi k r z c n⁻¹) = psi k r z c n := by
  have hinv := (unipotent_subgroup_holds k r).2.2 n hn
  have hu := WeylGroupFacts.isUnit_of_uh hn.1
  have h1 : psi k r z c n⁻¹ * psi k r z c n = 1 := by
    rw [← (additive_character_holds k r z c hz n⁻¹ hinv).1 n hn, Matrix.nonsing_inv_mul _ hu, psi_one z c hz]
  have h2 : star (psi k r z c n⁻¹) * psi k r z c n⁻¹ = 1 := by
    rw [Complex.star_def, Complex.conj_mul', (additive_character_holds k r z c hz n⁻¹ hinv).2]
    simp
  calc star (psi k r z c n⁻¹) = star (psi k r z c n⁻¹) * (psi k r z c n⁻¹ * psi k r z c n) := by
        rw [h1, mul_one]
    _ = psi k r z c n := by rw [← mul_assoc, h2, one_mul]
end Formalism.QuantumDeterminants.BesselUnipotentEquiv
