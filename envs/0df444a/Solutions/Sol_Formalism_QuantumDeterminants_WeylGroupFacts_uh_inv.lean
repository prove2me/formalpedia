-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:09.448329+00:00
-- url     : https://prove2.me/submissions/6fbd34fe-d17b-4850-a744-63a92b52c9bc

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hd := isUnit_of_uh hg
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hr : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hd
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [h1]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [mul_assoc]
    _ = Hpk k r := by rw [hr, Matrix.conjTranspose_one, one_mul, mul_one]
end Formalism.QuantumDeterminants.WeylGroupFacts
