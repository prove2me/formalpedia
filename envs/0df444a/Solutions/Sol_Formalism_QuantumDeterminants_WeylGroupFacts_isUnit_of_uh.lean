-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:43.253808+00:00
-- url     : https://prove2.me/submissions/156c3168-c5d5-4cc5-a428-fd943189d263

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq

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
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 : (Hpk k r * (gᴴ * Hpk k r)) * g = 1 := by
    calc (Hpk k r * (gᴴ * Hpk k r)) * g = Hpk k r * (gᴴ * Hpk k r * g) := by
          simp only [mul_assoc]
      _ = 1 := by rw [h1, hpk_sq]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_one, mul_comm] at h3
  exact ⟨⟨_, _, h3, (mul_comm _ _).trans h3⟩, rfl⟩
end Formalism.QuantumDeterminants.WeylGroupFacts
