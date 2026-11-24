-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_quad_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:47.978877+00:00
-- url     : https://prove2.me/submissions/5afd0074-862e-45e1-ab3f-8196389bdabd

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Theorems.Thm_Formalism_QuantumDeterminants_gn_gramM_eq

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
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    star c ⬝ᵥ (gramM k r z z' g *ᵥ c) =
      herm (Hpk k r) (gnB k r z z' g *ᵥ c) (gnB k r z z' g *ᵥ c) := by
  rw [gn_gramM_eq]
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
end Formalism.QuantumDeterminants
