-- Prove2me | solution 1 for Formalism.L2.Th1.H.cayley_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:26:18.214282+00:00
-- url     : https://prove2.me/submissions/fbf3604b-6b78-45a5-8474-14e39de68610

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (H : Sesq V) (δ Ae : V ≃ₗ[ℂ] V) (hδ : IsIsom H H (δ : V →ₗ[ℂ] V))
    (hAe : ∀ x, Ae x = x - δ.symm x) (u v : V) : H (Ae u) v + H u (Ae v) = H (Ae u) (Ae v) := by
  have key : H (δ.symm u) (δ.symm v) = H u v := by
    have h := hδ (δ.symm u) (δ.symm v)
    simpa using h.symm
  simp only [hAe, map_sub, LinearMap.sub_apply]
  rw [key]
  ring
end Formalism.L2.Th1.H
