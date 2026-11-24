-- Prove2me | solution 1 for Formalism.L2.Th1.H.unitary_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:22.774474+00:00
-- url     : https://prove2.me/submissions/42d876f5-e636-46b4-bc44-8eb3fc53d51d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
import Theorems.Thm_Formalism_L2_Th1_H_cayley_diag
import Theorems.Thm_Formalism_L2_Th1_H_cayley_identity

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
theorem _root_.solution [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (δ Ae : V ≃ₗ[ℂ] V)
    (hδ : IsIsom H H (δ : V →ₗ[ℂ] V)) (hAe : ∀ x, Ae x = x - δ.symm x) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (l : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ (∀ i, Ae (b i) = l i • b i) ∧ ∀ i, 0 < (l i).re :=
  cayley_diag H hH hP Ae (cayley_identity H δ Ae hδ hAe)
end Formalism.L2.Th1.H
