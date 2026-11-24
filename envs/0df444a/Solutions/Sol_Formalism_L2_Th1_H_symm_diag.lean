-- Prove2me | solution 1 for Formalism.L2.Th1.H.symm_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:27:28.012293+00:00
-- url     : https://prove2.me/submissions/16c475fb-7e42-4606-9fc4-755ceda82acd

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
theorem _root_.solution [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, H (T x) y = H x (T y)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (t : Fin (Module.finrank ℂ V) → ℝ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ ∀ i, T (b i) = (t i : ℂ) • b i := by
  letI cd : InnerProductSpace.Core ℂ V := coreOf H hH hP
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ cd
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  haveI : FiniteDimensional ℂ V := ‹FiniteDimensional ℂ V›
  have hS : LinearMap.IsSymmetric T := fun x y => (hT y x).symm
  let b := hS.eigenvectorBasis rfl
  refine ⟨b.toBasis, fun i => hS.eigenvalues rfl i, ?_, ?_⟩
  · intro i j
    rw [OrthonormalBasis.coe_toBasis]
    have h := (orthonormal_iff_ite.mp b.orthonormal) j i
    exact h.trans (if_congr eq_comm rfl rfl)
  · intro i
    rw [OrthonormalBasis.coe_toBasis]
    exact hS.apply_eigenvectorBasis rfl i
end Formalism.L2.Th1.H
