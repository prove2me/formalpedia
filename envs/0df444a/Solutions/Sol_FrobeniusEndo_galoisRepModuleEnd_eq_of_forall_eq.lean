-- Prove2me | solution 1 for FrobeniusEndo.galoisRepModuleEnd_eq_of_forall_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a654b6f7-3d82-5e04-96ae-684d833c3162

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.ZMod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.OfAssociative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_galoisRepModuleEnd_eq_of_forall_eq

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem solution {R : Type*} [CommRing R] {S : Type*} [CommRing S] {S' : Type*} [CommRing S']
    {k : Type*} [Field k] [DecidableEq k] [Algebra R S] [Algebra R S'] [Algebra R k] [Algebra S k] [Algebra S' k]
    [IsScalarTower R S k] [IsScalarTower R S' k]
    (W : WeierstrassCurve R) (σ : k ≃ₐ[S] k) (τ : k ≃ₐ[S'] k) (h : ∀ x : k, σ x = τ x) (p : ℕ) :
    galoisRepModuleEnd S W p σ = galoisRepModuleEnd S' W p τ ∧
      galoisTrace S W p σ = galoisTrace S' W p τ ∧
      LinearMap.det (galoisRepModuleEnd S W p σ) = LinearMap.det (galoisRepModuleEnd S' W p τ) := by

  have hs : ∀ P : (W⁄k).Point, σ • P = τ • P := by
    intro P
    rcases P with _ | ⟨x, y, hP⟩
    · rfl
    · rw [algEquiv_smul_def, algEquiv_smul_def, Point.map_some, Point.map_some]
      have hx : σ.toAlgHom x = τ.toAlgHom x := h x
      have hy : σ.toAlgHom y = τ.toAlgHom y := h y
      simp only [hx, hy]
  have hRep : galoisRepModuleEnd S W p σ = galoisRepModuleEnd S' W p τ := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    exact hs P
  refine ⟨hRep, ?_, ?_⟩
  · rw [galoisTrace_def, galoisTrace_def, hRep]
  · rw [hRep]

end S_FrobeniusEndo_galoisRepModuleEnd_eq_of_forall_eq
end P2MW
export P2MW.S_FrobeniusEndo_galoisRepModuleEnd_eq_of_forall_eq (solution)
