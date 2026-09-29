-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ffc70bb6-1d6a-5846-aa1e-9b0a83ce88ae

import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] (E : FakeEllipticCurve Λ N k) :
    SmoothOfRelativeDimension 2 E.f := by
  haveI hsm : Smooth E.f := E.bundle.smooth
  obtain ⟨d, hd⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing E.L
  let s : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k
  have hfib : E.f.base ⁻¹' {s} = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    show E.f.base x = s
    exact Subsingleton.elim _ _
  let e : ↥(E.f.base ⁻¹' {s}) ≃ₜ ↥E.A := (Homeomorph.setCongr hfib).trans (Homeomorph.Set.univ _)
  have hdim : topologicalKrullDim ↥E.A = 2 := by
    rw [← E.dim_fibre s]
    exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm
  haveI hne : Nonempty ↥E.A := by
    obtain ⟨x, -⟩ := (E.bundle.connectedFibres s).nonempty
    exact ⟨x⟩
  have h1 := AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim E.f d
  have h2 := AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le E.f d
  rw [hdim] at h1 h2
  have h3 : ((d : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ) : ℕ∞) := le_antisymm h1 h2
  have hd2 : d = 2 := by exact_mod_cast h3
  subst hd2
  exact hd

end S_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two (solution)
