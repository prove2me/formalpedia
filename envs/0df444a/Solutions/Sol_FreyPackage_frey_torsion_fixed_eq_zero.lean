-- Prove2me | solution 1 for FreyPackage.frey_torsion_fixed_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6b731440-af29-5896-8bac-e4dcaf816e02

import Theorems.Thm_WeierstrassCurve_Affine_Point_exists_baseChange_eq_of_forall_smul_eq
import Theorems.Thm_FreyPackage_freyCurve_rational_p_torsion_eq_zero
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_torsion_fixed_eq_zero

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (P : FreyPackage) (x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)
    (hx : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ • x = x) : x = 0 := by
  classical

  haveI hG : IsGalois ℚ (AlgebraicClosure ℚ) := by
    have h : @IsGalois ℚ _ (AlgebraicClosure ℚ) _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  have hx' : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      σ • (x : (P.freyCurve⁄(AlgebraicClosure ℚ)).Point) = x := fun σ =>
    congrArg Subtype.val (hx σ)
  obtain ⟨y, hy⟩ := Point.exists_baseChange_eq_of_forall_smul_eq P.freyCurve
    (x : (P.freyCurve⁄(AlgebraicClosure ℚ)).Point) hx'
  have hpx : (P.p : ℤ) • (x : (P.freyCurve⁄(AlgebraicClosure ℚ)).Point) = 0 :=
    (Submodule.mem_torsionBy_iff _ _).mp x.2
  have hpy : P.p • y = 0 := by
    apply Point.map_injective (Algebra.ofId ℚ (AlgebraicClosure ℚ))
    rw [map_nsmul, _root_.map_zero]
    change P.p • (Point.baseChange ℚ (AlgebraicClosure ℚ) y) = 0
    rw [hy, ← natCast_zsmul]
    exact hpx
  have hy0 : y = 0 := P.freyCurve_rational_p_torsion_eq_zero y hpy
  apply Subtype.ext
  change (x : (P.freyCurve⁄(AlgebraicClosure ℚ)).Point) = 0
  rw [← hy, hy0, _root_.map_zero]

end S_FreyPackage_frey_torsion_fixed_eq_zero
end P2MW
export P2MW.S_FreyPackage_frey_torsion_fixed_eq_zero (solution)
