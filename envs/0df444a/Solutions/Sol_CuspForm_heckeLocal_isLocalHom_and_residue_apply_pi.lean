-- Prove2me | solution 1 for CuspForm.heckeLocal.isLocalHom_and_residue_apply_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a823027b-cc83-5bf8-a0ef-857133642e53

import Definitions.Def_CuspForm_HeckeLocal
import Mathlib.RingTheory.Ideal.GoingUp
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_isLocalHom_and_residue_apply_pi

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open IsLocalRing

theorem solution
    (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    {𝒪' : Type} [CommRing 𝒪'] [IsLocalRing 𝒪'] [Algebra 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
    (ψ : CuspForm.heckeLocal N S 𝒪 θ →ₐ[𝒪] 𝒪') :
    IsLocalHom (ψ : CuspForm.heckeLocal N S 𝒪 θ →+* 𝒪') ∧
    ∀ t : ↥(CuspForm.heckeAlgebra N 2 S),
      IsLocalRing.residue 𝒪' (ψ (CuspForm.heckeLocal.π N S 𝒪 θ t)) =
        IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') (θ t) := by
  set T := CuspForm.heckeLocal N S 𝒪 θ

  let P : Ideal T := (maximalIdeal 𝒪').comap (ψ : T →+* 𝒪')
  haveI hPp : P.IsPrime := Ideal.IsPrime.comap _
  have hPO : P.comap (algebraMap 𝒪 T) = maximalIdeal 𝒪 := by
    have h1 : P.comap (algebraMap 𝒪 T) = (maximalIdeal 𝒪').comap (algebraMap 𝒪 𝒪') := by
      rw [Ideal.comap_comap]
      congr 1
      ext a
      simp
    rw [h1]
    have hle : maximalIdeal 𝒪 ≤ (maximalIdeal 𝒪').comap (algebraMap 𝒪 𝒪') := fun a ha => by
      rw [Ideal.mem_comap]
      exact map_nonunit (algebraMap 𝒪 𝒪') a ha
    exact ((maximalIdeal.isMaximal 𝒪).eq_of_le
      (Ideal.comap_ne_top _ (maximalIdeal.isMaximal 𝒪').ne_top) hle).symm
  haveI : Algebra.IsIntegral 𝒪 T := Algebra.IsIntegral.of_finite 𝒪 T
  have hPmax : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝒪) P (by rw [hPO]; exact maximalIdeal.isMaximal 𝒪)
  have hPeq : P = maximalIdeal T := (IsLocalRing.eq_maximalIdeal hPmax)
  have hloc : IsLocalHom (ψ : T →+* 𝒪') := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hxP : x ∈ P := by rw [hPeq]; exact hnu
    exact ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp hxP)) hx
  refine ⟨hloc, fun t => ?_⟩
  haveI := hloc
  show residue 𝒪' ((ψ : T →+* 𝒪') (CuspForm.heckeLocal.π N S 𝒪 θ t)) = _
  rw [← IsLocalRing.ResidueField.map_residue (ψ : T →+* 𝒪'), CuspForm.heckeLocal.residue_pi N S 𝒪 θ t,
    IsLocalRing.ResidueField.map_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (θ t)
  rw [← ha]
  change IsLocalRing.ResidueField.map _ (IsLocalRing.residue 𝒪 a) = IsLocalRing.ResidueField.map _ (IsLocalRing.residue 𝒪 a)
  rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue, RingHom.comp_apply]
  congr 1
  exact ψ.commutes a

end S_CuspForm_heckeLocal_isLocalHom_and_residue_apply_pi
end P2MW
export P2MW.S_CuspForm_heckeLocal_isLocalHom_and_residue_apply_pi (solution)
