-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_coe_eq_nsmulAlgHom_and_map_eq_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c9e8c681-95cd-53c9-bc22-f78626101d11

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_coe_eq_nsmulAlgHom_and_map_eq_nsmul

universe u v

set_option autoImplicit false

namespace R4K4cMAdd

open WithConv

private theorem map_nsmulAlgHom_of_mem_wittHom
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {m : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A]
    {x : TruncatedWittVector p m A} (hx : x ∈ Deformation.wittHom R p m A) (n : ℕ) :
    Deformation.TruncWitt.map (PDivisibleGroup.Hopf.nsmulAlgHom R A n).toRingHom x = n • x := by
  induction n with
  | zero =>
    have hfac : (PDivisibleGroup.Hopf.nsmulAlgHom R A 0).toRingHom =
        (algebraMap R A).comp (Bialgebra.counitAlgHom R A).toRingHom := by
      refine RingHom.ext fun a => ?_
      change PDivisibleGroup.Hopf.nsmulAlgHom R A 0 a = _
      rw [PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply]
      rfl
    rw [hfac, ← Deformation.TruncWitt.map_map, Deformation.map_counit_of_mem_wittHom hx, map_zero,
      zero_smul]
  | succ n ih =>
    have h := Deformation.map_convMul_of_mem_wittHom (T := A) hx
      (toConv (PDivisibleGroup.Hopf.nsmulAlgHom R A n)) (toConv (AlgHom.id R A))
    rw [PDivisibleGroup.Hopf.nsmulAlgHom_succ, h, add_smul, one_smul]
    change Deformation.TruncWitt.map (PDivisibleGroup.Hopf.nsmulAlgHom R A n).toRingHom x +
      Deformation.TruncWitt.map (RingHom.id A) x = _
    rw [ih, Deformation.TruncWitt.map_id]

end R4K4cMAdd

theorem solution
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A] (n : ℕ) :
    ∃ φ : A →ₐc[R] A, (φ : A →ₐ[R] A) = PDivisibleGroup.Hopf.nsmulAlgHom R A n ∧
      ∀ z : Deformation.DieudonneModule R p A,
        Deformation.DieudonneModule.map R p φ z = n • z := by
  classical

  let φ : A →ₐc[R] A := ((WithConv.toConv (BialgHom.id R A)) ^ n).ofConv
  have hφ : φ.toAlgHom = PDivisibleGroup.Hopf.nsmulAlgHom R A n := by
    have h := BialgHom.toAlgHom_convPow (WithConv.toConv (BialgHom.id R A)) n
    rw [WithConv.toConv_ofConv] at h
    change WithConv.toConv φ.toAlgHom = WithConv.toConv (AlgHom.id R A) ^ n at h
    exact (congrArg WithConv.ofConv h).trans rfl
  have hφ' : (φ : A →ₐ[R] A) = PDivisibleGroup.Hopf.nsmulAlgHom R A n := by
    rw [← hφ]
  refine ⟨φ, hφ', fun z => ?_⟩
  obtain ⟨m, x, rfl⟩ := Deformation.DieudonneModule.exists_of z
  rw [Deformation.DieudonneModule.map_of, ← map_nsmul]
  congr 1
  refine Subtype.ext ?_
  rw [Deformation.coe_wittHomMap, hφ', AddSubgroup.coe_nsmul]
  exact R4K4cMAdd.map_nsmulAlgHom_of_mem_wittHom x.2 n

end S_Deformation_DieudonneModule_exists_coe_eq_nsmulAlgHom_and_map_eq_nsmul
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_coe_eq_nsmulAlgHom_and_map_eq_nsmul (solution)
