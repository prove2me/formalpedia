-- Prove2me | solution 1 for Deformation.DieudonneModule.exact_map_hopfKerVal_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0367859b-f9e4-5efb-9d09-c661ef5393f0

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exact_map_hopfKerVal_map

set_option autoImplicit false

open Function

universe u v w

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.map_injective comulRingHom wittHom mem_wittHom_iff wittHomMap coeff_wittHomMap DieudonneModule DieudonneModule.of DieudonneModule.induction_on DieudonneModule.exists_of DieudonneModule.of_injective DieudonneModule.map DieudonneModule.map_of wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer"
p2m_open "Deformation"

namespace DieudonneMiddleExact

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
variable {B : Type w} [CommRing B] [HopfAlgebra k B] (π : A →ₐc[k] B)

p2m_open "HopfAlgebra Deformation.TruncWitt"

theorem wittHomMap_wittHomMap_hopfKerVal (x : wittHom k p n ↥(hopfKer π)) :
    wittHomMap p n π (wittHomMap p n (hopfKerVal π) x) = 0 := by
  rw [Deformation.wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer]
  intro i
  rw [coeff_wittHomMap, hopfKerVal_apply]
  exact ((x : TruncatedWittVector p n ↥(hopfKer π)).coeff i).2

theorem exists_map_eq_of_forall_coeff_mem (y : TruncatedWittVector p n A)
    (hy : ∀ i, y.coeff i ∈ hopfKer π) :
    ∃ x : TruncatedWittVector p n ↥(hopfKer π),
      TruncWitt.map ((hopfKerVal π : ↥(hopfKer π) →ₐ[k] A)).toRingHom x = y :=
  ⟨TruncatedWittVector.mk p fun i => ⟨y.coeff i, hy i⟩,
    TruncatedWittVector.ext fun i => by rw [coeff_map, TruncatedWittVector.coeff_mk]; rfl⟩

theorem mem_wittHom_of_map_mem (x : TruncatedWittVector p n ↥(hopfKer π))
    (hx : TruncWitt.map ((hopfKerVal π : ↥(hopfKer π) →ₐ[k] A)).toRingHom x ∈ wittHom k p n A) :
    x ∈ wittHom k p n ↥(hopfKer π) := by
  set C := ↥(hopfKer π)
  set ι : C →ₐ[k] A := (hopfKerVal π : C →ₐ[k] A) with hι
  rw [mem_wittHom_iff] at hx ⊢

  have hinj : Injective (HopfKerHopf.ι₂A π).toRingHom := HopfKerHopf.ι₂_injective π
  apply TruncWitt.map_injective hinj

  have hΔ : (HopfKerHopf.ι₂A π).toRingHom.comp (comulRingHom k C) =
      (comulRingHom k A).comp ι.toRingHom := by
    refine RingHom.ext fun c => ?_
    change HopfKerHopf.ι₂ π (Coalgebra.comul (R := k) c) = Coalgebra.comul (R := k) (c : A)
    exact HopfKerHopf.ι₂_comul π c
  have h₁ : (HopfKerHopf.ι₂A π).toRingHom.comp
      (Algebra.TensorProduct.includeLeft : C →ₐ[k] TensorProduct k C C).toRingHom =
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A A).toRingHom.comp
        ι.toRingHom := by
    refine RingHom.ext fun c => ?_
    rfl
  have h₂ : (HopfKerHopf.ι₂A π).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[k] TensorProduct k C C).toRingHom =
      (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k A A).toRingHom.comp
        ι.toRingHom := by
    refine RingHom.ext fun c => ?_
    rfl
  rw [map_add, map_map, map_map, map_map, hΔ, h₁, h₂, ← map_map, ← map_map, ← map_map]
  exact hx

end DieudonneMiddleExact

end Deformation

open _root_.Deformation _root_.P2MW.S_Deformation_DieudonneModule_exact_map_hopfKerVal_map.Deformation HopfAlgebra in
theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    {A : Type v} [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    {B : Type w} [CommRing B] [HopfAlgebra k B]
    (π : A →ₐc[k] B) :
    Function.Exact (Deformation.DieudonneModule.map k p (HopfAlgebra.hopfKerVal π))
      (Deformation.DieudonneModule.map k p π) := by
  intro z
  constructor
  ·
    intro hz
    obtain ⟨n, y, rfl⟩ := DieudonneModule.exists_of z
    rw [DieudonneModule.map_of] at hz
    have hy : wittHomMap p n π y = 0 :=
      DieudonneModule.of_injective n (hz.trans (map_zero _).symm)
    rw [Deformation.wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer] at hy
    obtain ⟨x, hx⟩ :=
      DieudonneMiddleExact.exists_map_eq_of_forall_coeff_mem π (y : TruncatedWittVector p n A) hy
    have hxmem : x ∈ wittHom k p n ↥(hopfKer π) :=
      DieudonneMiddleExact.mem_wittHom_of_map_mem π x (hx ▸ y.2)
    refine ⟨DieudonneModule.of k p (↥(hopfKer π)) n ⟨x, hxmem⟩, ?_⟩
    rw [DieudonneModule.map_of]
    congr 1
    exact Subtype.ext hx
  ·
    rintro ⟨w, rfl⟩
    induction w using DieudonneModule.induction_on with
    | ih n x =>
      rw [DieudonneModule.map_of, DieudonneModule.map_of,
        DieudonneMiddleExact.wittHomMap_wittHomMap_hopfKerVal, map_zero]

end S_Deformation_DieudonneModule_exact_map_hopfKerVal_map
end P2MW
export P2MW.S_Deformation_DieudonneModule_exact_map_hopfKerVal_map (solution)
