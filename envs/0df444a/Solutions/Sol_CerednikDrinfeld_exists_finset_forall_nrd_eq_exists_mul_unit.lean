-- Prove2me | solution 1 for CerednikDrinfeld.exists_finset_forall_nrd_eq_exists_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/77a0734b-f0f1-5c09-ad75-bd1873566b32

import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_finset_forall_nrd_eq_exists_mul_unit

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

namespace CPTd

variable {a b : ℚ}

theorem isTorsionFree_int : Module.IsTorsionFree ℤ ℍ[ℚ, a, b] :=
  Module.IsTorsionFree.of_smul_eq_zero fun z m h => by
    rw [← Int.cast_smul_eq_zsmul ℚ] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact_mod_cast h
    · right; exact h

theorem star_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℍ[ℚ, a, b]} (hr : r ∈ R) : star r ∈ R := by
  obtain ⟨-, t, ht⟩ := hR.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hr
  have h : star r = ((trd r : ℚ) : ℍ[ℚ, a, b]) - r := by
    rw [← add_star_eq_coe_trd]; abel
  rw [h, ← ht, QuaternionAlgebra.coe_intCast, ← zsmul_one]
  exact R.sub_mem (R.smul_mem t hR.one_mem) hr

theorem nrd_ne_zero (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) {x : ℍ[ℚ, a, b]} (hx : x ≠ 0) : nrd x ≠ 0 := by
  intro h0
  obtain ⟨u, rfl⟩ := hdiv x hx
  have h := nrd_mul (u : ℍ[ℚ, a, b]) (↑u⁻¹ : ℍ[ℚ, a, b])
  rw [Units.mul_inv, nrd_one, h0, zero_mul] at h
  exact one_ne_zero h

end CPTd

open CPTd in

theorem solution {a b : ℚ} (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (n : ℚ) :
    ∃ T : Finset ℍ[ℚ, a, b], (↑T : Set ℍ[ℚ, a, b]) ⊆ R ∧
      ∀ r ∈ R, nrd r = n → ∃ t ∈ T, ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ r = t * u := by
  classical
  by_cases hex : ∃ r₀ ∈ R, nrd r₀ = n
  swap
  · exact ⟨∅, by simp, fun r hr hrn => (hex ⟨r, hr, hrn⟩).elim⟩
  obtain ⟨r₀, hr₀, hr₀n⟩ := hex
  obtain ⟨⟨N, hN⟩, -⟩ := hR.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hr₀
  rw [hr₀n] at hN
  by_cases hN0 : N = 0
  · subst hN0
    refine ⟨{0}, by simp, fun r hr hrn => ⟨0, Finset.mem_singleton_self 0, 1,
      ⟨hR.one_mem, 1, hR.one_mem, one_mul 1, one_mul 1⟩, nrd_one, ?_⟩⟩
    rw [zero_mul]
    by_contra hr0
    exact nrd_ne_zero hdiv hr0 (by rw [hrn, ← hN]; simp)

  let I : ℍ[ℚ, a, b] → Submodule ℤ ℍ[ℚ, a, b] := fun r => R.map (AddMonoidHom.mulLeft r).toIntLinearMap
  have hmemI : ∀ r x : ℍ[ℚ, a, b], x ∈ I r ↔ ∃ y ∈ R, r * y = x := by
    intro r x
    simp only [I, Submodule.mem_map]
    rfl
  have hIle : ∀ r ∈ R, I r ≤ R := by
    intro r hr x hx
    obtain ⟨y, hy, rfl⟩ := (hmemI r x).mp hx
    exact hR.mul_mem hr hy
  have hself : ∀ r ∈ R, r ∈ I r := fun r hr => (hmemI r r).mpr ⟨1, hR.one_mem, mul_one r⟩
  have hNmem : ∀ r ∈ R, nrd r = n → ∀ x ∈ R, (N : ℤ) • x ∈ I r := by
    intro r hr hrn x hx
    refine (hmemI r _).mpr ⟨star r * x, hR.mul_mem (star_mem hR hr) hx, ?_⟩
    rw [← mul_assoc, mul_star_eq_coe_nrd, hrn, ← hN, QuaternionAlgebra.coe_intCast, zsmul_eq_mul]

  haveI : Module.Finite ℤ ↥R := Module.Finite.iff_fg.mpr hR.fg
  haveI : Module.IsTorsionFree ℤ ↥R :=
    Module.IsTorsionFree.of_smul_eq_zero fun z m h => by
      have h' : ((z : ℚ)) • (m : ℍ[ℚ, a, b]) = 0 := by
        rw [Int.cast_smul_eq_zsmul, ← Submodule.coe_smul, h, Submodule.coe_zero]
      rcases smul_eq_zero.mp h' with h'' | h''
      · left; exact_mod_cast h''
      · right; exact Subtype.ext h''
  let P : Submodule ℤ ↥R := LinearMap.range (LinearMap.lsmul ℤ ↥R N)
  haveI : Finite (↥R ⧸ P) :=
    (Submodule.finiteQuotient_iff P).mpr (LinearMap.finrank_range_of_inj (LinearMap.lsmul_injective hN0))
  haveI : Finite (Submodule ℤ (↥R ⧸ P)) :=
    Finite.of_injective (fun q : Submodule ℤ (↥R ⧸ P) => (q : Set (↥R ⧸ P))) SetLike.coe_injective
  let F : Submodule ℤ ℍ[ℚ, a, b] → Submodule ℤ (↥R ⧸ P) := fun J => (J.comap R.subtype).map P.mkQ
  let S : Set (Submodule ℤ ℍ[ℚ, a, b]) := {J | ∃ r ∈ R, nrd r = n ∧ I r = J}
  have hPle : ∀ J ∈ S, P ≤ J.comap R.subtype := by
    rintro J ⟨r, hr, hrn, rfl⟩ y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, Submodule.subtype_apply, Submodule.coe_smul]
    exact hNmem r hr hrn x x.2
  have hSle : ∀ J ∈ S, J ≤ R := by
    rintro J ⟨r, hr, hrn, rfl⟩
    exact hIle r hr
  have hSfin : S.Finite := by
    refine Set.Finite.of_finite_image (f := F) (Set.toFinite _) ?_
    have key : ∀ J ∈ S, Submodule.map R.subtype (Submodule.comap P.mkQ (F J)) = J := by
      intro J hJ
      show Submodule.map R.subtype (Submodule.comap P.mkQ
        (Submodule.map P.mkQ (Submodule.comap R.subtype J))) = J
      rw [Submodule.comap_map_mkQ, sup_eq_right.mpr (hPle J hJ), Submodule.map_comap_subtype,
        inf_eq_right.mpr (hSle J hJ)]
    intro J hJ J' hJ' hFF
    rw [← key J hJ, ← key J' hJ', hFF]

  let rep : Submodule ℤ ℍ[ℚ, a, b] → ℍ[ℚ, a, b] := fun J => if h : J ∈ S then h.choose else 0
  have hrep : ∀ J (h : J ∈ S), rep J ∈ R ∧ nrd (rep J) = n ∧ I (rep J) = J := by
    intro J h
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨hSfin.toFinset.image rep, ?_, ?_⟩
  · intro t ht
    rw [Finset.coe_image] at ht
    obtain ⟨J, hJ, rfl⟩ := ht
    exact (hrep J (hSfin.mem_toFinset.mp hJ)).1
  intro r hr hrn
  have hJ : I r ∈ S := ⟨r, hr, hrn, rfl⟩
  obtain ⟨htR, htn, htI⟩ := hrep (I r) hJ
  set t := rep (I r) with ht
  refine ⟨t, Finset.mem_image.mpr ⟨I r, hSfin.mem_toFinset.mpr hJ, rfl⟩, ?_⟩

  obtain ⟨u, hu, htu⟩ := (hmemI t r).mp (htI ▸ hself r hr)
  obtain ⟨u', hu', hru'⟩ := (hmemI r t).mp (htI.symm ▸ hself t htR)
  have hn0 : n ≠ 0 := by rw [← hN]; exact_mod_cast hN0
  have hr0 : r ≠ 0 := by rintro rfl; exact hn0 (by rw [← hrn, nrd_zero])
  have ht0 : t ≠ 0 := by rintro h0; exact hn0 (by rw [← htn, h0, nrd_zero])
  have h1 : u' * u = 1 := (hdiv r hr0).mul_left_cancel (by rw [← mul_assoc, hru', htu, mul_one])
  have h2 : u * u' = 1 := (hdiv t ht0).mul_left_cancel (by rw [← mul_assoc, htu, hru', mul_one])
  refine ⟨u, ⟨hu, u', hu', h2, h1⟩, ?_, htu.symm⟩
  have hm := nrd_mul t u
  rw [htu, hrn, htn] at hm
  exact (mul_eq_left₀ hn0).mp hm.symm

end S_CerednikDrinfeld_exists_finset_forall_nrd_eq_exists_mul_unit
end P2MW
export P2MW.S_CerednikDrinfeld_exists_finset_forall_nrd_eq_exists_mul_unit (solution)
