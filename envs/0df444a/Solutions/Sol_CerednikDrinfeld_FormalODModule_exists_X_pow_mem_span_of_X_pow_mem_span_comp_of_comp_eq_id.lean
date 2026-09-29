-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_X_pow_mem_span_comp_of_comp_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b9cf8bd9-d488-5a10-89c6-d0bc2f588c38

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp_of_comp_eq_id

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace NilpCoords

variable {B : Type} [CommRing B]

theorem mem_span_X_of_constantCoeff_eq_zero (g : MvPowerSeries (Fin 2) B)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    g ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B)) := by
  have h1 := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 g (fun m hm => by
    have hm0 : m = 0 := by
      rw [Nat.lt_one_iff] at hm
      exact (Finsupp.degree_eq_zero_iff m).mp hm
    subst hm0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hg)
  rwa [pow_one] at h1

theorem map_span_range_eq {φ ψ : Series B} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    Ideal.map (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0)).toRingHom
      (Ideal.span (Set.range ψ)) = Ideal.span (Set.range (ψ.comp φ)) := by
  rw [Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨j, ?_⟩
    show MvPowerSeries.subst φ (ψ j) = _
    rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0)]
    rfl
  · rintro ⟨j, rfl⟩
    refine ⟨ψ j, ⟨j, rfl⟩, ?_⟩
    show _ = MvPowerSeries.subst φ (ψ j)
    rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0)]
    rfl

theorem pow_mem_span_comp {φ ψ : Series B} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    {N : ℕ} {i : Fin 2}
    (h : (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range ψ)) :
    φ i ^ N ∈ Ideal.span (Set.range (ψ.comp φ)) := by
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have hmap := Ideal.mem_map_of_mem (MvPowerSeries.substAlgHom ha).toRingHom h
  rw [map_span_range_eq hφ0, map_pow] at hmap
  have hX : (MvPowerSeries.substAlgHom ha).toRingHom (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) = φ i := by
    show MvPowerSeries.substAlgHom ha (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) = φ i
    rw [MvPowerSeries.substAlgHom_X]
  rwa [hX] at hmap

theorem subst_mem_span {φ : Series B} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (g : MvPowerSeries (Fin 2) B) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst φ g ∈ Ideal.span (Set.range φ) := by
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have h := Ideal.mem_map_of_mem (MvPowerSeries.substAlgHom ha).toRingHom
    (mem_span_X_of_constantCoeff_eq_zero g hg)
  have heq : Ideal.map (MvPowerSeries.substAlgHom ha).toRingHom
      (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))) =
      Ideal.span (Set.range φ) := by
    have h2 := map_span_range_eq (ψ := Series.id B) hφ0
    rw [Series.id_comp φ hφ0] at h2
    exact h2
  rw [heq] at h
  rw [← MvPowerSeries.coe_substAlgHom ha]
  exact h

theorem span_pow_le {φ : Series B} {M : ℕ} {J : Ideal (MvPowerSeries (Fin 2) B)}
    (h : ∀ i, φ i ^ M ∈ J) : Ideal.span (Set.range φ) ^ (M + M) ≤ J := by
  have hI : Ideal.span (Set.range φ) ≤ Ideal.span {φ 0} ⊔ Ideal.span {φ 1} := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  refine (Ideal.pow_right_mono hI _).trans ?_
  refine Ideal.sup_pow_add_le_pow_sup_pow.trans ?_
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
  refine sup_le ?_ ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact h 0
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact h 1

end NilpCoords

theorem solution
    {B : Type} [CommRing B] {φ u v : Series B}
    (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
    (huv : u.comp v = Series.id B)
    (h : ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range (φ.comp u))) :
    ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ) := by
  obtain ⟨N, hN⟩ := h

  have hcomp : (φ.comp u).comp v = φ := by
    rw [Series.comp_assoc φ u v hu0 hv0, huv, Series.comp_id]

  have h1 : ∀ i : Fin 2, v i ^ N ∈ Ideal.span (Set.range φ) := by
    intro i
    have h := NilpCoords.pow_mem_span_comp (ψ := φ.comp u) hv0 (hN i)
    rwa [hcomp] at h

  have h2 : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ∈ Ideal.span (Set.range v) := by
    intro i
    have hx : MvPowerSeries.subst v (u i) = MvPowerSeries.X i := congrFun huv i
    rw [← hx]
    exact NilpCoords.subst_mem_span hv0 (u i) (hu0 i)
  refine ⟨N + N, fun i => ?_⟩
  exact NilpCoords.span_pow_le h1 (Ideal.pow_mem_pow (h2 i) _)

end S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp_of_comp_eq_id
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp_of_comp_eq_id (solution)
