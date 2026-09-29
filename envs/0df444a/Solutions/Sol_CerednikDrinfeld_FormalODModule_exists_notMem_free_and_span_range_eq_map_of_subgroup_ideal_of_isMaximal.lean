-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_notMem_free_and_span_range_eq_map_of_subgroup_ideal_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5b2a92f4-b5a7-5494-a76d-859d1122cc6d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subgroup_ideal_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_span_setOf_invariant_of_subgroup_ideal_of_free
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_pair_invariant_forall_exists_coeff_sub_mem_of_isMaximal
import Theorems.Thm_MvPowerSeries_exists_notMem_and_forall_span_pair_map_eq_map_of_forall_exists_coeff_sub_mem
import Theorems.Thm_CerednikDrinfeld_FormalODModule_map_mem_setOf_invariant_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_notMem_free_and_span_range_eq_map_of_subgroup_ideal_of_isMaximal
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] (hB : IsNilpotent (p : B))
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B)) (h : ℕ)

    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hrank : ∀ (κ : Type) [Field κ] (f : B →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ I.map (MvPowerSeries.map f)) = p ^ h)

    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)

    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))

    (hact : ∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst (X.act a) f ∈ I)
    (hvarpi : ∀ f ∈ I, MvPowerSeries.subst X.varpi f ∈ I)
    (𝔪 : Ideal B) (h𝔪 : 𝔪.IsMaximal) :
    ∃ s : B, s ∉ 𝔪 ∧
      Module.Finite (Localization.Away s) (MvPowerSeries (Fin 2) (Localization.Away s) ⧸ I.map (MvPowerSeries.map (algebraMap B (Localization.Away s)))) ∧
      Module.Free (Localization.Away s) (MvPowerSeries (Fin 2) (Localization.Away s) ⧸ I.map (MvPowerSeries.map (algebraMap B (Localization.Away s)))) ∧
      (∃ q : ℕ, ∀ i' : Fin 2, (MvPowerSeries.X i' : MvPowerSeries (Fin 2) (Localization.Away s)) ^ q ∈ I.map (MvPowerSeries.map (algebraMap B (Localization.Away s)))) ∧
      ∃ u : Series (Localization.Away s),
        (∀ j, MvPowerSeries.constantCoeff (u j) = 0) ∧
        (∀ j, MvPowerSeries.subst (X.map (algebraMap B (Localization.Away s))).F.toPowerSeries (u j) - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (Localization.Away s))) (u j) ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (Localization.Away s)))) '' ((I.map (MvPowerSeries.map (algebraMap B (Localization.Away s)))) : Set (MvPowerSeries (Fin 2) (Localization.Away s))))) ∧
        Ideal.span (Set.range u) = I.map (MvPowerSeries.map (algebraMap B (Localization.Away s))) := by
  classical

  obtain ⟨g, hg𝔪, hfreeAll⟩ :=
    MvPowerSeries.exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal I hfin hproj hnil 𝔪 h𝔪

  obtain ⟨hfinR, hprojR, -, hnilR, hunitR, hmulR, -, -⟩ :=
    CerednikDrinfeld.FormalODModule.subgroup_ideal_map p hB X I h hfin hproj hrank hnil hunit hmul hact hvarpi
      (algebraMap B (Localization.Away g))
  haveI : IsNoetherianRing (Localization.Away g) :=
    IsLocalization.isNoetherianRing (Submonoid.powers g) (Localization.Away g) inferInstance
  have hgR : IsUnit (algebraMap B (Localization.Away g) g) := IsLocalization.Away.algebraMap_isUnit g
  have hfreeR := hfreeAll (Localization.Away g) hgR

  have hInv := CerednikDrinfeld.FormalODModule.eq_span_setOf_invariant_of_subgroup_ideal_of_free p
    (X.map (algebraMap B (Localization.Away g))) (I.map (MvPowerSeries.map (algebraMap B (Localization.Away g))))
    hfinR hfreeR hnilR hunitR hmulR

  have h𝔪R : (Ideal.map (algebraMap B (Localization.Away g)) 𝔪).IsPrime := by
    apply IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g) 𝔪 h𝔪.isPrime
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hg𝔪 (h𝔪.isPrime.mem_of_pow_mem k hk)
  obtain ⟨𝔫, h𝔫, h𝔪𝔫⟩ := Ideal.exists_le_maximal _ h𝔪R.ne_top

  obtain ⟨r, hrInv, hgen⟩ :=
    CerednikDrinfeld.FormalODModule.exists_pair_invariant_forall_exists_coeff_sub_mem_of_isMaximal p
      (X.map (algebraMap B (Localization.Away g))) (I.map (MvPowerSeries.map (algebraMap B (Localization.Away g))))
      hfinR hnilR hunitR hInv 𝔫 h𝔫

  obtain ⟨g', hg'𝔫, hspan⟩ :=
    MvPowerSeries.exists_notMem_and_forall_span_pair_map_eq_map_of_forall_exists_coeff_sub_mem
      (I.map (MvPowerSeries.map (algebraMap B (Localization.Away g)))) hprojR 𝔫 h𝔫.ne_top r (fun j => (hrInv j).1) hgen

  obtain ⟨k, b, hb⟩ := IsLocalization.Away.surj g g'
  have hb𝔪 : b ∉ 𝔪 := by
    intro hbm
    apply hg'𝔫
    have h1 : algebraMap B (Localization.Away g) b ∈ 𝔫 := h𝔪𝔫 (Ideal.mem_map_of_mem _ hbm)
    rw [← hb] at h1
    rcases h𝔫.isPrime.mem_or_mem h1 with h2 | h2
    · exact h2
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h2 (IsLocalization.Away.algebraMap_pow_isUnit g k)) h𝔫.ne_top
  refine ⟨g * b, fun hmem => (h𝔪.isPrime.mem_or_mem hmem).elim hg𝔪 hb𝔪, ?_⟩

  have hgS : IsUnit (algebraMap B (Localization.Away (g * b)) g) :=
    IsLocalization.Away.isUnit_of_dvd (g * b) (Dvd.intro b rfl)
  have hbS : IsUnit (algebraMap B (Localization.Away (g * b)) b) :=
    IsLocalization.Away.isUnit_of_dvd (g * b) (Dvd.intro_left g rfl)
  letI algRS : Algebra (Localization.Away g) (Localization.Away (g * b)) :=
    (IsLocalization.Away.lift g hgS).toAlgebra
  have hcomp : (algebraMap (Localization.Away g) (Localization.Away (g * b))).comp (algebraMap B (Localization.Away g)) =
      algebraMap B (Localization.Away (g * b)) :=
    IsLocalization.Away.lift_comp g hgS
  haveI : IsScalarTower B (Localization.Away g) (Localization.Away (g * b)) :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hcomp x).symm
  have hg'S : IsUnit (algebraMap (Localization.Away g) (Localization.Away (g * b)) g') := by
    have h1 := congrArg (algebraMap (Localization.Away g) (Localization.Away (g * b))) hb
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    exact isUnit_of_mul_isUnit_left (h1.symm ▸ hbS)

  obtain ⟨hfinS, -, -, hnilS, -, -, -, -⟩ :=
    CerednikDrinfeld.FormalODModule.subgroup_ideal_map p hB X I h hfin hproj hrank hnil hunit hmul hact hvarpi
      (algebraMap B (Localization.Away (g * b)))
  have hIJ : (I.map (MvPowerSeries.map (algebraMap B (Localization.Away g)))).map
      (MvPowerSeries.map (algebraMap (Localization.Away g) (Localization.Away (g * b)))) =
      I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g * b)))) := by
    rw [Ideal.map_map, ← MvPowerSeries.map_comp, hcomp]
  have hXX : (X.map (algebraMap B (Localization.Away g))).map (algebraMap (Localization.Away g) (Localization.Away (g * b))) =
      X.map (algebraMap B (Localization.Away (g * b))) := by
    rw [FormalODModule.map_map, hcomp]
  refine ⟨hfinS, hfreeAll _ (IsLocalization.Away.isUnit_of_dvd (g * b) (Dvd.intro b rfl)), hnilS,
    fun j => MvPowerSeries.map (algebraMap (Localization.Away g) (Localization.Away (g * b))) (r j), ?_, ?_, ?_⟩
  · intro j
    rw [MvPowerSeries.constantCoeff_map, hunitR _ (hrInv j).1, map_zero]
  · intro j
    have := CerednikDrinfeld.FormalODModule.map_mem_setOf_invariant_of_mem p
      (X.map (algebraMap B (Localization.Away g))) (I.map (MvPowerSeries.map (algebraMap B (Localization.Away g))))
      (algebraMap (Localization.Away g) (Localization.Away (g * b))) (r j) (hrInv j)
    rw [hIJ, hXX] at this
    exact this.2
  · rw [← hIJ]
    exact hspan _ hg'S

end S_CerednikDrinfeld_FormalODModule_exists_notMem_free_and_span_range_eq_map_of_subgroup_ideal_of_isMaximal
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_notMem_free_and_span_range_eq_map_of_subgroup_ideal_of_isMaximal (solution)
