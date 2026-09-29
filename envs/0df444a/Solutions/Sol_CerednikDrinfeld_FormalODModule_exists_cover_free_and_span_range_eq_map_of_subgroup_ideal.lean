-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_cover_free_and_span_range_eq_map_of_subgroup_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/629ff181-f37e-591b-af65-9443e136cf9d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_notMem_free_and_span_range_eq_map_of_subgroup_ideal_of_isMaximal
import Theorems.Thm_Ideal_exists_span_range_eq_top_of_forall_isMaximal_exists_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_cover_free_and_span_range_eq_map_of_subgroup_ideal
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
    (hvarpi : ∀ f ∈ I, MvPowerSeries.subst X.varpi f ∈ I) :
    ∃ (n : ℕ) (g : Fin n → B), Ideal.span (Set.range g) = ⊤ ∧ ∀ i : Fin n,
      Module.Finite (Localization.Away (g i)) (MvPowerSeries (Fin 2) (Localization.Away (g i)) ⧸ I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g i))))) ∧
      Module.Free (Localization.Away (g i)) (MvPowerSeries (Fin 2) (Localization.Away (g i)) ⧸ I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g i))))) ∧
      (∃ q : ℕ, ∀ i' : Fin 2, (MvPowerSeries.X i' : MvPowerSeries (Fin 2) (Localization.Away (g i))) ^ q ∈ I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g i))))) ∧
      ∃ u : Series (Localization.Away (g i)),
        (∀ j, MvPowerSeries.constantCoeff (u j) = 0) ∧
        (∀ j, MvPowerSeries.subst (X.map (algebraMap B (Localization.Away (g i)))).F.toPowerSeries (u j) - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (Localization.Away (g i)))) (u j) ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (Localization.Away (g i))))) '' ((I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g i))))) : Set (MvPowerSeries (Fin 2) (Localization.Away (g i)))))) ∧
        Ideal.span (Set.range u) = I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g i)))) := by
  let P : B → Prop := fun s =>
        Module.Finite (Localization.Away s) (MvPowerSeries (Fin 2) (Localization.Away s) ⧸ I.map (MvPowerSeries.map (algebraMap B (Localization.Away s)))) ∧
        Module.Free (Localization.Away s) (MvPowerSeries (Fin 2) (Localization.Away s) ⧸ I.map (MvPowerSeries.map (algebraMap B (Localization.Away s)))) ∧
        (∃ q : ℕ, ∀ i' : Fin 2, (MvPowerSeries.X i' : MvPowerSeries (Fin 2) (Localization.Away s)) ^ q ∈ I.map (MvPowerSeries.map (algebraMap B (Localization.Away s)))) ∧
        ∃ u : Series (Localization.Away s),
          (∀ j, MvPowerSeries.constantCoeff (u j) = 0) ∧
          (∀ j, MvPowerSeries.subst (X.map (algebraMap B (Localization.Away s))).F.toPowerSeries (u j) - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (Localization.Away s))) (u j) ∈
            Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (Localization.Away s)))) '' ((I.map (MvPowerSeries.map (algebraMap B (Localization.Away s)))) : Set (MvPowerSeries (Fin 2) (Localization.Away s))))) ∧
          Ideal.span (Set.range u) = I.map (MvPowerSeries.map (algebraMap B (Localization.Away s)))
  exact Ideal.exists_span_range_eq_top_of_forall_isMaximal_exists_notMem P (fun 𝔪 h𝔪 =>
    CerednikDrinfeld.FormalODModule.exists_notMem_free_and_span_range_eq_map_of_subgroup_ideal_of_isMaximal
      p hB X I h hfin hproj hrank hnil hunit hmul hact hvarpi 𝔪 h𝔪)

end S_CerednikDrinfeld_FormalODModule_exists_cover_free_and_span_range_eq_map_of_subgroup_ideal
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_cover_free_and_span_range_eq_map_of_subgroup_ideal (solution)
