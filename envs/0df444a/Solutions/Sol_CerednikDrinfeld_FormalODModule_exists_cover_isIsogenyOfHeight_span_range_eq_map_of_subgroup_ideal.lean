-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_cover_isIsogenyOfHeight_span_range_eq_map_of_subgroup_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d835ba33-573a-50d3-9984-68169572a812

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_cover_invariant_coordinates_of_subgroup_ideal
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isIsogenyOfHeight_of_invariant_coordinates
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subgroup_ideal_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_cover_isIsogenyOfHeight_span_range_eq_map_of_subgroup_ideal
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
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
      ∃ (Y : FormalODModule p (Localization.Away (g i))) (ρ : Series (Localization.Away (g i))),
        FormalODModule.IsIsogenyOfHeight (X.map (algebraMap B (Localization.Away (g i)))) Y ρ h ∧
        Ideal.span (Set.range ρ) = I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g i)))) := by
  obtain ⟨n, g, hg, hu⟩ := CerednikDrinfeld.FormalODModule.exists_cover_invariant_coordinates_of_subgroup_ideal p hB X I h hfin hproj hrank
    hnil hunit hmul hact hvarpi
  refine ⟨n, g, hg, fun i => ?_⟩
  obtain ⟨u, hu0, huinv, huI, hcoord⟩ := hu i
  have hB' : IsNilpotent ((p : ℕ) : Localization.Away (g i)) := by
    rw [← map_natCast (algebraMap B (Localization.Away (g i)))]; exact hB.map _
  haveI : IsNoetherianRing (Localization.Away (g i)) := IsLocalization.isNoetherianRing (Submonoid.powers (g i)) _ inferInstance
  obtain ⟨hfin', hproj', hrank', hnil', hunit', hmul', hact', hvarpi'⟩ :=
    CerednikDrinfeld.FormalODModule.subgroup_ideal_map p hB X I h hfin hproj hrank hnil hunit hmul hact hvarpi
      (algebraMap B (Localization.Away (g i)))
  obtain ⟨Y, hY⟩ := CerednikDrinfeld.FormalODModule.exists_isIsogenyOfHeight_of_invariant_coordinates p hB'
    (X.map (algebraMap B (Localization.Away (g i)))) (I.map (MvPowerSeries.map (algebraMap B (Localization.Away (g i))))) h
    hfin' hproj' hrank' hnil' hunit' hmul' hact' hvarpi' u hu0 huinv huI hcoord
  exact ⟨Y, u, hY, huI⟩

end S_CerednikDrinfeld_FormalODModule_exists_cover_isIsogenyOfHeight_span_range_eq_map_of_subgroup_ideal
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_cover_isIsogenyOfHeight_span_range_eq_map_of_subgroup_ideal (solution)
