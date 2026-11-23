-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.glue_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:41.205525+00:00
-- url     : https://prove2.me/submissions/c03dd510-d9f0-4d3e-af9c-3a246c83e769

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_lg
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_sep
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution (hR : ¬ IsField R) (L0 : Submodule R V) (L : HeightOneSpectrum R → Submodule R V)
    (h0 : Submodule.IsLattice K L0) (hL : ∀ w, Submodule.IsLattice K (L w))
    (hfin : {w : HeightOneSpectrum R | localization₂ w.asIdeal (L w) ≠ localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsLattice K (⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w)) ∧
      ∀ w : HeightOneSpectrum R,
        localization₂ w.asIdeal (⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w)) =
          localization₂ w.asIdeal (L w) := by
  classical
  set G : Submodule R V := ⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w) with hG
  have hGmem : ∀ x, x ∈ G ↔ ∀ w : HeightOneSpectrum R, x ∈ localization₂ w.asIdeal (L w) := by
    intro x
    rw [hG, Submodule.mem_iInf]

  have hA : ∃ a : R, a ≠ 0 ∧ ∀ x ∈ L0, a • x ∈ G := by
    choose a ha0 ha using fun w => denom (K := K) L0 (L w) (Submodule.IsLattice.fg (self := h0))
      (Submodule.IsLattice.span_eq_top (self := hL w))
    refine ⟨∏ w ∈ hfin.toFinset, a w, Finset.prod_ne_zero_iff.mpr (fun w _ => ha0 w), ?_⟩
    intro x hx
    rw [hGmem]
    intro w
    by_cases hw : w ∈ hfin.toFinset
    · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem a hw
      rw [hr, mul_comm, mul_smul]
      exact locBasic_le_locS _ _ ((L w).smul_mem r (ha w x hx))
    · have hw' : localization₂ w.asIdeal (L w) = localization₂ w.asIdeal L0 := by
        by_contra h
        exact hw (hfin.mem_toFinset.mpr h)
      rw [hw']
      exact locBasic_le_locS _ _ (L0.smul_mem _ hx)

  have hB : ∃ b : R, b ≠ 0 ∧ ∀ x ∈ G, b • x ∈ L0 := by
    choose b hb0 hb using fun w => denom (K := K) (L w) L0 (Submodule.IsLattice.fg (self := hL w))
      (Submodule.IsLattice.span_eq_top (self := h0))
    refine ⟨∏ w ∈ hfin.toFinset, b w, Finset.prod_ne_zero_iff.mpr (fun w _ => hb0 w), ?_⟩
    intro x hx
    apply lg hR
    intro w
    have hxw := (hGmem x).mp hx w
    by_cases hw : w ∈ hfin.toFinset
    · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem b hw
      obtain ⟨s, hs, hsx⟩ := hxw
      refine ⟨s, hs, ?_⟩
      have e : s • (∏ w ∈ hfin.toFinset, b w) • x = r • (b w • (s • x)) := by
        rw [hr]
        module
      rw [e]
      exact L0.smul_mem r (hb w _ hsx)
    · have hw' : localization₂ w.asIdeal (L w) = localization₂ w.asIdeal L0 := by
        by_contra h
        exact hw (hfin.mem_toFinset.mpr h)
      rw [hw'] at hxw
      exact (localization₂ w.asIdeal L0).smul_mem _ hxw
  obtain ⟨a, ha0, ha⟩ := hA
  obtain ⟨b, hb0, hb⟩ := hB
  have hinvsmul : ∀ (r : R), r ≠ 0 → ∀ y : V, (algebraMap R K r)⁻¹ • (r • y) = y := by
    intro r hr y
    have : algebraMap R K r ≠ 0 := by
      simpa using (IsFractionRing.injective R K).ne hr
    rw [← algebraMap_smul K r y, smul_smul, inv_mul_cancel₀ this, one_smul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have hN : IsNoetherian R L0 :=
      isNoetherian_of_fg_of_noetherian L0 (Submodule.IsLattice.fg (self := h0))
    have hle : G.map (LinearMap.lsmul R V b) ≤ L0 := by
      rintro _ ⟨x, hx, rfl⟩
      exact hb x hx
    have hfg : (G.map (LinearMap.lsmul R V b)).FG := isNoetherian_submodule.mp hN _ hle
    refine Submodule.fg_of_fg_map_injective (LinearMap.lsmul R V b) ?_ hfg
    intro x y hxy
    have hxy' : b • x = b • y := hxy
    rw [← hinvsmul b hb0 x, ← hinvsmul b hb0 y, hxy']
  ·
    rw [eq_top_iff, ← Submodule.IsLattice.span_eq_top (self := h0), Submodule.span_le]
    intro x hx
    rw [← hinvsmul a ha0 x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (ha x hx))
  · intro w
    apply le_antisymm
    · have h1 : G ≤ localization₂ w.asIdeal (L w) := iInf_le _ w
      calc localization₂ w.asIdeal G ≤ localization₂ w.asIdeal (localization₂ w.asIdeal (L w)) := locBasic_locS_mono _ h1
        _ = localization₂ w.asIdeal (L w) := locBasic_locS_idem _ _
    · have h1 : L w ≤ localization₂ w.asIdeal G := by
        intro x hx

        obtain ⟨c', hc', hc'x⟩ : ∃ c' ∈ nonZeroDivisors R, c' • x ∈ L0 := by
          have : x ∈ locS (nonZeroDivisors R) L0 := by
            rw [indexBasic_locS_top (K := K) L0 (Submodule.IsLattice.span_eq_top (self := h0))]
            exact Submodule.mem_top
          exact this
        have hc0 : a * c' ≠ 0 := mul_ne_zero ha0 (nonZeroDivisors.ne_zero hc')
        have hcx : (a * c') • x ∈ G := by
          rw [mul_smul]
          exact ha _ hc'x
        obtain ⟨s, hsw, hs⟩ := sep w (a * c') hc0
        refine ⟨s, hsw, ?_⟩
        rw [hGmem]
        intro w'
        by_cases hw' : w' = w
        · subst hw'
          exact locBasic_le_locS _ _ ((L w').smul_mem s hx)
        · obtain ⟨t, ht, u, hu⟩ := hs w' hw'
          have h2 : t • (s • x) ∈ localization₂ w'.asIdeal (L w') := by
            rw [smul_smul, hu, mul_comm, mul_smul]
            exact (localization₂ w'.asIdeal (L w')).smul_mem u ((hGmem _).mp hcx w')
          have h3 : s • x ∈ localization₂ w'.asIdeal (localization₂ w'.asIdeal (L w')) := ⟨t, ht, h2⟩
          rwa [show localization₂ w'.asIdeal (localization₂ w'.asIdeal (L w')) = localization₂ w'.asIdeal (L w') from
            locBasic_locS_idem _ _] at h3
      calc localization₂ w.asIdeal (L w) ≤ localization₂ w.asIdeal (localization₂ w.asIdeal G) := locBasic_locS_mono _ h1
        _ = localization₂ w.asIdeal G := locBasic_locS_idem _ _
end Formalism.DivisionValues.GluingInclusion
