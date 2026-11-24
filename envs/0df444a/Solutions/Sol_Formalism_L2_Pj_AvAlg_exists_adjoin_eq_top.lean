-- Prove2me | solution 1 for Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:37.388438+00:00
-- url     : https://prove2.me/submissions/37fe6742-3054-4d9c-9b36-a6e87db6dd5c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Theorems.Thm_Formalism_L2_Pj_AvAlg_adjoin_eq_top_of_gen
import Theorems.Thm_Formalism_L2_Pj_AvAlg_residue_aeval
import Theorems.Thm_Formalism_L2_Pj_AvAlg_adjoin_residue_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.AvAlg
variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
namespace Formalism.L2.Pj.AvAlg
theorem _root_.solution [Module.Finite A B] [Finite (ResidueField A)]
    (hinj : Function.Injective (algebraMap A B)) : ∃ α : B, Algebra.adjoin A {α} = ⊤ := by
  haveI : Finite (ResidueField B) := IsLocalRing.ResidueField.finite_of_finite (R := A) ‹_›
  obtain ⟨γ, hγ⟩ := adjoin_residue_gen (A := A) (B := B)
  obtain ⟨α0, rfl⟩ := IsLocalRing.residue_surjective γ
  have hint : IsIntegral (ResidueField A) (residue B α0) := IsIntegral.of_finite _ _
  have hsep : (minpoly (ResidueField A) (residue B α0)).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  have hq0 : aeval (residue B α0) (minpoly (ResidueField A) (residue B α0)) = 0 := minpoly.aeval _ _
  have hq' : aeval (residue B α0) (derivative (minpoly (ResidueField A) (residue B α0))) ≠ 0 :=
    hsep.aeval_derivative_ne_zero hq0
  obtain ⟨P, hP⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective
    (minpoly (ResidueField A) (residue B α0))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hm : aeval α0 P ∈ maximalIdeal B := by
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, hP, hq0]
  have hd : IsUnit (aeval α0 (derivative P)) := by
    by_contra hnu
    have h3 : aeval α0 (derivative P) ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, ← Polynomial.derivative_map, hP] at h3
    exact hq' h3
  by_cases h2 : aeval α0 P ∈ Ideal.span {π ^ 2}
  · refine ⟨α0 + π, adjoin_eq_top_of_gen hinj (α0 + π) ?_ P ?_⟩
    · have hr : residue B π = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr (hmax ▸ Ideal.mem_span_singleton_self π)
      rw [map_add, hr, add_zero]; exact hγ
    · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h2
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.map (algebraMap A B)) α0 π
      have e : aeval (α0 + π) P = π * (aeval α0 (derivative P) + π * (t + k)) := by
        simp only [Polynomial.aeval_def, ← Polynomial.eval_map] at ht ⊢
        rw [← Polynomial.derivative_map, hk, ← ht]
        ring
      have hv : IsUnit (aeval α0 (derivative P) + π * (t + k)) := by
        by_contra hnu
        have h1 : aeval α0 (derivative P) + π * (t + k) ∈ maximalIdeal B :=
          (IsLocalRing.mem_maximalIdeal _).mpr hnu
        have h3 : π * (t + k) ∈ maximalIdeal B := by
          rw [hmax]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
        have h4 : aeval α0 (derivative P) ∈ maximalIdeal B := by
          simpa using Ideal.sub_mem _ h1 h3
        exact (IsLocalRing.mem_maximalIdeal _).mp h4 hd
      rw [e]
      exact (irreducible_mul_isUnit hv).mpr hπ
  · refine ⟨α0, adjoin_eq_top_of_gen hinj α0 hγ P ?_⟩
    rw [hmax] at hm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hm
    have hwu : IsUnit w := by
      by_contra hnu
      apply h2
      have h5 : w ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [hmax, Ideal.mem_span_singleton'] at h5
      obtain ⟨v, hv⟩ := h5
      rw [Ideal.mem_span_singleton']
      exact ⟨v, by rw [← hw, ← hv]; ring⟩
    rw [← hw, mul_comm]
    exact (irreducible_mul_isUnit hwu).mpr hπ
end Formalism.L2.Pj.AvAlg
