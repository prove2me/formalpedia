-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_le_map_of_pow_mul_iterate_deriv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:20.867498+00:00
-- url     : https://prove2.me/submissions/97757dcb-618b-48f2-8ce4-08301356875f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_truncatedSeries_mem_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_truncatedSeries_sub_mem_maximalIdeal_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeriesRingHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply


section
namespace FunctorialResolution.EmbeddedResolution
section
variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
end
section
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
end
section
open IsLocalRing
private theorem mem_of_forall_mem_sup_maximalIdeal_pow {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (J : Ideal B) (hJ : J ≤ IsLocalRing.maximalIdeal B) (x : B)
    (hx : ∀ N : ℕ, x ∈ J ⊔ IsLocalRing.maximalIdeal B ^ N) : x ∈ J := by
  have hmne : IsLocalRing.maximalIdeal B ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  have hJne : J ≠ ⊤ := by
    intro h
    apply hmne
    rw [eq_top_iff]
    rw [h] at hJ
    exact hJ
  have : Nontrivial (B ⧸ J) := by
    refine ⟨0, 1, fun h => hJne ?_⟩
    rw [Ideal.eq_top_iff_one]
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [map_one]
    exact h.symm
  have : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hIne : Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) ≠ ⊤ := by
    intro h
    have h1 : (1 : B ⧸ J) ∈ Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).1 h1
    have h2 : (1 : B) - y ∈ J := by
      refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
      rw [map_sub, hy1, map_one, sub_self]
    have h3 : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
      have h4 := Submodule.add_mem (IsLocalRing.maximalIdeal B) (hJ h2) hy
      simp at h4
    exact hmne ((Ideal.eq_top_iff_one _).2 h3)
  have hbot : (⨅ i : ℕ,
      (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i) = ⊥ := by
    apply Ideal.iInf_pow_eq_bot_of_isLocalRing
    exact hIne
  have hmem : ∀ N : ℕ, Ideal.Quotient.mk J x ∈
      (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ N := by
    intro N
    obtain ⟨j, hj, y, hy, hxy⟩ := Submodule.mem_sup.1 (hx N)
    have hxe : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := by
      rw [← hxy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
    rw [hxe]
    exact (Ideal.map_pow (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) N).le
      (Ideal.mem_map_of_mem _ hy)
  have hfin : Ideal.Quotient.mk J x ∈
      (⨅ i : ℕ, (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i) :=
    (Submodule.mem_iInf _).2 hmem
  rw [hbot, Ideal.mem_bot] at hfin
  exact Ideal.Quotient.eq_zero_iff_mem.1 hfin
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B) (b : R) (J : Ideal R)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (hb : φ b = β)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J) :
    Ideal.map φ' J ≤ Ideal.map φ J := by
  refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
  refine Ideal.mem_comap.mpr ?_
  by_cases htop : Ideal.map φ J = ⊤
  · rw [htop]
    exact Submodule.mem_top
  · refine mem_of_forall_mem_sup_maximalIdeal_pow (Ideal.map φ J)
      (IsLocalRing.le_maximalIdeal htop) (φ' g) ?_
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
      exact Submodule.mem_top
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have h1 : TaylorExpansion.truncatedSeries φ D β n g ∈ Ideal.map φ J := by
        have hmem := truncatedSeries_mem_map φ D b J hstab n g hg
        rwa [hb] at hmem
      have h2 : TaylorExpansion.truncatedSeries φ D β n g - φ' g ∈ maximalIdeal B ^ n :=
        truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep n hn1 g
      have hEq : φ' g = TaylorExpansion.truncatedSeries φ D β n g - (TaylorExpansion.truncatedSeries φ D β n g - φ' g) := by
        ring
      rw [hEq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
end FunctorialResolution.EmbeddedResolution
