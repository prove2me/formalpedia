-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.map_derivIdeal_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:00:23.686977+00:00
-- url     : https://prove2.me/submissions/4484048c-6dd4-4264-a1c1-c31f746bb941

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_inr_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_inl_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_of_mem_span
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (J : Ideal S) :
    Ideal.map (algebraMap S T) (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S T) J) := by
  have key1 : ∀ (D : Derivation k S S) (y : S), y ∈ J →
      algebraMap S T (D y) ∈ derivIdeal k (Ideal.map (algebraMap S T) J) := by
    intro D y hy
    have hsp : D ∈ Submodule.span S (Set.range (partialDeriv k ι S)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨i, rfl⟩ := hD
        rw [← partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
        exact derivation_apply_mem_derivIdeal k _ _ (Ideal.mem_map_of_mem _ hy)
    | zero =>
        have h0 : ((0 : Derivation k S S)) y = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) y = a y + b y := rfl
        rw [h0, map_add]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) y = c * a y := rfl
        rw [h0, map_mul]
        exact Ideal.mul_mem_left _ _ ha
  have key2 : ∀ (D' : Derivation k T T) (y : S), y ∈ J →
      D' (algebraMap S T y) ∈ Ideal.map (algebraMap S T) (derivIdeal k J) := by
    intro D' y hy
    have hsp : D' ∈ Submodule.span T (Set.range (partialDeriv k (ι ⊕ κ) T)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨x, rfl⟩ := hD
        cases x with
        | inl i =>
            rw [partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
            exact Ideal.mem_map_of_mem _
              (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) hy)
        | inr j =>
            rw [partialDeriv_inr_algebraMap k ι κ S T hcoord j y]
            exact Submodule.zero_mem _
    | zero =>
        have h0 : ((0 : Derivation k T T)) (algebraMap S T y) = 0 := rfl
        rw [h0]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) (algebraMap S T y)
            = a (algebraMap S T y) + b (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) (algebraMap S T y) = c * a (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.mul_mem_left _ _ ha
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
    refine ⟨fun y hy => Ideal.mem_comap.mpr (le_derivIdeal k _ (Ideal.mem_map_of_mem _ hy)), ?_⟩
    intro D y hy
    exact Ideal.mem_comap.mpr (key1 D y hy)
  · rw [derivIdeal_le_iff]
    refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
    intro D' z hz
    have hspan : Ideal.map (algebraMap S T) J
        = Ideal.span ((algebraMap S T) '' (J : Set S)) := by
      rw [← Ideal.map_span, Ideal.span_eq]
    rw [hspan] at hz
    refine derivation_apply_mem_of_mem_span D' ?_ ?_ hz
    · rw [← hspan]
      exact Ideal.map_mono (le_derivIdeal k J)
    · rintro g ⟨y, hy, rfl⟩
      exact key2 D' y hy
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
