-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_derivIdealSheafIterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:33:08.437944+00:00
-- url     : https://prove2.me/submissions/87af30ed-7feb-4077-8cb2-2dca2f3af51a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_derivIdealSheafIterate_eq_sub
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_add
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_le_of_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem eq_top_or_exists_eq_natCast (a : ℕ∞) : a = ⊤ ∨ ∃ n : ℕ, a = (n : ℕ∞) := by
  rcases eq_or_ne a ⊤ with h | h
  · exact Or.inl h
  · exact Or.inr ⟨a.toNat, (ENat.natCast_toNat h).symm⟩
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (I : X.IdealSheafData)
    {r m : ℕ} (h : r < m) :
    orderAtLeastLocus (derivIdealSheafIterate k p r I) (m - r) = orderAtLeastLocus I m := by
  refine Set.Subset.antisymm ?_ (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p I r m)
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  rcases eq_top_or_exists_eq_natCast (orderAt I x) with htop | ⟨n, hn⟩
  · rw [htop]
    exact le_top
  · rcases Nat.lt_or_ge n r with hnr | hrn
    · exfalso
      have hzero : orderAt (derivIdealSheafIterate k p n I) x = ((n - n : ℕ) : ℕ∞) :=
        orderAt_derivIdealSheafIterate_eq_sub k p I x hn le_rfl
      simp only [Nat.sub_self, Nat.cast_zero] at hzero
      have hsplit : r - n + n = r := by omega
      have hadd : derivIdealSheafIterate k p (r - n + n) I =
          derivIdealSheafIterate k p (r - n) (derivIdealSheafIterate k p n I) :=
        derivIdealSheafIterate_add k p (r - n) n I
      rw [hsplit] at hadd
      have hle : derivIdealSheafIterate k p n I ≤ derivIdealSheafIterate k p r I := by
        rw [hadd]
        exact le_derivIdealSheafIterate k p (r - n) (derivIdealSheafIterate k p n I)
      have h1 : orderAt (derivIdealSheafIterate k p r I) x ≤ 0 := by
        have h2 := orderAt_le_of_le hle x
        rwa [hzero] at h2
      have h3 : ((m - r : ℕ) : ℕ∞) ≤ 0 := le_trans hx h1
      have h4 : m - r ≤ 0 := by exact_mod_cast h3
      omega
    · have key : orderAt (derivIdealSheafIterate k p r I) x = ((n - r : ℕ) : ℕ∞) :=
        orderAt_derivIdealSheafIterate_eq_sub k p I x hn hrn
      rw [key] at hx
      have hmn : m - r ≤ n - r := by exact_mod_cast hx
      have hmn' : m ≤ n := by omega
      rw [hn]
      exact_mod_cast hmn'
end FunctorialResolution.EmbeddedResolution
