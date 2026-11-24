-- Prove2me | solution 1 for Formalism.MainNotions.Pf14.smith_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:42.671244+00:00
-- url     : https://prove2.me/submissions/ea6b4075-690d-4f86-af1d-d5af9df7e8a2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ScaleEdges_DvdOfAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.Pf14
open Module
namespace Formalism.MainNotions.Pf14
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsLocalRing O]
    {I : Type*} [Fintype I] (S : Submodule O (I → O)) (a : O)
    (h : ∀ φ : I → O, (∃ i, IsUnit (φ i)) → ∃ s ∈ S, (∑ i, φ i * s i) ∣ a) (x : I → O) : a • x ∈ S := by
  classical
  obtain ⟨n, snf⟩ := S.smithNormalForm (Pi.basisFun O I)
  have key : ∀ j, a • snf.bM j ∈ S := by
    intro j
    set φ : I → O := fun i => snf.bM.coord j (Pi.single i 1) with hφdef
    have hφ : ∀ y : I → O, ∑ i, φ i * y i = snf.bM.coord j y := by
      intro y
      conv_rhs => rw [show y = ∑ i, y i • Pi.single i (1 : O) by
        ext k; simp [Finset.sum_apply, Pi.single_apply]]
      simp only [map_sum, map_smul, smul_eq_mul, hφdef, mul_comm]
    have hprim : ∃ i, IsUnit (φ i) := by
      by_contra hne
      push_neg at hne
      have h1 : snf.bM.coord j (snf.bM j) = 1 := by simp
      rw [← hφ] at h1
      have hmem : ∑ i, φ i * snf.bM j i ∈ IsLocalRing.maximalIdeal O :=
        Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i))
      rw [h1] at hmem
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hmem)
    obtain ⟨s, hs, hsd⟩ := h φ hprim
    rw [hφ] at hsd
    have hs' : s = ∑ k, snf.bN.repr ⟨s, hs⟩ k • snf.a k • snf.bM (snf.f k) := by
      have := congrArg Subtype.val (snf.bN.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, snf.snf] at this
      exact this.symm
    have hc : snf.bM.coord j s =
        ∑ k, snf.bN.repr ⟨s, hs⟩ k * snf.a k * (if snf.f k = j then 1 else 0) := by
      conv_lhs => rw [hs']
      simp [map_sum, map_smul, Finsupp.single_apply, mul_assoc]
    by_cases hj : ∃ k, snf.f k = j
    · obtain ⟨k0, rfl⟩ := hj
      have hc0 : snf.bM.coord (snf.f k0) s = snf.bN.repr ⟨s, hs⟩ k0 * snf.a k0 := by
        rw [hc, Finset.sum_eq_single k0]
        · simp
        · intro k _ hk
          simp [snf.f.injective.ne hk]
        · simp
      rw [hc0] at hsd
      obtain ⟨t, ht⟩ := (Dvd.intro_left _ rfl : snf.a k0 ∣ snf.bN.repr ⟨s, hs⟩ k0 * snf.a k0).trans hsd
      rw [ht, mul_comm, mul_smul, ← snf.snf k0]
      exact S.smul_mem t (snf.bN k0).2
    · push_neg at hj
      have hc0 : snf.bM.coord j s = 0 := by
        rw [hc]
        exact Finset.sum_eq_zero fun k _ => by simp [hj k]
      rw [hc0, zero_dvd_iff] at hsd
      simp [hsd]
  rw [← snf.bM.sum_repr x, Finset.smul_sum]
  refine S.sum_mem fun j _ => ?_
  rw [smul_comm]
  exact S.smul_mem _ (key j)
end Formalism.MainNotions.Pf14
