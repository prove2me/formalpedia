-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.expand_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:47.40644+00:00
-- url     : https://prove2.me/submissions/95c95da2-e0cb-480b-9531-ed34d7aff102

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsASDOfTuple
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA Module
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution [FiniteDimensional K V] {y : Fin (finrank K V) → V}
    (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) (hne : ∀ i, h (y i) (y i) ≠ 0) (v : V) :
    v = ∑ i, (h (y i) v * (h (y i) (y i))⁻¹) • y i := by
  have hli : LinearIndependent K y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hj := congrArg (h (y j)) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact (mul_eq_zero.mp hj).resolve_right (hne j)
  by_cases h0 : finrank K V = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact Subsingleton.elim _ _
  haveI : Nonempty (Fin (finrank K V)) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
  set b := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _) with hb
  have hbi : ∀ i, b i = y i := fun i => by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hv : ∑ i, b.repr v i • y i = v := by
    simp_rw [← hbi]
    exact b.sum_repr v
  have hc : ∀ j, b.repr v j = h (y j) v * (h (y j) (y j))⁻¹ := by
    intro j
    rw [eq_mul_inv_iff_mul_eq₀ (hne j)]
    have hj := congrArg (h (y j)) hv
    simp only [map_sum, map_smul, smul_eq_mul] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact hj
  calc v = ∑ i, b.repr v i • y i := hv.symm
    _ = _ := Finset.sum_congr rfl fun i _ => by rw [hc i]
end Formalism.HermitianLattices.Ext.L3.U0
