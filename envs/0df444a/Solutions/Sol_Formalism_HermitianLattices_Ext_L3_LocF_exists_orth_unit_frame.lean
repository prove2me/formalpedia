-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.exists_orth_unit_frame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:13.088142+00:00
-- url     : https://prove2.me/submissions/b601377d-8817-4acc-acfc-079d7a84cd8a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_next_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution [FiniteDimensional K V] (hS : IsHermSemilocal S)
    (hloc : ∀ a ∈ S, ∀ b ∈ S, star a = a → star b = b → ¬ IsUnitIn S a → ¬ IsUnitIn S b →
      IsUnitIn S (a + b + 1))
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSelfDualMod S h M) :
    ∃ x : Fin (finrank K V) → V, (∀ i, x i ∈ M) ∧ (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
      ∀ i, IsUnitIn S (h (x i) (x i)) := by
  classical
  have P : ∀ k, k ≤ finrank K V → ∃ x : ℕ → V, (∀ i < k, x i ∈ M) ∧
      (∀ i < k, ∀ j < k, i ≠ j → h (x i) (x j) = 0) ∧ ∀ i < k, IsUnitIn S (h (x i) (x i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hxM, hxo, hxu⟩ := ih (by omega)
      set W : Submodule K V := Submodule.span K (((Finset.range k).image x : Finset V) : Set V)
        with hW
      have hWne : W ≠ ⊤ := by
        intro htop
        have h1 : finrank K W ≤ k :=
          (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (by simp))
        rw [htop, finrank_top] at h1
        omega
      obtain ⟨u, hu⟩ : ∃ u, u ∉ W := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        exact hWne (eq_top_iff.mpr fun u _ => hcon u)
      have hxW : ∀ i ∈ Finset.range k, x i ∈ W := fun i hi =>
        Submodule.subset_span (by exact_mod_cast Finset.mem_image_of_mem x hi)
      have hsW : ∑ i ∈ Finset.range k, (h (x i) u * (h (x i) (x i))⁻¹) • x i ∈ W :=
        W.sum_mem fun i hi => W.smul_mem _ (hxW i hi)
      obtain ⟨z, hzM, hzu, hzo⟩ := exists_next_unit hS hloc hs hd hM x (Finset.range k)
        (fun i hi => hxM i (Finset.mem_range.mp hi))
        (fun i hi j hj => hxo i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj))
        (fun i hi => hxu i (Finset.mem_range.mp hi))
        (u - ∑ i ∈ Finset.range k, (h (x i) u * (h (x i) (x i))⁻¹) • x i)
        (fun h0 => hu (by rw [sub_eq_zero.mp h0]; exact hsW))
        (by
          intro j hj
          rw [map_sub, map_sum, Finset.sum_eq_single j]
          · rw [map_smul, smul_eq_mul,
              inv_mul_cancel_right₀ (hxu j (Finset.mem_range.mp hj)).1, sub_self]
          · intro i hi hij
            rw [map_smul, hxo j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi)
              (Ne.symm hij), smul_zero]
          · exact fun hj' => absurd hj hj')
      have hzo' : ∀ i < k, h z (x i) = 0 := fun i hi => by
        rw [← hs.eq, hzo i (Finset.mem_range.mpr hi), map_zero]
      refine ⟨fun i => if i = k then z else x i, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · simpa [hik] using hzM
        · simpa [hik] using hxM i (by omega)
      · intro i hi j hj hij
        by_cases hik : i = k
        · have hjk : j ≠ k := fun e => hij (hik.trans e.symm)
          simpa [hik, hjk] using hzo' j (by omega)
        · by_cases hjk : j = k
          · simpa [hik, hjk] using hzo i (Finset.mem_range.mpr (by omega))
          · simpa [hik, hjk] using hxo i (by omega) j (by omega) hij
      · intro i hi
        by_cases hik : i = k
        · simpa [hik] using hzu
        · simpa [hik] using hxu i (by omega)
  obtain ⟨x, h1, h2, h3⟩ := P _ le_rfl
  exact ⟨fun i => x i, fun i => h1 i i.isLt,
    fun i j hij => h2 i i.isLt j j.isLt (fun e => hij (Fin.ext e)), fun i => h3 i i.isLt⟩
end Formalism.HermitianLattices.Ext.L3.LocF
