-- Prove2me | solution 1 for DaiWeissFluid.KellyType.condition_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:11:34.182795+00:00
-- url     : https://prove2.me/submissions/c95c63e9-7536-49dd-9d4d-a5c0da7d851b

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel
import Definitions.Def_DaiWeissFluid_KellyType_KellyLine

namespace Aux_Kelly_condb
open DaiWeissFluid.KellyType

lemma fin2 (a i j : Fin 2) (hij : i ≠ j) (ha : a ≠ i) : a = j := by
  revert a i j; decide

/-- predecessor class -/
def pr {K : ℕ} (k : Fin K) : Fin K := ⟨(k : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

lemma qplus_succ {K : ℕ} (Q : ℝ → Fin K → ℝ) (t : ℝ) (k : Fin K) (hk : (k : ℕ) ≠ 0) :
    DaiWeissFluid.ThreeBuffer.Qplus Q k t =
      DaiWeissFluid.ThreeBuffer.Qplus Q (pr k) t + Q t k := by
  unfold DaiWeissFluid.ThreeBuffer.Qplus
  have hfil : Finset.univ.filter (· ≤ k) = insert k (Finset.univ.filter (· ≤ pr k)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.le_iff_val_le_val, Fin.ext_iff, pr]
    omega
  have hnot : k ∉ Finset.univ.filter (· ≤ pr k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, pr]
    omega
  rw [hfil, Finset.sum_insert hnot]
  ring

lemma qplus_zero {K : ℕ} (Q : ℝ → Fin K → ℝ) (t : ℝ) (k : Fin K) (hk : (k : ℕ) = 0) :
    DaiWeissFluid.ThreeBuffer.Qplus Q k t = Q t k := by
  unfold DaiWeissFluid.ThreeBuffer.Qplus
  have hfil : Finset.univ.filter (· ≤ k) = {k} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.le_iff_val_le_val, Fin.ext_iff]
    omega
  rw [hfil, Finset.sum_singleton]

lemma qplus_nonneg {K : ℕ} (Q : ℝ → Fin K → ℝ) (t : ℝ) (h : ∀ k, 0 ≤ Q t k) (k : Fin K) :
    0 ≤ DaiWeissFluid.ThreeBuffer.Qplus Q k t :=
  Finset.sum_nonneg (fun l _ => h l)

end Aux_Kelly_condb

open DaiWeissFluid.KellyType Aux_Kelly_condb in
theorem solution {K : ℕ} (L : ReentrantLine 2 K) (hm : ∀ k, 0 < L.m k)
    (hfb : L.NoImmediateFeedback)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T) (t : ℝ) (ht : 0 ≤ t)
    (i j : Fin 2) (hij : i ≠ j) :
    L.volume Q i t = 0 →
      L.kellyG Q i t ≤ L.kellyG Q j t ∧
        ((hK : 0 < K) → L.σ ⟨0, hK⟩ = j → L.σ ⟨K - 1, by omega⟩ = i →
          L.kellyG Q i t = L.kellyG Q j t) := by
  intro hv
  have hnn : ∀ k, 0 ≤ Q t k := hsol.nonneg t ht
  -- empty station: all its queues vanish
  have hQ0 : ∀ k ∈ L.C i, Q t k = 0 := by
    intro k hk
    unfold ReentrantLine.volume at hv
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
      mul_nonneg (hm l).le (hnn l))).mp hv k hk
    exact (mul_eq_zero.mp this).resolve_left (hm k).ne'
  set P : Fin K → ℝ := fun k => DaiWeissFluid.ThreeBuffer.Qplus Q k t with hP
  have hPnn : ∀ k, 0 ≤ P k := fun k => qplus_nonneg Q t hnn k
  set S : Finset (Fin K) := (L.C i).filter (fun k : Fin K => (k : ℕ) ≠ 0) with hS
  -- step 1: G_i = ∑_{k ∈ S} P (pr k)
  have h1 : L.kellyG Q i t = ∑ k ∈ S, P (pr k) := by
    unfold ReentrantLine.kellyG
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs with h0
    · rw [qplus_succ Q t k h0, hQ0 k hk, add_zero]
    · push_neg at h0
      rw [qplus_zero Q t k h0, hQ0 k hk]
  have hinj : Set.InjOn pr (S : Set (Fin K)) := by
    intro a ha b hb hab
    simp only [hS, Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    simp only [pr, Fin.ext_iff] at hab ⊢
    omega
  have h2 : ∑ k ∈ S, P (pr k) = ∑ k ∈ S.image pr, P k :=
    (Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)).symm
  have hsub : S.image pr ⊆ L.C j := by
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hk'
    simp only [hS, Finset.mem_filter, ReentrantLine.C, Finset.mem_univ, true_and] at hk ⊢
    have hk1 : ((pr k : Fin K) : ℕ) + 1 < K := by
      simp only [pr]; have := k.isLt; omega
    have hne := hfb (pr k) hk1
    have e : (⟨((pr k : Fin K) : ℕ) + 1, hk1⟩ : Fin K) = k := by
      apply Fin.ext; simp only [pr]; omega
    rw [e, hk.1] at hne
    exact fin2 _ i j hij (Ne.symm hne)
  have hG : L.kellyG Q i t = ∑ k ∈ S.image pr, P k := h1.trans h2
  refine ⟨?_, ?_⟩
  · rw [hG]
    unfold ReentrantLine.kellyG
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hPnn k)
  · intro hK _ hlast
    rw [hG]
    unfold ReentrantLine.kellyG
    congr 1
    apply Finset.Subset.antisymm hsub
    intro k' hk'
    simp only [ReentrantLine.C, Finset.mem_filter, Finset.mem_univ, true_and] at hk'
    have hlt : (k' : ℕ) + 1 < K := by
      by_contra hc
      have e : k' = ⟨K - 1, by omega⟩ := by apply Fin.ext; simp; have := k'.isLt; omega
      rw [e, hlast] at hk'
      exact hij hk'
    have hne := hfb k' hlt
    rw [hk'] at hne
    have hi : L.σ ⟨(k' : ℕ) + 1, hlt⟩ = i := fin2 _ j i (Ne.symm hij) hne
    apply Finset.mem_image.mpr
    refine ⟨⟨(k' : ℕ) + 1, hlt⟩, ?_, ?_⟩
    · simp only [hS, Finset.mem_filter, ReentrantLine.C, Finset.mem_univ, true_and]
      exact ⟨hi, by omega⟩
    · apply Fin.ext; simp [pr]
