-- Prove2me | solution 1 for FasterWCTFPTAS.Main.observation_4_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:31:36.64548+00:00
-- url     : https://prove2.me/submissions/bec35d5c-ee3c-4050-ad9e-ba98ffde8954

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Scheduling
import Theorems.Thm_FasterWCTFPTAS_Main_smith_rule

set_option autoImplicit false

open FasterWCTFPTAS.Main
open Finset

namespace Obs45Aux

lemma smithBefore_iff_le {n : ℕ} {p w : Fin n → ℝ} (hsort : Sorted p w) (i j : Fin n) :
    SmithBefore p w i j ↔ i ≤ j := by
  constructor
  · rintro (hlt | ⟨_, hle⟩)
    · by_contra hnot
      have hji : j ≤ i := le_of_not_ge hnot
      have hle' := hsort j i hji
      linarith
    · exact hle
  · intro hle
    rcases lt_or_eq_of_le (hsort i j hle) with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, hle⟩

lemma U_eq_smithCost_one {n : ℕ} (p w : Fin n → ℝ) (hsort : Sorted p w) :
    U p w n = smithCost p w (fun _ : Fin n => (0 : Fin 1)) := by
  unfold U T smithCost smithCompletion
  have huniv : univ.filter (fun j : Fin n => j.val < n) = univ := by
    ext j
    simp
  rw [huniv]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_filter, mem_univ, true_and, smithBefore_iff_le hsort]
  exact Nat.lt_succ_iff

lemma U_le_m_mul_cost {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n) :
    U p w n ≤ (m : ℝ) * cost p w σ ρ := by
  let C : Fin n → ℝ := completion p σ ρ
  let π : Fin n ≃ Fin n := Tuple.sort C
  let ρ₁ : Fin n ≃ Fin n := π.symm
  let σ₁ : Fin n → Fin 1 := fun _ => 0
  have hmono : ∀ i j : Fin n, ρ₁ i ≤ ρ₁ j → C i ≤ C j := by
    intro i j hle
    have hm := Tuple.monotone_sort C hle
    simpa [Function.comp, ρ₁, π] using hm
  have hsmith : U p w n ≤ cost p w σ₁ ρ₁ := by
    rw [U_eq_smithCost_one p w hsort]
    exact FasterWCTFPTAS.Main.smith_rule p w hp hw σ₁ ρ₁
  have hcomp_le : ∀ j : Fin n, completion p σ₁ ρ₁ j ≤ (m : ℝ) * C j := by
    intro j
    let Sj : Finset (Fin n) := univ.filter (fun i => ρ₁ i ≤ ρ₁ j)
    have hSj : completion p σ₁ ρ₁ j = ∑ i ∈ Sj, p i := by
      unfold completion
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i
      simp [Sj, σ₁]
    rw [hSj]
    have hpart : ∑ i ∈ Sj, p i = ∑ l : Fin m, ∑ i ∈ Sj.filter (fun i => σ i = l), p i := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) p
    rw [hpart]
    have hCj_nonneg : 0 ≤ C j :=
      Finset.sum_nonneg fun i _ => le_of_lt (hp i)
    calc
      ∑ l : Fin m, ∑ i ∈ Sj.filter (fun i => σ i = l), p i
          ≤ ∑ _l : Fin m, C j := by
            refine Finset.sum_le_sum fun l _ => ?_
            let Al := Sj.filter (fun i => σ i = l)
            change ∑ i ∈ Al, p i ≤ C j
            by_cases hne : Al.Nonempty
            · obtain ⟨iStar, hiStar_mem, hiStar_max⟩ := Finset.exists_max_image Al ρ hne
              have hiStar_Sj : iStar ∈ Sj := (mem_filter.mp hiStar_mem).1
              have hiStar_mach : σ iStar = l := (mem_filter.mp hiStar_mem).2
              have hC_le : C iStar ≤ C j := hmono iStar j (mem_filter.mp hiStar_Sj).2
              have hsub : Al ⊆ univ.filter (fun i => σ i = σ iStar ∧ ρ i ≤ ρ iStar) := by
                intro i hi
                have hi_mach : σ i = l := (mem_filter.mp hi).2
                exact mem_filter.mpr ⟨mem_univ i, hi_mach.trans hiStar_mach.symm, hiStar_max i hi⟩
              have hsum_le : ∑ i ∈ Al, p i ≤ C iStar :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => le_of_lt (hp i)
              linarith
            · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
              exact hCj_nonneg
      _ = (m : ℝ) * C j := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hcost_le : cost p w σ₁ ρ₁ ≤ (m : ℝ) * cost p w σ ρ := by
    unfold cost
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hmul := mul_le_mul_of_nonneg_left (hcomp_le j) (hw j)
    change w j * completion p σ₁ ρ₁ j ≤ (m : ℝ) * (w j * C j)
    linarith
  linarith

end Obs45Aux

theorem solution {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) :
    U p w n / m ≤ OPT m p w := by
  unfold OPT
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  let Scosts : Set ℝ := {c : ℝ | ∃ (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n), cost p w σ ρ = c}
  have hne : Scosts.Nonempty :=
    ⟨cost p w (fun _ => ⟨0, by omega⟩) (Equiv.refl (Fin n)),
      ⟨fun _ => ⟨0, by omega⟩, Equiv.refl (Fin n), rfl⟩⟩
  refine le_csInf hne ?_
  rintro _ ⟨σ, ρ, rfl⟩
  rw [div_le_iff₀ hm_pos]
  linarith [Obs45Aux.U_le_m_mul_cost p w hp hw hsort σ ρ]
