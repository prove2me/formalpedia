-- Prove2me | solution 1 for FairSelling.servable_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:16.702972+00:00
-- url     : https://prove2.me/submissions/14772c0d-85c2-4237-860c-00c196a765c5

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Theorems.Thm_FairSelling_trunc_le_max
import Theorems.Thm_FairSelling_truncBundle_le_vbarSum
import Theorems.Thm_FairSelling_truncBundle_sdiff
import Theorems.Thm_FairSelling_servable_extend
import Theorems.Thm_FairSelling_exists_minimal_bag

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
open Classical
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (τ t : Fin n → ℝ) (hτ : ∀ i, 0 ≤ τ i) (ht : ∀ i, t i ≤ 2 * τ i) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → 0 ≤ D →
      (∀ i ∈ T, (2 * (m : ℝ) - 1) * τ i ≤ truncBundle (v i) p (t i) R + D) →
      Servable v p τ T R D := by
  classical
  intro m
  induction m with
  | zero =>
    intro T R D hcard hD _
    have hT : T = ∅ := Finset.card_eq_zero.mp hcard
    refine ⟨fun _ => ∅, ∅, fun _ => 0, fun _ => Finset.empty_subset _,
      Finset.empty_subset _, fun _ _ _ => by simp, fun _ => by simp, fun _ => le_refl 0, ?_, ?_,
      fun _ _ => ⟨rfl, rfl⟩⟩
    · simp [hD]
    · intro i hi; rw [hT] at hi; exact absurd hi (Finset.notMem_empty i)
  | succ m ih =>
    intro T R D hcard hD hinv
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    -- an active agent of least threshold
    obtain ⟨i₀, hi₀T, hi₀min⟩ := Finset.exists_min_image T τ hTne
    have hcard' : (T.erase i₀).card = m := by
      rw [Finset.card_erase_of_mem hi₀T, hcard]; rfl
    -- the invariant needs to be re-established with `m` active agents
    have hstep : ∀ (j : Fin n) (X : Finset G) (dD : ℝ), X ⊆ R →
        (∀ i ∈ T.erase j, truncBundle (v i) p (t i) X + dD ≤ 2 * τ i) →
        ∀ i ∈ T.erase j, (2 * (m : ℝ) - 1) * τ i
            ≤ truncBundle (v i) p (t i) (R \ X) + (D - dD) := by
      intro j X dD hX hloss i hi
      have h1 := hinv i (Finset.mem_of_mem_erase hi)
      have h2 := truncBundle_sdiff (v i) p (t i) hX
      have h3 := hloss i hi
      push_cast at h1 ⊢
      linarith
    by_cases hcase1 : ∃ g ∈ R, ∃ k ∈ T, τ k ≤ p g
    · -- Loop 1: sell an expensive good, pay the least-threshold agent
      obtain ⟨g, hgR, k, hkT, hgk⟩ := hcase1
      have hpg : τ i₀ ≤ p g := le_trans (hi₀min k hkT) hgk
      refine servable_extend v p τ i₀ hi₀T ∅ {g} (τ i₀) (Finset.empty_subset _)
        (Finset.singleton_subset_iff.mpr hgR) (by simp) (hτ i₀)
        (by simp [vbarSum]) ?_
      have hDD : D + (∑ x ∈ ({g} : Finset G), p x) - τ i₀ = D - (τ i₀ - p g) := by
        simp; ring
      have hXsub : ({g} : Finset G) ⊆ R := Finset.singleton_subset_iff.mpr hgR
      have hEq : R \ (∅ ∪ ({g} : Finset G)) = R \ ({g} : Finset G) := by simp
      rw [hDD, hEq]
      refine ih _ _ _ hcard' (by simp; linarith) ?_
      refine hstep i₀ _ _ hXsub ?_
      intro i hi
      have hτi : 0 ≤ τ i := hτ i
      have hle : trunc (v i) p (t i) g ≤ max (p g) (t i) := trunc_le_max _ _ _ _
      have hi₀le : τ i₀ ≤ τ i := hi₀min i (Finset.mem_of_mem_erase hi)
      have hti := ht i
      simp only [truncBundle, Finset.sum_singleton]
      rcases max_cases (p g) (t i) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hle <;> linarith
    · push_neg at hcase1
      by_cases hcase2 : ∃ g ∈ R, ∃ k ∈ T, τ k ≤ v k g
      · -- Loop 2: hand a highly valued good to the agent that values it
        obtain ⟨g, hgR, k, hkT, hgk⟩ := hcase2
        refine servable_extend v p τ k hkT {g} ∅ 0
          (Finset.singleton_subset_iff.mpr hgR) (Finset.empty_subset _) (by simp) (le_refl 0)
          ?_ ?_
        · simp only [vbarSum, Finset.sum_singleton, vbar, add_zero]
          exact le_trans hgk (le_max_right _ _)
        · have hDD : D + (∑ x ∈ (∅ : Finset G), p x) - 0 = D - 0 := by simp
          have hEq : R \ (({g} : Finset G) ∪ ∅) = R \ ({g} : Finset G) := by simp
          rw [hDD, hEq]
          refine ih _ _ _ (by rw [Finset.card_erase_of_mem hkT, hcard]; rfl) (by linarith) ?_
          refine hstep k _ _ (Finset.singleton_subset_iff.mpr hgR) ?_
          intro i hi
          have hiT := Finset.mem_of_mem_erase hi
          have hle : trunc (v i) p (t i) g ≤ max (p g) (t i) := trunc_le_max _ _ _ _
          have hpg := hcase1 g hgR i hiT
          have hti := ht i
          have hτi : 0 ≤ τ i := hτ i
          simp only [truncBundle, Finset.sum_singleton, add_zero]
          rcases max_cases (p g) (t i) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hle <;> linarith
      · push_neg at hcase2
        by_cases hcase3 : τ i₀ ≤ D
        · -- enough banked cash to pay the least-threshold agent outright
          refine servable_extend v p τ i₀ hi₀T ∅ ∅ (τ i₀) (Finset.empty_subset _)
            (Finset.empty_subset _) (by simp) (hτ i₀) (by simp [vbarSum]) ?_
          have hDD : D + (∑ x ∈ (∅ : Finset G), p x) - τ i₀ = D - τ i₀ := by simp
          have hEq : R \ ((∅ : Finset G) ∪ ∅) = R \ (∅ : Finset G) := by simp
          rw [hDD, hEq]
          refine ih _ _ _ hcard' (by linarith) ?_
          refine hstep i₀ _ _ (Finset.empty_subset _) ?_
          intro i hi
          have hi₀le : τ i₀ ≤ τ i := hi₀min i (Finset.mem_of_mem_erase hi)
          have hτi : 0 ≤ τ i := hτ i
          simp only [truncBundle, Finset.sum_empty, zero_add]
          linarith
        · -- Loop 3: bag filling
          push_neg at hcase3
          have hsmall : ∀ i ∈ T, ∀ g ∈ R, vbar (v i) p g < τ i := by
            intro i hi g hg
            exact max_lt (hcase1 g hg i hi) (hcase2 g hg i hi)
          have hDlt : ∀ i ∈ T, D < τ i := by
            intro i hi
            exact lt_of_lt_of_le hcase3 (hi₀min i hi)
          have hfull : τ i₀ ≤ vbarSum (v i₀) p R + D := by
            have h1 := hinv i₀ hi₀T
            have h2 := truncBundle_le_vbarSum (v i₀) p (t i₀) R
            have h3 : (1:ℝ) ≤ 2 * ((m:ℝ) + 1) - 1 := by
              have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
              linarith
            have h4 : τ i₀ ≤ (2 * ((m:ℝ) + 1) - 1) * τ i₀ := by
              nlinarith [hτ i₀]
            push_cast at h1
            linarith
          obtain ⟨B, k, hBR, hkT, hkserve, hkloss⟩ :=
            exists_minimal_bag v p τ T R D hsmall hDlt i₀ hi₀T hfull
          refine servable_extend v p τ k hkT B ∅ D hBR (Finset.empty_subset _) (by simp) hD
            (by linarith [hkserve]) ?_
          have hDD : D + (∑ x ∈ (∅ : Finset G), p x) - D = D - D := by simp
          have hEq : R \ (B ∪ (∅ : Finset G)) = R \ B := by simp
          rw [hDD, hEq]
          refine ih _ _ _ (by rw [Finset.card_erase_of_mem hkT, hcard]; rfl) (by simp) ?_
          refine hstep k _ _ hBR ?_
          intro i hi
          have hiT := Finset.mem_of_mem_erase hi
          have h1 := hkloss i hiT
          have h2 := truncBundle_le_vbarSum (v i) p (t i) B
          linarith
end FairSelling
