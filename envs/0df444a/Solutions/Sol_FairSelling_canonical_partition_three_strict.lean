-- Prove2me | solution 1 for FairSelling.canonical_partition_three_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:04:10.878802+00:00
-- url     : https://prove2.me/submissions/22d03843-b17e-4b14-ad8a-c816b3dc4afd

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
import Theorems.Thm_FairSelling_canonical_strict_trivial
import Theorems.Thm_FairSelling_canonical_strict_pure_parts
import Theorems.Thm_FairSelling_canonical_strict_singleton
import Theorems.Thm_FairSelling_canonical_strict_two_pure
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_exists_reduced_three
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_sdiff
import Theorems.Thm_FairSelling_vbarSum_union
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (3 / 4) * MMS 3 w p) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p ((3 / 4) * MMS 3 w p) kept sold money leftover := by
  classical
  set M : ℝ := MMS 3 w p with hM
  set τ : ℝ := (3 / 4) * M with hτdef
  have hM0 : 0 ≤ M := MMS_nonneg (by norm_num) w p hw hp
  rcases eq_or_lt_of_le hM0 with hMzero | hMpos
  · exact canonical_strict_trivial w p (by rw [hτdef, ← hMzero]; norm_num)
  have hτ : 0 < τ := by rw [hτdef]; linarith
  obtain ⟨A, s, q, hcfg, hscard⟩ := exists_reduced_three w p hw hp
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hqsum, hge⟩ := hcfg
  -- the total value available: goods outside `s` plus the sale proceeds
  have hVeq : vbarSum w p (Finset.univ \ s) = ∑ i : Fin 3, vbarSum w p (A i) := by
    rw [show Finset.univ \ s = Finset.biUnion Finset.univ A from ?_]
    · rw [vbarSum, Finset.sum_biUnion]
      · rfl
      · exact fun i _ j _ hij => hdisjA i j hij
    · ext g
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hg
        have hg' : g ∈ s ∪ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ g
        rcases Finset.mem_union.mp hg' with h | h
        · exact absurd h hg
        · simpa using h
      · rintro ⟨i, hi⟩ hgs
        exact Finset.disjoint_left.mp (hdisjs i) hgs hi
  have hVtot : 4 * τ ≤ vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g := by
    have hsum3 : (3 : ℝ) * M ≤ ∑ i, (vbarSum w p (A i) + q i) := by
      have h := Finset.sum_le_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) => hge i)
      simpa [Fin.sum_univ_three] using h
    rw [Finset.sum_add_distrib, hqsum, ← hVeq] at hsum3
    rw [hτdef]; linarith
  by_cases hbig : ∃ i j : Fin 3, i ≠ j ∧ M / 4 < q i ∧ M / 4 < q j
  · -- at least two parts carry more than `M/4`: some force-sold good is expensive
    obtain ⟨i, j, hij, hi, hj⟩ := hbig
    have hqtot : M / 2 < ∑ g ∈ s, p g := by
      rw [← hqsum]
      have hsum : q i + q j ≤ ∑ k, q k := by
        have hsub : ({i, j} : Finset (Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hq0 k)
        rw [Finset.sum_pair hij] at h2
        exact h2
      linarith
    have hsne : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with rfl | h
      · simp at hqtot; linarith
      · exact h
    obtain ⟨F, hFs, hFmax⟩ := Finset.exists_max_image (f := p) s hsne
    have hpF0 : 0 ≤ p F := hp F
    have hpF : τ / 3 ≤ p F := by
      have hle : ∑ g ∈ s, p g ≤ (s.card : ℝ) * p F := by
        calc ∑ g ∈ s, p g ≤ ∑ _g ∈ s, p F := Finset.sum_le_sum (fun g hg => hFmax g hg)
        _ = (s.card : ℝ) * p F := by simp [mul_comm]
      have hcard : (s.card : ℝ) ≤ 2 := by exact_mod_cast hscard
      have h2 : M / 2 < 2 * p F := by nlinarith
      rw [hτdef]; linarith
    -- the total value with only `F` sold
    have hdisj_sF : Disjoint (Finset.univ \ s) (s \ ({F} : Finset G)) := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx2).1
    have hunion : (Finset.univ \ s) ∪ (s \ ({F} : Finset G)) = Finset.univ \ {F} := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro (hx | ⟨hx, hxF⟩)
        · rintro rfl; exact hx hFs
        · exact hxF
      · intro hxF
        by_cases hxs : x ∈ s
        · exact Or.inr ⟨hxs, hxF⟩
        · exact Or.inl hxs
    have hsplit : vbarSum w p (Finset.univ \ ({F} : Finset G))
        = vbarSum w p (Finset.univ \ s) + vbarSum w p (s \ {F}) := by
      rw [← hunion, vbarSum_union w p hdisj_sF]
    have hsF : ∑ g ∈ s, p g = p F + ∑ g ∈ s \ ({F} : Finset G), p g := by
      rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hFs)]
      simp [add_comm]
    have hsFle : ∑ g ∈ s \ ({F} : Finset G), p g ≤ vbarSum w p (s \ {F}) :=
      Finset.sum_le_sum (fun g _ => le_max_left _ _)
    have htotF : 4 * τ ≤ vbarSum w p (Finset.univ \ ({F} : Finset G)) + p F := by
      rw [hsF] at hVtot
      rw [hsplit]
      linarith
    by_cases hsing : ∃ e ∈ (Finset.univ \ ({F} : Finset G)), τ ≤ vbar w p e + p F
    · obtain ⟨e, heU, hee⟩ := hsing
      have heF : e ≠ F := by simpa using (Finset.mem_sdiff.mp heU).2
      exact canonical_strict_singleton w p hτ hsmall F e heF hpF hee htotF
    · push_neg at hsing
      have hsmallF : ∀ g ∈ (Finset.univ \ ({F} : Finset G)), vbar w p g < (2 / 3) * τ := by
        intro g hg
        have h := hsing g hg
        linarith
      have hpFlt : p F < τ := lt_of_le_of_lt (le_max_left _ _) (hsmall F)
      have htot3 : 3 * τ ≤ vbarSum w p (Finset.univ \ ({F} : Finset G)) := by linarith
      have hFuniv : vbarSum w p Finset.univ
          = vbarSum w p (Finset.univ \ ({F} : Finset G)) + vbar w p F := by
        rw [vbarSum_sdiff w p (Finset.subset_univ ({F} : Finset G))]
        simp [vbarSum]
      have hFge : p F ≤ vbar w p F := le_max_left _ _
      exact canonical_strict_two_pure w p hp hτ F hsmallF htot3 (by rw [hFuniv]; linarith)
  · -- at most one part carries more than `M/4`
    push_neg at hbig
    obtain ⟨lo, hlo⟩ : ∃ lo : Fin 3, ∀ i, i ≠ lo → q i ≤ M / 4 := by
      by_cases h0 : M / 4 < q 0
      · refine ⟨0, fun i hi => ?_⟩
        by_contra hcon
        exact absurd (hbig i 0 hi (lt_of_not_ge hcon)) (not_le.mpr h0)
      · by_cases h1 : M / 4 < q 1
        · refine ⟨1, fun i hi => ?_⟩
          by_contra hcon
          exact absurd (hbig i 1 hi (lt_of_not_ge hcon)) (not_le.mpr h1)
        · refine ⟨2, fun i hi => ?_⟩
          push_neg at h0 h1
          fin_cases i <;> simp_all
    refine canonical_strict_pure_parts w p A s q hdisjA hdisjs hq0 hqsum hge hscard lo ?_ ?_
    · intro i hi
      have h := hlo i hi
      rw [hτdef]; linarith
    · rw [hτdef]; linarith
end FairSelling
