-- Prove2me | solution 1 for FBMSP.discrete_candidate_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:15:07.380441+00:00
-- url     : https://prove2.me/submissions/db186f62-8596-41bb-a070-777c807ee47b

import Definitions.Def_FBMSP_DiscreteCandidates

open FBMSP
open scoped BigOperators

private theorem rounded_price (P : Finset ℝ) (hzero : 0 ∈ P)
    (p : ℝ) (hp : 0 ≤ p) :
    ∃ q ∈ P, ∀ v : ℝ, (0 ≤ v → v ∈ P) →
      (if p ≤ v then p else 0) ≤ (if q ≤ v then q else 0) := by
  classical
  let S := P.filter (fun v => p ≤ v)
  by_cases hS : S.Nonempty
  · let q := S.min' hS
    have hqS : q ∈ S := Finset.min'_mem _ _
    have hqP : q ∈ P := (Finset.mem_filter.mp hqS).1
    have hpq : p ≤ q := (Finset.mem_filter.mp hqS).2
    refine ⟨q, hqP, ?_⟩
    intro v hv
    by_cases hpv : p ≤ v
    · have hvS : v ∈ S := Finset.mem_filter.mpr ⟨hv (hp.trans hpv), hpv⟩
      have hqv : q ≤ v := Finset.min'_le S v hvS
      simpa only [if_pos hpv, if_pos hqv] using hpq
    · simp only [if_neg hpv]
      split_ifs
      · exact hp.trans hpq
      · exact le_rfl
  · refine ⟨0, hzero, ?_⟩
    intro v hv
    have hpv : ¬ p ≤ v := by
      intro hpv
      exact hS ⟨v, Finset.mem_filter.mpr ⟨hv (hp.trans hpv), hpv⟩⟩
    simp [hpv]

private theorem realized_value_mem (I : RationalMarketInput)
    (i : Fin I.means.length) (j : Fin I.shocks.length)
    (h : 0 ≤ (I.means.get i : ℝ) + (I.shocks.get j : ℝ)) :
    (I.means.get i : ℝ) + (I.shocks.get j : ℝ) ∈ rationalCandidatePrices I := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_filter.mpr
  refine ⟨?_, h⟩
  apply Finset.mem_image.mpr
  refine ⟨(I.means.get i, I.shocks.get j), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr (List.get_mem _ _),
        List.mem_toFinset.mpr (List.get_mem _ _)⟩
  · simp

theorem solution (I : RationalMarketInput)
    (hvalid : ValidRationalMarket I) :
    0 ∈ rationalCandidatePrices I ∧
    (∀ p ∈ rationalCandidatePrices I, 0 ≤ p) ∧
    (rationalCandidatePrices I).card ≤ I.means.length * I.shocks.length + 1 ∧
    ∀ (prices : Fin I.segments → ℝ)
      (assignment : Fin I.means.length → Fin I.segments),
      (∀ j, 0 ≤ prices j) →
      ∃ candidatePrices : Fin I.segments → ℝ,
        (∀ j, candidatePrices j ∈ rationalCandidatePrices I) ∧
        rationalMarketRevenue I prices assignment ≤
          rationalMarketRevenue I candidatePrices assignment := by
  classical
  have hzero : 0 ∈ rationalCandidatePrices I := by
    simp [rationalCandidatePrices]
  refine ⟨hzero, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact le_rfl
    · exact (Finset.mem_filter.mp hp).2
  · unfold rationalCandidatePrices
    calc
      _ ≤
          ((((I.means.toFinset.product I.shocks.toFinset).image
            (fun z : ℚ × ℚ => ((z.1 + z.2 : ℚ) : ℝ))).filter
            (fun p => 0 ≤ p)).card) + 1 := Finset.card_insert_le _ _
      _ ≤ ((I.means.toFinset.product I.shocks.toFinset).image
            (fun z : ℚ × ℚ => ((z.1 + z.2 : ℚ) : ℝ))).card + 1 :=
        Nat.add_le_add_right (Finset.card_filter_le _ _) 1
      _ ≤ (I.means.toFinset.product I.shocks.toFinset).card + 1 :=
        Nat.add_le_add_right (Finset.card_image_le) 1
      _ = I.means.toFinset.card * I.shocks.toFinset.card + 1 := by
        exact congrArg (fun n : ℕ => n + 1) (Finset.card_product _ _)
      _ ≤ I.means.length * I.shocks.length + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul
          I.means.toFinset_card_le I.shocks.toFinset_card_le) 1
  · intro prices assignment hp
    have hround : ∀ j, ∃ q ∈ rationalCandidatePrices I, ∀ v : ℝ,
        (0 ≤ v → v ∈ rationalCandidatePrices I) →
        (if prices j ≤ v then prices j else 0) ≤ (if q ≤ v then q else 0) :=
      fun j => rounded_price _ hzero _ (hp j)
    choose q hq hdom using hround
    refine ⟨q, hq, ?_⟩
    rcases hvalid with ⟨_, _, _, hwl, hw, _, _, hsl, hs, _, _, _⟩
    unfold rationalMarketRevenue
    apply Finset.sum_le_sum
    intro i hi
    have hwi : 0 ≤ (I.weights.getD i.val 0 : ℝ) := by
      have hilt : i.val < I.weights.length := by rw [hwl]; exact i.isLt
      rw [List.getD_eq_getElem I.weights 0 hilt]
      exact_mod_cast (le_of_lt (hw _ (List.getElem_mem hilt)))
    apply mul_le_mul_of_nonneg_left _ hwi
    apply Finset.sum_le_sum
    intro j hj
    have hsj : 0 ≤ (I.shockWeights.getD j.val 0 : ℝ) := by
      have hjlt : j.val < I.shockWeights.length := by rw [hsl]; exact j.isLt
      rw [List.getD_eq_getElem I.shockWeights 0 hjlt]
      exact_mod_cast (hs _ (List.getElem_mem hjlt))
    apply mul_le_mul_of_nonneg_left _ hsj
    exact hdom (assignment i) _
      (fun hv => realized_value_mem I i j hv)
