-- Prove2me | solution 1 for Erdos287.consecutive_omissions_from_residue_implication_cycle
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:53:35.485839+00:00
-- url     : https://prove2.me/submissions/a8f7495b-0729-4e07-9e1d-c9af94468a4b

import Mathlib

open Finset

set_option autoImplicit false

/-- A cycle joining a keep literal to its opposite and back certifies a gap
when each implication follows from spacing, known positions, or a congruence. -/
theorem solution (D H R : Finset ℕ) (m M C : ℕ)
    (hD : D ⊆ Finset.Icc m M) (hpos : ∀ n ∈ D, 0 < n)
    (hdiv : ∀ n ∈ D, n ∣ C) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : Disjoint D H) (hR : R ⊆ D)
    (edge : (ℕ × Bool) → (ℕ × Bool) → Prop)
    (hEdges : ∀ a b, edge a b →
      (a.2 = false ∧ b.2 = true ∧
        ((a.1 + 1 = b.1 ∧ m ≤ a.1 ∧ b.1 ≤ M) ∨
         (b.1 + 1 = a.1 ∧ m ≤ b.1 ∧ a.1 ≤ M))) ∨
      (b.2 = true ∧ b.1 ∈ R) ∨ (b.2 = false ∧ b.1 ∈ H) ∨
      ∃ (q : ℕ) (S : Finset ℕ), q ∣ C ∧ a.1 ∈ S ∧ b.1 ∈ S ∧
        (∀ n ∈ Finset.Icc m M, ¬ q ∣ C / n → n ∈ S) ∧
        (∀ T ⊆ S, q ∣ (∑ n ∈ T, C / n) →
          (a.1 ∈ T ↔ a.2 = true) → (b.1 ∈ T ↔ b.2 = true)))
    (hPaths : ∃ n, Relation.ReflTransGen edge (n, true) (n, false) ∧
      Relation.ReflTransGen edge (n, false) (n, true)) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D := by
  by_contra hg
  have hnxt (n : ℕ) (hl : m ≤ n) (hr : n + 1 ≤ M) (hn : n ∉ D) : n + 1 ∈ D := by
    by_contra hh
    exact hg ⟨n, hl, hr, hn, hh⟩
  have hnum : (∑ n ∈ D, C / n) = C := by
    have hscale : (C : ℚ) * (∑ n ∈ D, (1 : ℚ) / n) = ((∑ n ∈ D, C / n : ℕ) : ℚ) := by
      rw [mul_sum, Nat.cast_sum]
      refine sum_congr rfl fun n hn => ?_
      rw [mul_one_div]
      apply (div_eq_iff (Nat.cast_ne_zero.mpr (hpos n hn).ne')).mpr
      exact_mod_cast (Nat.div_mul_cancel (hdiv n hn)).symm
    rw [hsum, mul_one] at hscale
    exact_mod_cast hscale.symm
  let holds (a : ℕ × Bool) := (a.1 ∈ D ↔ a.2 = true)
  have hstep (a b : ℕ × Bool) (hab : edge a b) : holds a → holds b := by
    intro ha
    rcases hEdges a b hab with h | h | h | h
    · obtain ⟨ha₀, hb₁, hpair⟩ := h
      have hna : a.1 ∉ D := fun h => Bool.false_ne_true (ha₀ ▸ ha.mp h)
      have hb : b.1 ∈ D := by
        rcases hpair with ⟨he, hl, hr⟩ | ⟨he, hl, hr⟩
        · rw [← he]
          exact hnxt a.1 hl (he.symm ▸ hr) hna
        · by_contra hnb
          exact hna (he ▸ hnxt b.1 hl (he.symm ▸ hr) hnb)
      exact ⟨fun _ => hb₁, fun _ => hb⟩
    · exact ⟨fun _ => h.1, fun _ => hR h.2⟩
    · have hn : b.1 ∉ D := fun hn => disjoint_left.mp hH hn h.2
      exact ⟨fun hh => (hn hh).elim, fun hh => (Bool.false_ne_true (h.1 ▸ hh)).elim⟩
    · obtain ⟨q, S, hq, haS, hbS, hsupport, hcert⟩ := h
      let T := D ∩ S
      have hout : q ∣ ∑ n ∈ D \ S, C / n := by
        refine dvd_sum fun n hn => ?_
        obtain ⟨hnD, hnS⟩ := mem_sdiff.mp hn
        by_contra hh
        exact hnS (hsupport n (hD hnD) hh)
      have hdiff : D \ T = D \ S := by
        ext n
        simp only [T, mem_sdiff, mem_inter]
        tauto
      have hsplit := sum_sdiff (f := fun n => C / n) (inter_subset_left : T ⊆ D)
      rw [hdiff, hnum] at hsplit
      have hT : q ∣ ∑ n ∈ T, C / n := by
        have he : (∑ n ∈ T, C / n) = C - ∑ n ∈ D \ S, C / n := by
          have hh := congrArg (fun x : ℕ => x - ∑ n ∈ D \ S, C / n) hsplit
          simpa only [T, Nat.add_sub_cancel_left] using hh
        rw [he]
        exact Nat.dvd_sub hq hout
      have haT : a.1 ∈ T ↔ a.2 = true := by simpa only [T, mem_inter, haS, and_true] using ha
      have hbT := hcert T inter_subset_right hT haT
      simpa only [holds, T, mem_inter, hbS, and_true] using hbT
  have hwalk {a b : ℕ × Bool} (hh : Relation.ReflTransGen edge a b) : holds a → holds b := by
    induction hh with
    | refl => exact id
    | tail _ hab ih => exact fun ha => hstep _ _ hab (ih ha)
  obtain ⟨n, hp₁, hp₂⟩ := hPaths
  by_cases hn : n ∈ D
  · have hy : holds (n, true) := ⟨fun _ => rfl, fun _ => hn⟩
    exact Bool.false_ne_true ((hwalk hp₁ hy).mp hn)
  · have hy : holds (n, false) := ⟨fun h => (hn h).elim, fun h => (Bool.false_ne_true h).elim⟩
    exact hn ((hwalk hp₂ hy).mpr rfl)

