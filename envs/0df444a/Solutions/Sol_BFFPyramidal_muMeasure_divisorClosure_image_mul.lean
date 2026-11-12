-- Prove2me | solution 1 for BFFPyramidal.muMeasure_divisorClosure_image_mul
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T18:51:45.913961+00:00
-- url     : https://prove2.me/submissions/9dee4ae0-97a2-4b5e-894e-f4ca9ea22516

import Mathlib
import Definitions.Def_BFFPyramidal_arithmetic

open BFFPyramidal Finset

/-- Membership in the divisor closure. -/
private lemma mem_divisorClosure_iff {R : Finset ℕ} {d : ℕ} :
    d ∈ divisorClosure R ↔ ∃ m ∈ R, d ∣ m ∧ m ≠ 0 := by
  simp [divisorClosure, Nat.mem_divisors]

/-- The basic divisibility reformulation: `N ∣ m * j` iff the order `N / gcd N j` divides `m`. -/
private lemma dvd_mul_iff_div_gcd_dvd {N : ℕ} (hN : 0 < N) (j m : ℕ) :
    N ∣ m * j ↔ N / N.gcd j ∣ m := by
  have hgpos : 0 < N.gcd j := by
    rcases Nat.eq_zero_or_pos (N.gcd j) with h | h
    · rw [Nat.gcd_eq_zero_iff] at h; omega
    · exact h
  have hgN : N.gcd j ∣ N := Nat.gcd_dvd_left N j
  have hgj : N.gcd j ∣ j := Nat.gcd_dvd_right N j
  have hNg : N / N.gcd j * N.gcd j = N := Nat.div_mul_cancel hgN
  have hjg : j / N.gcd j * N.gcd j = j := Nat.div_mul_cancel hgj
  have hcop : Nat.Coprime (N / N.gcd j) (j / N.gcd j) := Nat.coprime_div_gcd_div_gcd hgpos
  constructor
  · intro h
    have h2 : N / N.gcd j * N.gcd j ∣ m * (j / N.gcd j) * N.gcd j := by
      rw [hNg, mul_assoc, hjg]; exact h
    have h3 : N / N.gcd j ∣ m * (j / N.gcd j) :=
      (Nat.mul_dvd_mul_iff_right hgpos).mp h2
    exact hcop.dvd_of_dvd_mul_right h3
  · intro h
    have h2 : N / N.gcd j * N.gcd j ∣ m * j := mul_dvd_mul h hgj
    rwa [hNg] at h2

/-- Counting interpretation of `μ (D R)`: if every member of `R` divides `N > 0`, then
`μ (D R)` is the number of `j < N` killed by some `m ∈ R`. -/
private lemma count_eq_muMeasure (N : ℕ) (hN : 0 < N) (R : Finset ℕ) (hdvd : ∀ m ∈ R, m ∣ N) :
    #{j ∈ range N | ∃ m ∈ R, N ∣ m * j} = muMeasure (divisorClosure R) := by
  have hpos : ∀ m ∈ R, m ≠ 0 := by
    intro m hm h
    exact hN.ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd m hm))
  have hsub : divisorClosure R ⊆ N.divisors := by
    intro d hd
    obtain ⟨m, hm, hdm, hm0⟩ := mem_divisorClosure_iff.mp hd
    exact Nat.mem_divisors.mpr ⟨hdm.trans (hdvd m hm), hN.ne'⟩
  have hfil : {j ∈ range N | ∃ m ∈ R, N ∣ m * j}
      = {j ∈ range N | N / N.gcd j ∈ divisorClosure R} := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨m, hm, h⟩
      exact mem_divisorClosure_iff.mpr
        ⟨m, hm, (dvd_mul_iff_div_gcd_dvd hN j m).mp h, hpos m hm⟩
    · intro h
      obtain ⟨m, hm, hdm, -⟩ := mem_divisorClosure_iff.mp h
      exact ⟨m, hm, (dvd_mul_iff_div_gcd_dvd hN j m).mpr hdm⟩
  rw [hfil]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun j => N.gcd j) (t := N.divisors)
    (fun x _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hN.ne'⟩)]
  have step : ∀ c ∈ N.divisors,
      #{j ∈ {j ∈ range N | N / N.gcd j ∈ divisorClosure R} | N.gcd j = c}
        = if N / c ∈ divisorClosure R then Nat.totient (N / c) else 0 := by
    intro c hc
    rw [Finset.filter_filter]
    by_cases hmem : N / c ∈ divisorClosure R
    · rw [if_pos hmem, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hc)]
      congr 1
      apply Finset.filter_congr
      intro j _
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hmem, h⟩
    · rw [if_neg hmem, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h
      exact hmem (h.2 ▸ h.1)
  rw [Finset.sum_congr rfl step]
  rw [Nat.sum_div_divisors N (fun d => if d ∈ divisorClosure R then Nat.totient d else 0)]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  rfl

/-- A sum of a function of period `N` over `range (k * N)` is `k` times its sum over `range N`. -/
private lemma sum_range_mul_of_periodic (N : ℕ) (g : ℕ → ℕ) (hg : ∀ j, g (j % N) = g j) :
    ∀ k : ℕ, ∑ j ∈ range (k * N), g j = k * ∑ j ∈ range N, g j := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hkN : (k + 1) * N = k * N + N := by ring
    rw [hkN, Finset.sum_range_add, ih]
    have hshift : ∀ x ∈ range N, g (k * N + x) = g x := by
      intro x _
      have hmod : (k * N + x) % N = x % N := by
        rw [Nat.add_comm, Nat.mul_comm]
        exact Nat.add_mul_mod_self_left x N k
      rw [← hg (k * N + x), hmod, hg x]
    rw [Finset.sum_congr rfl hshift]
    ring

theorem solution (k : ℕ) (hk : 0 < k) (R : Finset ℕ) (hR : ∀ m ∈ R, 0 < m) :
    muMeasure (divisorClosure (R.image (fun m => k * m)))
      = k * muMeasure (divisorClosure R) := by
  classical
  set N := ∏ m ∈ R, m with hNdef
  have hN : 0 < N := Finset.prod_pos hR
  have hdvd : ∀ m ∈ R, m ∣ N := fun m hm => Finset.dvd_prod_of_mem _ hm
  have hkN : 0 < k * N := Nat.mul_pos hk hN
  have hdvd' : ∀ m' ∈ R.image (fun m => k * m), m' ∣ k * N := by
    intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
    exact Nat.mul_dvd_mul_left k (hdvd m hm)
  rw [← count_eq_muMeasure N hN R hdvd, ← count_eq_muMeasure (k * N) hkN _ hdvd']
  -- rewrite the predicate on the left
  have hpred : {j ∈ range (k * N) | ∃ m' ∈ R.image (fun m => k * m), k * N ∣ m' * j}
      = {j ∈ range (k * N) | ∃ m ∈ R, N ∣ m * j} := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨m', hm', h⟩
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
      refine ⟨m, hm, ?_⟩
      rw [mul_assoc] at h
      exact (Nat.mul_dvd_mul_iff_left hk).mp h
    · rintro ⟨m, hm, h⟩
      refine ⟨k * m, Finset.mem_image_of_mem _ hm, ?_⟩
      rw [mul_assoc]
      exact Nat.mul_dvd_mul_left k h
  rw [hpred, Finset.card_filter, Finset.card_filter]
  have hg : ∀ j, (if ∃ m ∈ R, N ∣ m * (j % N) then 1 else 0)
      = (if ∃ m ∈ R, N ∣ m * j then 1 else 0) := by
    intro j
    have hiff : (∃ m ∈ R, N ∣ m * (j % N)) ↔ (∃ m ∈ R, N ∣ m * j) := by
      refine exists_congr fun m => and_congr_right fun _ => ?_
      have h : m * (j % N) ≡ m * j [MOD N] := Nat.ModEq.mul_left m (Nat.mod_modEq j N)
      rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
      exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩
    simp only [hiff]
  exact sum_range_mul_of_periodic N _ hg k
