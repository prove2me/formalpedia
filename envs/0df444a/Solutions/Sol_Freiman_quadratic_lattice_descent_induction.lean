-- Prove2me | solution 1 for Freiman.quadratic_lattice_descent_induction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:07:50.2305+00:00
-- url     : https://prove2.me/submissions/e228c804-35a5-4a56-a3ed-e1354bb93cbc

import Definitions.Def_Freiman_reducedForms

open Freiman

private theorem reduced_value_neg_both (α β : ℝ) (p q : ℤ) :
    reducedValue α β (-p) (-q) = reducedValue α β p q := by
  simp only [reducedValue, quadraticValue, Int.cast_neg]
  ring

theorem solution (R : ReducedOrbit)
    (haxis : ∀ n p q : ℤ, (p ≠ 0 ∨ q ≠ 0) → (p=0 ∨ q=0) →
      orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q|)
    (hpos : ∀ n p q : ℤ, 0<p → 0<q →
      |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R →
      ∃ m r s : ℤ, (r≠0 ∨ s≠0) ∧
        |reducedValue (R.alpha m) (R.beta m) r s|=|reducedValue (R.alpha n) (R.beta n) p q| ∧
        latticeSize r s<latticeSize p q)
    (hneg : ∀ n p q : ℤ, 0<p → q<0 →
      |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R →
      ∃ m r s : ℤ, (r≠0 ∨ s≠0) ∧
        |reducedValue (R.alpha m) (R.beta m) r s|=|reducedValue (R.alpha n) (R.beta n) p q| ∧
        latticeSize r s<latticeSize p q) :
    ∀ n p q : ℤ, (p ≠ 0 ∨ q ≠ 0) →
      orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q| := by
  have hall : ∀ k : ℕ, ∀ n p q : ℤ, latticeSize p q ≤ k → (p ≠ 0 ∨ q ≠ 0) →
      orbitReciprocalInfimum R ≤ |reducedValue (R.alpha n) (R.beta n) p q| := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n p q hsize hpq
      by_contra hbad
      have hv : |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R :=
        lt_of_not_ge hbad
      have hp0 : p ≠ 0 := by
        intro he
        exact (not_lt_of_ge (haxis n p q hpq (Or.inl he))) hv
      have hq0 : q ≠ 0 := by
        intro he
        exact (not_lt_of_ge (haxis n p q hpq (Or.inr he))) hv
      have hpositive : ∀ p q : ℤ, 0 < p → q ≠ 0 → latticeSize p q ≤ k →
          |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R → False := by
        intro p q hp hq hsz hv
        have hd : ∃ m r s : ℤ, (r ≠ 0 ∨ s ≠ 0) ∧
            |reducedValue (R.alpha m) (R.beta m) r s| = |reducedValue (R.alpha n) (R.beta n) p q| ∧
            latticeSize r s < latticeSize p q := by
          by_cases hqpos : 0 < q
          · exact hpos n p q hp hqpos hv
          · exact hneg n p q hp (by omega) hv
        obtain ⟨m, r, s, hrs, he, hlt⟩ := hd
        have hbound := ih (latticeSize r s) (lt_of_lt_of_le hlt hsz) m r s le_rfl hrs
        rw [he] at hbound
        exact (not_lt_of_ge hbound) hv
      by_cases hp : 0 < p
      · exact hpositive p q hp hq0 hsize hv
      · apply hpositive (-p) (-q) (by omega) (neg_ne_zero.mpr hq0)
        · simpa only [latticeSize, Int.natAbs_neg] using hsize
        · simpa only [reduced_value_neg_both] using hv
  intro n p q hpq
  exact hall (latticeSize p q) n p q le_rfl hpq
