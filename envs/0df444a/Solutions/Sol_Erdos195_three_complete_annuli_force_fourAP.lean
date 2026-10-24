-- Prove2me | solution 1 for Erdos195.three_complete_annuli_force_fourAP
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:52:47.140775+00:00
-- url     : https://prove2.me/submissions/1580ebb6-657a-4db3-9054-462a30f71ac7

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195.AnnulusResearch

/-- The complete signed geometric annulus, with the same endpoints as Adenwalla's blocks. -/
def annulus (b : ℤ) (j : ℕ) (x : ℤ) : Prop :=
  (-b ^ j ≤ x ∧ x < -b ^ (j - 1)) ∨ (b ^ (j - 1) ≤ x ∧ x < b ^ j)

/-- Three complete annuli cannot be ordered chronologically with a single parity
precedence throughout the third annulus and avoid four-term progressions. -/
theorem three_annuli_parity_obstruction (b : ℤ) (hb : 4 ≤ b) (heven : b % 2 = 0)
    (pos : ℤ → ℕ)
    (h12 : ∀ x y, annulus b 1 x → annulus b 2 y → pos x < pos y)
    (h23 : ∀ x y, annulus b 2 x → annulus b 3 y → pos x < pos y)
    (hpar : (∀ x y, annulus b 3 x → annulus b 3 y → x % 2 = 1 → y % 2 = 0 → pos x < pos y) ∨
      (∀ x y, annulus b 3 x → annulus b 3 y → x % 2 = 0 → y % 2 = 1 → pos x < pos y)) :
    ∃ a d : ℤ, d ≠ 0 ∧ pos a < pos (a + d) ∧
      pos (a + d) < pos (a + 2 * d) ∧ pos (a + 2 * d) < pos (a + 3 * d) := by
  have hb0 : 0 ≤ b := by omega
  have hsq : 16 ≤ b ^ 2 := by nlinarith
  have hcube : 3 * b ^ 2 + 2 * b ≤ b ^ 3 := by
    have hq : 0 ≤ b ^ 2 - 3 * b - 2 := by nlinarith
    have := mul_nonneg hb0 hq
    nlinarith
  have hA1 : annulus b 1 (b - 1) := by
    right
    norm_num
    omega
  have hA2 : annulus b 1 (b - 2) := by
    right
    norm_num
    omega
  have hB1 : annulus b 2 (-b ^ 2) := by
    left
    norm_num
    nlinarith
  have hB2 : annulus b 2 (-b ^ 2 + 1) := by
    left
    norm_num
    nlinarith
  have hC1 : annulus b 3 (-2 * b ^ 2 - b + 1) := by
    left
    norm_num
    constructor <;> nlinarith
  have hD1 : annulus b 3 (-3 * b ^ 2 - 2 * b + 2) := by
    left
    norm_num
    constructor <;> nlinarith
  have hC2 : annulus b 3 (-2 * b ^ 2 - b + 4) := by
    left
    norm_num
    constructor <;> nlinarith
  have hD2 : annulus b 3 (-3 * b ^ 2 - 2 * b + 7) := by
    left
    norm_num
    constructor <;> nlinarith
  have hpC1 : (-2 * b ^ 2 - b + 1) % 2 = 1 := by omega
  have hpD1 : (-3 * b ^ 2 - 2 * b + 2) % 2 = 0 := by
    have hsqeven : b ^ 2 % 2 = 0 := by rw [pow_two, Int.mul_emod, heven]; norm_num
    omega
  have hpC2 : (-2 * b ^ 2 - b + 4) % 2 = 0 := by omega
  have hpD2 : (-3 * b ^ 2 - 2 * b + 7) % 2 = 1 := by
    have hsqeven : b ^ 2 % 2 = 0 := by rw [pow_two, Int.mul_emod, heven]; norm_num
    omega
  rcases hpar with hpar | hpar
  · refine ⟨b - 1, -b ^ 2 - b + 1, by nlinarith, ?_, ?_, ?_⟩
    · convert h12 _ _ hA1 hB1 using 1; congr 1; ring
    · convert h23 _ _ hB1 hC1 using 1 <;> congr 1 <;> ring
    · convert hpar _ _ hC1 hD1 hpC1 hpD1 using 1 <;> congr 1 <;> ring
  · refine ⟨b - 2, -b ^ 2 - b + 3, by nlinarith, ?_, ?_, ?_⟩
    · convert h12 _ _ hA2 hB2 using 1; congr 1; ring
    · convert h23 _ _ hB2 hC2 using 1 <;> congr 1 <;> ring
    · convert hpar _ _ hC2 hD2 hpC2 hpD2 using 1 <;> congr 1 <;> ring

/-- The obstruction is to the original monotone-AP predicate, with both directions allowed. -/
theorem permutation_has_fourAP_of_annuli (b : ℤ) (hb : 4 ≤ b) (heven : b % 2 = 0)
    (f : ℕ ≃ ℤ)
    (h12 : ∀ x y, annulus b 1 x → annulus b 2 y → f.symm x < f.symm y)
    (h23 : ∀ x y, annulus b 2 x → annulus b 3 y → f.symm x < f.symm y)
    (hpar : (∀ x y, annulus b 3 x → annulus b 3 y → x % 2 = 1 → y % 2 = 0 → f.symm x < f.symm y) ∨
      (∀ x y, annulus b 3 x → annulus b 3 y → x % 2 = 0 → y % 2 = 1 → f.symm x < f.symm y)) :
    HasMonotoneAP f 4 := by
  obtain ⟨a, d, _, h01, h12', h23'⟩ :=
    three_annuli_parity_obstruction b hb heven f.symm h12 h23 hpar
  refine ⟨[f.symm a, f.symm (a + d), f.symm (a + 2 * d), f.symm (a + 3 * d)], ?_, ?_⟩
  · refine ⟨a, d, Or.inl ?_⟩
    simp [List.range_succ]
  · simpa [List.pairwise_cons] using
      And.intro (And.intro h01 (And.intro (lt_trans h01 h12')
        (lt_trans h01 (lt_trans h12' h23'))))
        (And.intro (And.intro h12' (lt_trans h12' h23')) h23')

end Erdos195.AnnulusResearch

/-- Chronological complete annuli with a parity-grouped third annulus force a four-AP. -/
theorem solution (b : ℤ) (hb : 4 ≤ b) (heven : b % 2 = 0) (f : ℕ ≃ ℤ) :
    let A : ℕ → ℤ → Prop := fun j x =>
      (-b ^ j ≤ x ∧ x < -b ^ (j - 1)) ∨
        (b ^ (j - 1) ≤ x ∧ x < b ^ j)
    (∀ x y, A 1 x → A 2 y → f.symm x < f.symm y) →
    (∀ x y, A 2 x → A 3 y → f.symm x < f.symm y) →
    ((∀ x y, A 3 x → A 3 y → x % 2 = 1 → y % 2 = 0 →
        f.symm x < f.symm y) ∨
      (∀ x y, A 3 x → A 3 y → x % 2 = 0 → y % 2 = 1 →
        f.symm x < f.symm y)) →
    Erdos195.HasMonotoneAP f 4 := by
  dsimp only
  intro h12 h23 hpar
  exact Erdos195.AnnulusResearch.permutation_has_fourAP_of_annuli b hb heven f h12 h23 hpar
