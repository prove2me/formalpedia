-- Prove2me | solution 1 for BinaryQuadraticForm.existsUnique_reduced_and_finite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T00:12:40.250912+00:00
-- url     : https://prove2.me/submissions/6874fb20-ce0f-48c4-b9ab-ad0fd08086e8

import Mathlib
import Definitions.Def_RPLib_S3_HurwitzA

set_option autoImplicit false

namespace UploadHurwitz

open RamanujanPetersson.Hurwitz

/-- Textbook reducedness (`|b| ≤ a ≤ c`, `b ≥ 0` on the boundary) with `a ≠ 0` gives the library's `IsReduced`. -/
theorem isReduced_of_tb {a b c : ℤ} (ha : a ≠ 0)
    (h : |b| ≤ a ∧ a ≤ c ∧ (|b| = a ∨ a = c → 0 ≤ b)) : (⟨a, b, c⟩ : BQF).IsReduced := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb := abs_le.1 h1
  have ha0 : 0 ≤ a := le_trans (abs_nonneg b) h1
  show -a < b ∧ b ≤ a ∧ a ≤ c ∧ (a = c → 0 ≤ b)
  refine ⟨?_, hb.2, h2, fun hac => h3 (Or.inr hac)⟩
  by_contra hcon
  have hbeq : b = -a := by omega
  have habs : |b| = a := by rw [hbeq, abs_neg, abs_of_nonneg ha0]
  have := h3 (Or.inl habs)
  omega

/-- The library's `IsReduced` gives textbook reducedness. -/
theorem tb_of_isReduced {g : BQF} (hg : g.IsReduced) :
    |g.b| ≤ g.a ∧ g.a ≤ g.c ∧ (|g.b| = g.a ∨ g.a = g.c → 0 ≤ g.b) := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  refine ⟨abs_le.2 ⟨h1.le, h2⟩, h3, ?_⟩
  rintro (h | h)
  · rcases abs_cases g.b with ⟨h5, _⟩ | ⟨h5, _⟩ <;> omega
  · exact h4 h

/-- A triple whose form is `f ∘ γ` pointwise is the form `act γ f`. -/
theorem eq_act_of_forall {r1 r2 r3 : ℤ} {f : BQF} {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h : ∀ x y : ℤ, r1 * x ^ 2 + r2 * x * y + r3 * y ^ 2 =
          f.a * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
            f.b * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
            f.c * (γ 1 0 * x + γ 1 1 * y) ^ 2) :
    (⟨r1, r2, r3⟩ : BQF) = act γ f := by
  have e : ∀ x y : ℤ, r1 * x ^ 2 + r2 * x * y + r3 * y ^ 2 = (act γ f).eval x y := by
    intro x y; rw [h, eval_act]; rfl
  have h10 := e 1 0
  have h01 := e 0 1
  have h11 := e 1 1
  simp only [BQF.eval] at h10 h01 h11
  norm_num at h10 h01 h11
  refine BQF.ext ?_ ?_ ?_
  · show r1 = (act γ f).a; linarith
  · show r2 = (act γ f).b; linarith
  · show r3 = (act γ f).c; linarith

theorem main (a b c : ℤ) (ha : 0 < a) (hdisc : b ^ 2 - 4 * a * c < 0) :
    (∃! r : ℤ × ℤ × ℤ,
      (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1)) ∧
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∀ x y : ℤ,
        r.1 * x ^ 2 + r.2.1 * x * y + r.2.2 * y ^ 2 =
          a * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
            b * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
            c * (γ 1 0 * x + γ 1 1 * y) ^ 2) ∧
    {r : ℤ × ℤ × ℤ | r.2.1 ^ 2 - 4 * r.1 * r.2.2 = b ^ 2 - 4 * a * c ∧
      (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))}.Finite := by
  have hf : (⟨a, b, c⟩ : BQF).PosDef := ⟨ha, hdisc⟩
  obtain ⟨γ, hγ⟩ := exists_act_isReduced _ hf
  refine ⟨⟨((act γ ⟨a, b, c⟩).a, (act γ ⟨a, b, c⟩).b, (act γ ⟨a, b, c⟩).c),
    ⟨tb_of_isReduced hγ, γ, fun x y => eval_act γ ⟨a, b, c⟩ x y⟩, ?_⟩, ?_⟩
  · rintro ⟨r1, r2, r3⟩ ⟨hr, δ, hδ⟩
    dsimp only at hr hδ
    have e : (⟨r1, r2, r3⟩ : BQF) = act δ ⟨a, b, c⟩ := eq_act_of_forall (f := ⟨a, b, c⟩) hδ
    have hdr : (⟨r1, r2, r3⟩ : BQF).disc < 0 := by rw [e, disc_act]; exact hdisc
    have hr0 : r1 ≠ 0 := by
      intro h0
      have hd' : r2 ^ 2 - 4 * r1 * r3 < 0 := hdr
      rw [h0] at hd'
      nlinarith [sq_nonneg r2]
    have hred := isReduced_of_tb hr0 hr
    rw [e] at hred
    have hmem : act δ ⟨a, b, c⟩ ∈ MulAction.orbit (Matrix.SpecialLinearGroup (Fin 2) ℤ) (act γ ⟨a, b, c⟩) :=
      (mem_orbit_iff_act _ _).2 ⟨γ⁻¹ * δ, by rw [← act_mul, mul_inv_cancel_left]⟩
    have heq := hγ.eq_of_mem_orbit hred hmem
    rw [← heq, ← e]
  · refine ((finite_reduced (b ^ 2 - 4 * a * c)).image (fun g : BQF => (g.a, g.b, g.c))).subset ?_
    rintro ⟨r1, r2, r3⟩ ⟨hD, hr⟩
    dsimp only at hD hr
    have hr0 : r1 ≠ 0 := by
      intro h0
      rw [h0] at hD
      nlinarith [sq_nonneg r2]
    exact ⟨⟨r1, r2, r3⟩, ⟨hD, isReduced_of_tb hr0 hr⟩, rfl⟩

end UploadHurwitz

theorem solution (a b c : ℤ) (ha : 0 < a)
    (hdisc : b ^ 2 - 4 * a * c < 0) :
    (∃! r : ℤ × ℤ × ℤ,
      (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1)) ∧
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∀ x y : ℤ,
        r.1 * x ^ 2 + r.2.1 * x * y + r.2.2 * y ^ 2 =
          a * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
            b * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
            c * (γ 1 0 * x + γ 1 1 * y) ^ 2) ∧
    {r : ℤ × ℤ × ℤ | r.2.1 ^ 2 - 4 * r.1 * r.2.2 = b ^ 2 - 4 * a * c ∧
      (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))}.Finite := by
  exact UploadHurwitz.main a b c ha hdisc
