-- Prove2me | solution 1 for Erdos287.variable_auxiliary_phase_correction
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T18:20:24.315124+00:00
-- url     : https://prove2.me/submissions/1c79533e-8187-4469-9561-5f2bea652a49

import Mathlib

set_option autoImplicit false

private theorem shared_dvd (B m₁ m₂ t : ℤ) (hB : B ≠ 0)
    (hc : IsCoprime m₁ m₂) (h₁ : B * m₁ ∣ t) (h₂ : B * m₂ ∣ t) :
    B * m₁ * m₂ ∣ t := by
  obtain ⟨z, rfl⟩ := (dvd_mul_right B m₁).trans h₁
  simpa only [mul_assoc] using (mul_dvd_mul_iff_left hB).mpr
    (hc.mul_dvd ((mul_dvd_mul_iff_left hB).mp h₁) ((mul_dvd_mul_iff_left hB).mp h₂))

private theorem auxiliary_inverse (q c : ℤ) (hc : IsCoprime c q) :
    ∃ z : ℤ, q ∣ c * z - 1 := by
  obtain ⟨z, w, hw⟩ := hc
  refine ⟨z, -w, ?_⟩
  linear_combination hw

/-- Assign each shared auxiliary prime to one baseline constraint. The
full correction then allows different auxiliary residues on the two sides. -/
theorem solution (B m₁ m₂ q₁ q₂ a A₁ A₂ x x₀ n₁ n₂ k : ℤ) (hB : B ≠ 0)
    (hdiff : n₁ - n₂ = B * k)
    (hm : IsCoprime m₁ m₂)
    (hc₁ : IsCoprime (B * m₁) n₁) (hc₂ : IsCoprime (B * m₂) n₂)
    (hn₁ : IsCoprime q₁ n₁) (hn₂ : IsCoprime q₂ n₂)
    (hqq : IsCoprime q₁ q₂)
    (hL₁ : IsCoprime (B * m₁ * m₂) q₁) (hL₂ : IsCoprime (B * m₁ * m₂) q₂)
    (h₁ : B * m₁ ∣ x * n₁ - a) (h₂ : B * m₂ ∣ x * n₂ - a)
    (ha₁ : q₁ ∣ x * n₁ - A₁) (ha₂ : q₂ ∣ x * n₂ - A₂)
    (hb₁ : B * (m₁ * q₁) ∣ x₀ * n₁ - a) (hb₂ : B * (m₂ * q₂) ∣ x₀ * n₂ - a) :
    let L := B * m₁ * m₂
    ∃ z₁ z₂ l : ℤ,
      (q₁ ∣ L * q₂ * n₁ * z₁ - 1) ∧
      (q₂ ∣ L * q₁ * n₂ * z₂ - 1) ∧
      (L * q₁ * q₂ ∣ x - x₀ - L * q₂ * (A₁ - a) * z₁ - L * q₁ * (A₂ - a) * z₂) ∧
      x₀ * n₁ = a + (m₁ * q₁) * B * l ∧
      (m₂ * q₂) * n₁ ∣ (m₁ * q₁) * n₂ * l - a * k := by
  dsimp only
  let L := B * m₁ * m₂
  obtain ⟨z₁, hz₁⟩ := auxiliary_inverse q₁ (L * q₂ * n₁)
    ((hL₁.mul_left hqq.symm).mul_left hn₁.symm)
  obtain ⟨z₂, hz₂⟩ := auxiliary_inverse q₂ (L * q₁ * n₂)
    ((hL₂.mul_left hqq).mul_left hn₂.symm)
  have hmain₁ : B * m₁ ∣ x₀ * n₁ - a :=
    (show B * m₁ ∣ B * (m₁ * q₁) from ⟨q₁, by ring⟩).trans hb₁
  have hmain₂ : B * m₂ ∣ x₀ * n₂ - a :=
    (show B * m₂ ∣ B * (m₂ * q₂) from ⟨q₂, by ring⟩).trans hb₂
  have hdiff₁ : B * m₁ ∣ x - x₀ := by
    apply hc₁.dvd_of_dvd_mul_right
    convert h₁.sub hmain₁ using 1
    ring
  have hdiff₂ : B * m₂ ∣ x - x₀ := by
    apply hc₂.dvd_of_dvd_mul_right
    convert h₂.sub hmain₂ using 1
    ring
  have hL : L ∣ x - x₀ := shared_dvd B m₁ m₂ (x - x₀) hB hm hdiff₁ hdiff₂
  let E := x - x₀ - L * q₂ * (A₁ - a) * z₁ - L * q₁ * (A₂ - a) * z₂
  have hEL : L ∣ E :=
    (hL.sub ((dvd_mul_right L q₂).mul_right _ |>.mul_right _)).sub
      ((dvd_mul_right L q₁).mul_right _ |>.mul_right _)
  have hbq₁ : q₁ ∣ x₀ * n₁ - a :=
    (show q₁ ∣ B * (m₁ * q₁) from ⟨B * m₁, by ring⟩).trans hb₁
  have hbq₂ : q₂ ∣ x₀ * n₂ - a :=
    (show q₂ ∣ B * (m₂ * q₂) from ⟨B * m₂, by ring⟩).trans hb₂
  have he₁ : q₁ ∣ E := by
    apply hn₁.dvd_of_dvd_mul_right
    have hzero : q₁ ∣ L * q₁ * (A₂ - a) * z₂ * n₁ :=
      ⟨L * (A₂ - a) * z₂ * n₁, by ring⟩
    unfold E
    convert (ha₁.sub hbq₁).sub (hz₁.mul_left (A₁ - a)) |>.sub hzero using 1
    ring
  have he₂ : q₂ ∣ E := by
    apply hn₂.dvd_of_dvd_mul_right
    have hzero : q₂ ∣ L * q₂ * (A₁ - a) * z₁ * n₂ :=
      ⟨L * (A₁ - a) * z₁ * n₂, by ring⟩
    unfold E
    convert (ha₂.sub hbq₂).sub (hz₂.mul_left (A₂ - a)) |>.sub hzero using 1
    ring
  have hmod : L * q₁ * q₂ ∣ E :=
    (hL₂.mul_left hqq).mul_dvd (hL₁.mul_dvd hEL he₁) he₂
  obtain ⟨l, hl⟩ := hb₁
  obtain ⟨j, hj⟩ := hb₂
  refine ⟨z₁, z₂, l, hz₁, hz₂, hmod, ?_, j, ?_⟩
  · rw [mul_comm (m₁ * q₁) B]
    linarith only [hl]
  · apply mul_left_cancel₀ hB
    calc
      B * ((m₁ * q₁) * n₂ * l - a * k) = n₂ * (B * (m₁ * q₁) * l) - a * (B * k) := by ring
      _ = n₂ * (x₀ * n₁ - a) - a * (n₁ - n₂) := by rw [← hl, ← hdiff]
      _ = n₁ * (x₀ * n₂ - a) := by ring
      _ = B * ((m₂ * q₂) * n₁ * j) := by rw [hj]; ring

