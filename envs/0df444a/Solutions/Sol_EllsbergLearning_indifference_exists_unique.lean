-- Prove2me | solution 1 for EllsbergLearning.indifference_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:25:13.811754+00:00
-- url     : https://prove2.me/submissions/4d4dd9e8-ba72-443f-8a34-bfd62fa6648c

import Definitions.Def_EllsbergLearning_Params

namespace Aux_EllsIEU

theorem key (A B x u00 u01 u10 u11 : ℝ) (hA : 0 < A) (hB : 0 < B) (hx : 0 < x)
    (hu : u00 = u11) :
    (A * x / (1 + A * x) * u11 + (1 - A * x / (1 + A * x)) * u10 =
      B * x / (1 + B * x) * u01 + (1 - B * x / (1 + B * x)) * u00) ↔
    A * B * (u00 - u01) * x ^ 2 + B * (u10 - u01) * x - (u00 - u10) = 0 := by
  have h1 : 0 < 1 + A * x := by positivity
  have h2 : 0 < 1 + B * x := by positivity
  subst hu
  have hid : (A * x / (1 + A * x) * u00 + (1 - A * x / (1 + A * x)) * u10) -
      (B * x / (1 + B * x) * u01 + (1 - B * x / (1 + B * x)) * u00) =
      (A * B * (u00 - u01) * x ^ 2 + B * (u10 - u01) * x - (u00 - u10)) /
        ((1 + A * x) * (1 + B * x)) := by
    field_simp
    ring
  rw [← sub_eq_zero, hid, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exfalso; have := mul_pos h1 h2; linarith
  · intro h; exact Or.inl h

end Aux_EllsIEU

open EllsbergLearning Aux_EllsIEU in
theorem solution (p : Params) (hp : p.Valid) :
    ∃! q : ℝ × ℝ × (ℝ → ℝ), p.IsIndifference q.1 q.2.1 q.2.2 := by
  have hm1 := hp.mLo0_pos
  have hm2 := hp.mLo0_lt_mUp0
  have hm3 := hp.mUp0_lt_one
  obtain ⟨A, hA⟩ : ∃ A, A = p.mLo0 / (1 - p.mLo0) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = p.mUp0 / (1 - p.mUp0) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; apply div_pos <;> linarith
  have hB0 : 0 < B := by rw [hB]; apply div_pos <;> linarith
  have hu := hp.u00_eq_u11
  have h01 := hp.u01_lt_u00
  have h10 := hp.u10_lt_u11
  obtain ⟨a2, ha2⟩ : ∃ a2, a2 = A * B * (p.u 0 0 - p.u 0 1) := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a1, a1 = B * (p.u 1 0 - p.u 0 1) := ⟨_, rfl⟩
  obtain ⟨a0, ha0⟩ : ∃ a0, a0 = p.u 0 0 - p.u 1 0 := ⟨_, rfl⟩
  have ha2p : 0 < a2 := by rw [ha2]; apply mul_pos (mul_pos hA0 hB0); linarith
  have ha0p : 0 < a0 := by rw [ha0]; linarith
  have hkey : ∀ x, 0 < x →
      ((A * x / (1 + A * x) * p.u 1 1 + (1 - A * x / (1 + A * x)) * p.u 1 0 =
        B * x / (1 + B * x) * p.u 0 1 + (1 - B * x / (1 + B * x)) * p.u 0 0) ↔
      a2 * x ^ 2 + a1 * x - a0 = 0) := by
    intro x hx
    rw [key A B x _ _ _ _ hA0 hB0 hx hu, ha2, ha1, ha0]
  -- the positive root
  obtain ⟨D, hD⟩ : ∃ D, D = a1 ^ 2 + 4 * a2 * a0 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hsD := Real.sq_sqrt hD0
  have hs0 := Real.sqrt_nonneg D
  have hsgt : a1 < Real.sqrt D := by
    have : a1 ^ 2 < D := by rw [hD]; nlinarith [mul_pos ha2p ha0p]
    nlinarith [sq_nonneg (a1 + Real.sqrt D)]
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = (-a1 + Real.sqrt D) / (2 * a2) := ⟨_, rfl⟩
  have hx0p : 0 < x0 := by rw [hx0]; apply div_pos <;> linarith
  have hQ0 : a2 * x0 ^ 2 + a1 * x0 - a0 = 0 := by
    have ha2ne : a2 ≠ 0 := ha2p.ne'
    have hid : a2 * x0 ^ 2 + a1 * x0 - a0 = ((Real.sqrt D) ^ 2 - D) / (4 * a2) := by
      rw [hx0]
      field_simp
      rw [hD]
      ring
    rw [hid, hsD]
    simp
  have huniq : ∀ x, 0 < x → a2 * x ^ 2 + a1 * x - a0 = 0 → x = x0 := by
    intro x hx hQ
    have hpx : 0 < a2 * x + a1 := by
      have : x * (a2 * x + a1) = a0 := by linear_combination hQ
      have h' : 0 < x * (a2 * x + a1) := by rw [this]; exact ha0p
      exact (pos_iff_pos_of_mul_pos h').mp hx
    have hprod : (x - x0) * (a2 * (x + x0) + a1) = 0 := by linear_combination hQ - hQ0
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exfalso; nlinarith
  -- the boundary
  have hθ := hp.θ_lt
  have hσ := hp.σ_pos
  have hk : 0 < (p.θ₁ - p.θ₀) / p.σ ^ 2 := by apply div_pos <;> [linarith; positivity]
  have hθne : p.θ₁ - p.θ₀ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hθ)
  have hσne : p.σ ≠ 0 := hσ.ne'
  let zf : ℝ → ℝ := fun t =>
    (Real.log x0 + (p.θ₁ ^ 2 - p.θ₀ ^ 2) * t / (2 * p.σ ^ 2)) / ((p.θ₁ - p.θ₀) / p.σ ^ 2)
  have hphi : ∀ t, p.phi t (zf t) = x0 := by
    intro t
    unfold Params.phi
    have : (p.θ₁ - p.θ₀) / p.σ ^ 2 * zf t - (p.θ₁ ^ 2 - p.θ₀ ^ 2) * t / (2 * p.σ ^ 2) =
        Real.log x0 := by
      simp only [zf]
      field_simp <;> ring
    rw [this, Real.exp_log hx0p]
  have hpostL : ∀ x t z, p.phi t z = x → p.mLo t z = A * x / (1 + A * x) := by
    intro x t z h
    unfold Params.mLo Params.post
    rw [h, ← hA]
  have hpostU : ∀ x t z, p.phi t z = x → p.mUp t z = B * x / (1 + B * x) := by
    intro x t z h
    unfold Params.mUp Params.post
    rw [h, ← hB]
  refine ⟨(A * x0 / (1 + A * x0), B * x0 / (1 + B * x0), zf),
    ⟨fun t => ⟨(hpostL x0 t (zf t) (hphi t)).symm, (hpostU x0 t (zf t) (hphi t)).symm⟩,
      (hkey x0 hx0p).2 hQ0⟩, ?_⟩
  rintro ⟨πL, πU, zt⟩ ⟨hall, heq⟩
  have hroot : ∀ t, p.phi t (zt t) = x0 := by
    intro t
    obtain ⟨h1, h2⟩ := hall t
    have hx : 0 < p.phi t (zt t) := Real.exp_pos _
    have hL := hpostL _ t (zt t) rfl
    have hU := hpostU _ t (zt t) rfl
    simp only at h1 h2 heq
    rw [h1, h2, hL, hU] at heq
    exact huniq _ hx ((hkey _ hx).1 heq)
  obtain ⟨h1, h2⟩ := hall 0
  simp only at h1 h2
  rw [hpostL x0 0 (zt 0) (hroot 0)] at h1
  rw [hpostU x0 0 (zt 0) (hroot 0)] at h2
  have hz : zt = zf := by
    funext t
    have h := hroot t
    unfold Params.phi at h
    rw [← Real.exp_log hx0p] at h
    have h' := Real.exp_injective h
    simp only [zf]
    field_simp
    field_simp at h'
    linarith
  rw [h1, h2, hz]
