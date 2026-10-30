-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInfty_of_tendstoZeroCInfty
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T21:10:27.728983+00:00
-- url     : https://prove2.me/submissions/a792318d-8333-4d2a-b168-5f01de44291d

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_norm_iteratedFDeriv_succ_le_of_halfPlane
import Theorems.Thm_FiniteEnergyPlane_monotone_of_add_le_two_mul_of_bddBelow



namespace FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

theorem expDecayCInfty_of_tendstoZeroCInfty_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ × ℝ → F) (hf : TendstoZeroCInfty f) (δ C s₀ : ℝ)
    (hdec : ∀ s ≥ s₀, ∀ t : ℝ, ‖f (s, t)‖ ≤ C * Real.exp (-(δ * s))) :
    ∀ b < δ, ExpDecayCInfty f b := by
  intro b hb
  obtain ⟨⟨s₀', hsm⟩, hlim⟩ := hf
  refine ⟨⟨s₀', hsm⟩, ?_⟩
  let R : ℕ → ℝ → Prop := fun k a => ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
    ‖iteratedFDeriv ℝ k f (s, t)‖ ≤ C * Real.exp (-(a * s))
  have hCnn : ∀ (k : ℕ) (a C s : ℝ) (t : ℝ),
      ‖iteratedFDeriv ℝ k f (s, t)‖ ≤ C * Real.exp (-(a * s)) → 0 ≤ C := by
    intro k a C s t h
    have h0 := (norm_nonneg _).trans h
    by_contra hC
    push_neg at hC
    nlinarith [Real.exp_pos (-(a * s))]
  have hR0 : ∀ k, R k 0 := by
    intro k
    obtain ⟨s₁, h⟩ := hlim k 1 one_pos
    exact ⟨1, s₁, fun s hs t => by simpa using h s hs t⟩
  have hmono : ∀ k a a', R k a → a' ≤ a → R k a' := by
    rintro k a a' ⟨C, s₁, h⟩ ha
    refine ⟨C, max s₁ 0, fun s hs t => ?_⟩
    have hs1 : s₁ ≤ s := le_of_max_le_left hs
    have hs0 : 0 ≤ s := le_of_max_le_right hs
    have hC := hCnn k a C s t (h s hs1 t)
    refine (h s hs1 t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
    nlinarith
  have hint : ∀ j a c, 0 ≤ a → 0 ≤ c → R j a → R (j + 2) c → R (j + 1) ((a + c) / 2) := by
    rintro j a c ha hc ⟨C1, s1, h1⟩ ⟨C2, s2, h2⟩
    have hC1 := hCnn j a C1 s1 0 (h1 s1 le_rfl 0)
    have hC2 := hCnn (j + 2) c C2 s2 0 (h2 s2 le_rfl 0)
    refine ⟨2 * (2 * C1 + C2), max (max s1 s2) (s₀' + 1), fun s hs t => ?_⟩
    have hs1 : s1 ≤ s := le_trans (le_max_left _ _) (le_of_max_le_left hs)
    have hs2 : s2 ≤ s := le_trans (le_max_right _ _) (le_of_max_le_left hs)
    have hs3 : s₀' < s := by linarith [le_of_max_le_right hs]
    have key := norm_iteratedFDeriv_succ_le_of_halfPlane f s₀' hsm j (s, t) hs3
      (C1 * Real.exp (-(a * s))) (C2 * Real.exp (-(c * s))) (Real.exp (-((a - c) / 2 * s)))
      (Real.exp_pos _)
      (by
        rintro ⟨q1, q2⟩ hq
        refine (h1 q1 (hs1.trans hq) q2).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC1)
        simp only at hq
        nlinarith)
      (by
        rintro ⟨q1, q2⟩ hq
        refine (h2 q1 (hs2.trans hq) q2).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC2)
        simp only at hq
        nlinarith)
    refine key.trans (le_of_eq ?_)
    have e1 : Real.exp (-(a * s)) / Real.exp (-((a - c) / 2 * s)) =
        Real.exp (-((a + c) / 2 * s)) := by
      rw [← Real.exp_sub]; congr 1; ring
    have e2 : Real.exp (-(c * s)) * Real.exp (-((a - c) / 2 * s)) =
        Real.exp (-((a + c) / 2 * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc 2 * (2 * (C1 * Real.exp (-(a * s))) / Real.exp (-((a - c) / 2 * s)) +
          C2 * Real.exp (-(c * s)) * Real.exp (-((a - c) / 2 * s)))
        = 2 * (2 * C1 * (Real.exp (-(a * s)) / Real.exp (-((a - c) / 2 * s))) +
          C2 * (Real.exp (-(c * s)) * Real.exp (-((a - c) / 2 * s)))) := by ring
      _ = 2 * (2 * C1 + C2) * Real.exp (-((a + c) / 2 * s)) := by rw [e1, e2]; ring
  intro m
  by_cases hb0 : b ≤ 0
  · exact hmono m 0 b (hR0 m) hb0
  push_neg at hb0
  have hδ : 0 < δ := hb0.trans hb
  let S : ℕ → Set ℝ := fun k => {x | 0 ≤ x ∧ x ≤ δ ∧ R k x}
  let A : ℕ → ℝ := fun k => sSup (S k)
  have hne : ∀ k, (S k).Nonempty := fun k => ⟨0, le_rfl, hδ.le, hR0 k⟩
  have hbdd : ∀ k, BddAbove (S k) := fun k => ⟨δ, fun x hx => hx.2.1⟩
  have hA0 : ∀ k, 0 ≤ A k := fun k => le_csSup (hbdd k) ⟨le_rfl, hδ.le, hR0 k⟩
  have hAδ : ∀ k, A k ≤ δ := fun k => csSup_le (hne k) (fun x hx => hx.2.1)
  have hRA : ∀ k x, x < A k → R k x := by
    intro k x hx
    obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup (hne k) hx
    exact hmono k y x hy.2.2 hxy.le
  have happrox : ∀ k η, 0 < η → ∃ a, 0 ≤ a ∧ a ≤ δ ∧ A k - η ≤ a ∧ R k a := by
    intro k η hη
    by_cases h : A k - η < 0
    · exact ⟨0, le_rfl, hδ.le, h.le, hR0 k⟩
    · push_neg at h
      exact ⟨A k - η, h, by linarith [hAδ k], le_rfl, hRA k _ (by linarith)⟩
  have hconc : ∀ k, A k + A (k + 2) ≤ 2 * A (k + 1) := by
    intro k
    have hη : ∀ η > 0, (A k + A (k + 2)) / 2 ≤ A (k + 1) + η := by
      intro η hη
      obtain ⟨a, ha0, haδ, ha, hRa⟩ := happrox k η hη
      obtain ⟨c, hc0, hcδ, hc, hRc⟩ := happrox (k + 2) η hη
      have hmem : (a + c) / 2 ∈ S (k + 1) :=
        ⟨by positivity, by linarith, hint k a c ha0 hc0 hRa hRc⟩
      have := le_csSup (hbdd (k + 1)) hmem
      linarith
    have := le_of_forall_pos_le_add hη
    linarith
  have hmon := monotone_of_add_le_two_mul_of_bddBelow A 0 hA0 hconc
  have R0δ : R 0 δ := ⟨C, s₀, fun s hs t => by
    rw [norm_iteratedFDeriv_zero]; exact hdec s hs t⟩
  have hA0δ : A 0 = δ := le_antisymm (hAδ 0) (le_csSup (hbdd 0) ⟨hδ.le, le_rfl, R0δ⟩)
  have hlt : b < A m := by
    have := hmon (Nat.zero_le m)
    linarith
  exact hRA m b hlt

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × ℝ → F) (hf : TendstoZeroCInfty f) (δ C s₀ : ℝ)
    (hdec : ∀ s ≥ s₀, ∀ t : ℝ, ‖f (s, t)‖ ≤ C * Real.exp (-(δ * s))) :
    ∀ b < δ, ExpDecayCInfty f b :=
  expDecayCInfty_of_tendstoZeroCInfty_aux f hf δ C s₀ hdec
