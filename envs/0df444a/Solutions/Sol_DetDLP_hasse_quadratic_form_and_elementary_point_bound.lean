-- Prove2me | solution 1 for DetDLP.hasse_quadratic_form_and_elementary_point_bound
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:03:15.858582+00:00
-- url     : https://prove2.me/submissions/8ca503cc-6d05-4a62-bb8e-662a4125c0c4

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

open DetDLP

private lemma ec_point_x_fiber_le_two {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve (ZMod p)) (x : ZMod p)
    (B : Finset E.toAffine.Point)
    (hB : ∀ P ∈ B, ∃ y h, P = WeierstrassCurve.Affine.Point.some x y h) :
    B.card ≤ 2 := by
  by_cases h0 : B = ∅
  · simp [h0]
  · obtain ⟨P₁, hP₁⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    by_cases h1 : (B.erase P₁) = ∅
    · have hsub : B ⊆ {P₁} := fun P hP => by
        by_cases he : P = P₁
        · simp [he]
        · have : P ∈ B.erase P₁ := Finset.mem_erase.mpr ⟨he, hP⟩
          rw [h1] at this; exact False.elim (Finset.notMem_empty P this)
      calc B.card ≤ ({P₁} : Finset _).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton P₁
        _ ≤ 2 := by omega
    · obtain ⟨P₂, hP₂_er⟩ := Finset.nonempty_iff_ne_empty.mpr h1
      have hne12 : P₂ ≠ P₁ := (Finset.mem_erase.mp hP₂_er).1
      have hP₂ : P₂ ∈ B := (Finset.mem_erase.mp hP₂_er).2
      obtain ⟨y₁, h₁, rfl⟩ := hB P₁ hP₁
      obtain ⟨y₂, h₂, rfl⟩ := hB P₂ hP₂
      have hy_ne12 : y₂ ≠ y₁ := fun heq => hne12 (by subst heq; rfl)
      have heq1 : y₁ ^ 2 + E.a₁ * x * y₁ + E.a₃ * y₁ =
          x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
        simpa using (E.toAffine.equation_iff x y₁).mp h₁.1
      have heq2 : y₂ ^ 2 + E.a₁ * x * y₂ + E.a₃ * y₂ =
          x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
        simpa using (E.toAffine.equation_iff x y₂).mp h₂.1
      have hfac12 : (y₂ - y₁) * (y₂ + y₁ + E.a₁ * x + E.a₃) = 0 := by
        linear_combination heq2 - heq1
      have hsum12 : y₂ + y₁ + E.a₁ * x + E.a₃ = 0 :=
        (mul_eq_zero.mp hfac12).resolve_left (sub_ne_zero.mpr hy_ne12)
      have hsub : B ⊆ {.some x y₁ h₁, .some x y₂ h₂} := by
        intro P₃ hP₃
        obtain ⟨y₃, h₃, rfl⟩ := hB P₃ hP₃
        have heq3 : y₃ ^ 2 + E.a₁ * x * y₃ + E.a₃ * y₃ =
            x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
          simpa using (E.toAffine.equation_iff x y₃).mp h₃.1
        have hfac13 : (y₃ - y₁) * (y₃ + y₁ + E.a₁ * x + E.a₃) = 0 := by
          linear_combination heq3 - heq1
        rcases mul_eq_zero.mp hfac13 with h31 | hsum13
        · have hy31 : y₃ = y₁ := sub_eq_zero.mp h31
          simp [hy31]
        · have hy32 : y₃ = y₂ := by linear_combination hsum13 - hsum12
          simp [hy32]
      calc B.card ≤ ({WeierstrassCurve.Affine.Point.some x y₁ h₁,
            WeierstrassCurve.Affine.Point.some x y₂ h₂} : Finset E.toAffine.Point).card :=
          Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two

private def pointXOpt {p : ℕ} {E : WeierstrassCurve (ZMod p)} :
    E.toAffine.Point → Option (ZMod p)
  | .zero => none
  | .some x _ _ => some x

theorem solution :
    (∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)),
      letI := ecPointFintype E
      1 ≤ Fintype.card E.toAffine.Point ∧ Fintype.card E.toAffine.Point ≤ 2 * p + 1) ∧
    (∀ (p N : ℕ), 0 < p →
      (∀ m n : ℤ, 0 ≤ m ^ 2 * (p : ℤ) - m * n * ((p : ℤ) + 1 - (N : ℤ)) + n ^ 2) →
      ((N : ℤ) - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ) ∧
      |(N : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ)) := by
  constructor
  · intro p _ E
    have hp : p.Prime := Fact.out
    have : NeZero p := ⟨hp.ne_zero⟩
    let _ := ecPointFintype E
    have hpos : 1 ≤ Fintype.card E.toAffine.Point := by
      have : Nonempty E.toAffine.Point := ⟨.zero⟩
      exact Fintype.card_pos
    refine ⟨hpos, ?_⟩
    have hfib : (Finset.univ : Finset E.toAffine.Point).card =
        ∑ o ∈ (Finset.univ : Finset (Option (ZMod p))),
          (Finset.univ.filter fun P : E.toAffine.Point => pointXOpt P = o).card :=
      Finset.card_eq_sum_card_fiberwise (f := pointXOpt)
        (s := (Finset.univ : Finset E.toAffine.Point))
        (t := (Finset.univ : Finset (Option (ZMod p))))
        (fun P _ => Finset.mem_univ (pointXOpt P))
    rw [Fintype.card, hfib, Fintype.sum_option]
    have hnone : (Finset.univ.filter fun P : E.toAffine.Point => pointXOpt P = none) ⊆ {.zero} := by
      intro P hP
      rw [Finset.mem_filter] at hP
      cases P with
      | zero => exact Finset.mem_singleton_self _
      | some x y h =>
        dsimp [pointXOpt] at hP
        cases hP.2
    have hnone_card :
        (Finset.univ.filter fun P : E.toAffine.Point => pointXOpt P = none).card ≤ 1 :=
      le_trans (Finset.card_le_card hnone) (by simp)
    have hsome_card :
        ∑ x : ZMod p,
          (Finset.univ.filter fun P : E.toAffine.Point => pointXOpt P = some x).card ≤
        ∑ _x : ZMod p, 2 := by
      refine Finset.sum_le_sum fun x _ => ?_
      refine ec_point_x_fiber_le_two E x _ fun P hP => ?_
      rw [Finset.mem_filter] at hP
      cases P with
      | zero =>
        dsimp [pointXOpt] at hP
        cases hP.2
      | some x' y h =>
        dsimp [pointXOpt] at hP
        have hx : x' = x := Option.some.inj hP.2
        subst hx
        exact ⟨y, h, rfl⟩
    have hsum2 : (∑ _x : ZMod p, 2) = 2 * p := by
      simp [ZMod.card p, mul_comm]
    omega
  · intro p N hp hQ
    have hinst := hQ ((p : ℤ) + 1 - (N : ℤ)) (2 * (p : ℤ))
    have hid :
        ((p : ℤ) + 1 - (N : ℤ)) ^ 2 * (p : ℤ) -
          ((p : ℤ) + 1 - (N : ℤ)) * (2 * (p : ℤ)) * ((p : ℤ) + 1 - (N : ℤ)) +
          (2 * (p : ℤ)) ^ 2 =
        (p : ℤ) * (4 * (p : ℤ) - ((N : ℤ) - ((p : ℤ) + 1)) ^ 2) := by
      ring
    rw [hid] at hinst
    have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    have hsqZ : ((N : ℤ) - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ) := by
      nlinarith
    refine ⟨hsqZ, ?_⟩
    have hsqR : ((N : ℝ) - ((p : ℝ) + 1)) ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 := by
      have hcast : (((N : ℤ) - ((p : ℤ) + 1)) ^ 2 : ℝ) ≤ (4 * (p : ℤ) : ℝ) := by
        exact_mod_cast hsqZ
      push_cast at hcast
      have hrhs : (2 * Real.sqrt (p : ℝ)) ^ 2 = 4 * (p : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
        ring
      linarith
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsqR (by positivity))
