-- Prove2me | solution 3 for ConvexOptAlg.SVRG.theorem_6_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:31:22.964687+00:00
-- url     : https://prove2.me/submissions/236bc68b-b7ed-4b83-be03-14aa7c0107c9

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Theorems.Thm_ConvexOptAlg_SVRG_eq_6_1

-- carved verbatim out of submission 5cff3f1a-262b-4e42-b670-aa35e51700e7, lines 510-561

section
set_option autoImplicit false
open ConvexOptAlg.SVRG

theorem sum_snoc {X : Type*} [Fintype X] (s : ℕ) (F : (Fin (s + 1) → X) → ℝ) :
    ∑ idx, F idx = ∑ r : Fin s → X, ∑ a : X, F (Fin.snoc r a) := by
  rw [← Fintype.sum_prod_type']
  let e : (Fin s → X) × X ≃ (Fin (s + 1) → X) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun idx => (fun j => idx j.castSucc, idx (Fin.last s))
      left_inv := by
        rintro ⟨r, a⟩
        simp
      right_inv := by
        intro idx
        exact Fin.snoc_init_self idx }
  exact (Fintype.sum_equiv e _ _ (fun p => rfl)).symm

theorem mean_snoc {X : Type*} [Fintype X] (s : ℕ) (F : (Fin (s + 1) → X) → ℝ) :
    uniformMean F = uniformMean (fun r : Fin s → X => uniformMean (fun a : X => F (Fin.snoc r a))) := by
  unfold uniformMean
  rw [sum_snoc, ← Finset.sum_div, div_div]
  congr 1
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  ring

theorem mean_mono {A : Type*} [Fintype A] {g h : A → ℝ} (hgh : ∀ a, g a ≤ h a) :
    uniformMean g ≤ uniformMean h := by
  unfold uniformMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => hgh a) (by positivity)

theorem mean_affine {A : Type*} [Fintype A] [Nonempty A] (c d : ℝ) (g : A → ℝ) :
    uniformMean (fun a => c + d * g a) = c + d * uniformMean g := by
  unfold uniformMean
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem epochOutput_snoc {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y₁ : EuclideanSpace ℝ (Fin n)) (s : ℕ) (r : Fin s → Fin k → Fin m)
    (a : Fin k → Fin m) :
    epochOutput gs η y₁ (s + 1) (Fin.snoc r a) = epochOut gs η k (epochOutput gs η y₁ s r) a := by
  simp [epochOutput]

end

section
set_option autoImplicit false

open ConvexOptAlg.SVRG in open scoped InnerProductSpace in
theorem solution {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (k s : ℕ) (y₁ xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hk : 0 < k) (hs : 1 ≤ s)
    (hα : 0 < α) (hβ : 0 < β)
    (hkexact : (k : ℝ) = 20 * (β / α))
    (hfamily : SmoothConvexFamily fs gs β)
    (hstrong : OnlineConvexOpt.ConvexBasics.StronglyConvexOn
      Set.univ (objective fs) (fullGradient gs) α)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun idx : Fin s → Fin k → Fin m =>
        objective fs (epochOutput gs (1 / (10 * β)) y₁ s idx)) -
        objective fs xstar ≤
      (9 / 10 : ℝ) ^ s * (objective fs y₁ - objective fs xstar) := by
  have : NeZero m := ⟨hm.ne'⟩
  clear hs
  induction s with
  | zero =>
    simp [uniformMean, epochOutput]
  | succ s ih =>
    rw [mean_snoc]
    have key : ∀ r : Fin s → Fin k → Fin m,
        uniformMean (fun a : Fin k → Fin m =>
          objective fs (epochOutput gs (1 / (10 * β)) y₁ (s + 1) (Fin.snoc r a))) ≤
        objective fs xstar + (9 / 10 : ℝ) *
          objective fs (epochOutput gs (1 / (10 * β)) y₁ s r) +
          (9 / 10 : ℝ) * (- objective fs xstar) := by
      intro r
      simp only [epochOutput_snoc]
      have := ConvexOptAlg.SVRG.eq_6_1 fs gs α β k (epochOutput gs (1 / (10 * β)) y₁ s r) xstar
        hm hk hα hβ hkexact hfamily hstrong hmin
      linarith
    have h2 := mean_mono key
    have h3 := mean_affine (objective fs xstar + (9 / 10 : ℝ) * (- objective fs xstar))
      (9 / 10 : ℝ)
      (fun r : Fin s → Fin k → Fin m => objective fs (epochOutput gs (1 / (10 * β)) y₁ s r))
    have h4 : uniformMean (fun r : Fin s → Fin k → Fin m =>
        objective fs xstar + (9 / 10 : ℝ) *
          objective fs (epochOutput gs (1 / (10 * β)) y₁ s r) +
          (9 / 10 : ℝ) * (- objective fs xstar)) =
        objective fs xstar + (9 / 10 : ℝ) * (- objective fs xstar) + (9 / 10 : ℝ) *
          uniformMean (fun r : Fin s → Fin k → Fin m =>
            objective fs (epochOutput gs (1 / (10 * β)) y₁ s r)) := by
      rw [← h3]
      congr 1
      funext r
      ring
    rw [h4] at h2
    rw [pow_succ]
    nlinarith [ih]

end
