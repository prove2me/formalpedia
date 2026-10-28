-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:26:28.119906+00:00
-- url     : https://prove2.me/submissions/f97c40d9-0cee-44ce-9056-ac04f8b620dc

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting

open BoundedEntropyGames.ConvRate in
theorem solution {E F : Type*} [Fintype E] [Fintype F] :
    (∀ (pE qE : E → ℝ) (K : E → F → ℝ), IsPMF pE → IsPMF qE → (∀ e, IsPMF (K e)) →
      tv (fun z : E × F => pE z.1 * K z.1 z.2) (fun z => qE z.1 * K z.1 z.2) = tv pE qE) ∧
    (∀ (pE qE : E → ℝ) (K L : E → F → ℝ), IsPMF pE → IsPMF qE → (∀ e, IsPMF (K e)) →
      (∀ e, IsPMF (L e)) →
      tv pE qE ≤ tv (fun z : E × F => pE z.1 * K z.1 z.2) (fun z => qE z.1 * L z.1 z.2)) ∧
    (∀ (pE₁ pE₂ : E → ℝ) (pF₁ qF₂ : F → ℝ), IsPMF pE₁ → IsPMF pE₂ → IsPMF pF₁ → IsPMF qF₂ →
      tv (fun z : E × F => pE₁ z.1 * pF₁ z.2) (fun z => pE₂ z.1 * qF₂ z.2)
        ≤ tv pE₁ pE₂ + tv pF₁ qF₂) := by
  refine ⟨fun pE qE K _ _ hK => ?_, fun pE qE K L _ _ hK hL => ?_,
    fun a c b d _ hc hb _ => ?_⟩
  · unfold tv
    rw [Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    have : ∀ f, |pE e * K e f - qE e * K e f| = |pE e - qE e| * K e f := by
      intro f
      rw [← sub_mul, abs_mul, abs_of_nonneg ((hK e).1 f)]
    simp only [this, ← Finset.mul_sum, (hK e).2, mul_one]
  · unfold tv
    rw [Fintype.sum_prod_type]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine Finset.sum_le_sum fun e _ => ?_
    have h : pE e - qE e = ∑ f, (pE e * K e f - qE e * L e f) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hK e).2, (hL e).2]
      ring
    rw [h]
    exact Finset.abs_sum_le_sum_abs _ _
  · unfold tv
    rw [Fintype.sum_prod_type]
    have hpt : ∀ e f, |a e * b f - c e * d f| ≤ |a e - c e| * b f + c e * |b f - d f| := by
      intro e f
      have e1 : a e * b f - c e * d f = (a e - c e) * b f + c e * (b f - d f) := by ring
      rw [e1]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (hb.1 f), abs_of_nonneg (hc.1 e)]
    have hsum : ∑ e, ∑ f, |a e * b f - c e * d f|
        ≤ ∑ e, |a e - c e| + ∑ f, |b f - d f| := by
      calc ∑ e, ∑ f, |a e * b f - c e * d f|
          ≤ ∑ e, ∑ f, (|a e - c e| * b f + c e * |b f - d f|) :=
            Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ => hpt e f
        _ = ∑ e, |a e - c e| + ∑ f, |b f - d f| := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hb.2, mul_one, ← Finset.sum_mul,
              hc.2, one_mul]
    simp only at hsum ⊢
    linarith
