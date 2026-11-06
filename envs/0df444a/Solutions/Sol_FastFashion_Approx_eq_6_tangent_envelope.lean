-- Prove2me | solution 1 for FastFashion.Approx.eq_6_tangent_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:24:23.334315+00:00
-- url     : https://prove2.me/submissions/c6bc6fad-17cb-4bce-a977-10b06dc26f84

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_FastFashion_Approx_Tangents
import Theorems.Thm_FastFashion_Approx_eq_4_5_single_size
import Theorems.Thm_FastFashion_Approx_tangent_slopes_pos_decreasing

open MeasureTheory ProbabilityTheory

namespace FFEq6

/-- concavity: a partial-sum sequence with antitone increments lies below each of its tangents -/
lemma partial_sum_le_tangent (f : ℕ → ℝ) (hf : Antitone f) (q i : ℕ) :
    ∑ k ∈ Finset.range q, f k ≤ f i * ((q : ℝ) - i) + ∑ k ∈ Finset.range i, f k := by
  rcases le_total i q with hiq | hqi
  · rw [← Finset.sum_range_add_sum_Ico f hiq]
    have h1 : ∑ k ∈ Finset.Ico i q, f k ≤ (Finset.Ico i q).card • f i :=
      Finset.sum_le_card_nsmul _ _ _ (fun k hk => hf (Finset.mem_Ico.mp hk).1)
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hiq] at h1
    linarith
  · rw [← Finset.sum_range_add_sum_Ico f hqi]
    have h1 : (Finset.Ico q i).card • f i ≤ ∑ k ∈ Finset.Ico q i, f k :=
      Finset.card_nsmul_le_sum _ _ _ (fun k hk => hf (Finset.mem_Ico.mp hk).2.le)
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hqi] at h1
    nlinarith

/-- the truncation map `x ↦ x ∧ T` from `WithTop ℝ` to `ℝ` -/
noncomputable def trunc (T : ℝ) : WithTop ℝ → ℝ
  | ⊤ => T
  | (t : ℝ) => min t T

lemma trunc_le {T : ℝ} (x : WithTop ℝ) : trunc T x ≤ T := by
  induction x using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe a => exact min_le_right _ _

lemma hA_le_T {S Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : S → ℝ → Ω → ℕ) (T : ℝ) (hT : 0 < T) (A : Finset S) (q : S → ℕ) :
    FastFashion.Structure.hA N P T A q ≤ T := by
  unfold FastFashion.Structure.hA
  by_cases hint : Integrable (fun ω => FastFashion.Structure.stopMin N A q T ω) P
  · calc ∫ ω, FastFashion.Structure.stopMin N A q T ω ∂P ≤ ∫ _ω, T ∂P := by
          refine integral_mono hint (integrable_const T) (fun ω => ?_)
          have : FastFashion.Structure.stopMin N A q T ω = trunc T
              (FastFashion.Structure.tauMin N A q ω) := by
            unfold FastFashion.Structure.stopMin trunc; rfl
          rw [this]; exact trunc_le _
      _ = T := by simp
  · rw [integral_undef hint]; exact hT.le

end FFEq6

open FFEq6 FastFashion.Approx in
theorem solution {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (s : S) (q : S → ℕ) :
    IsLeast (Set.range fun i : WithTop ℕ => tangent (lam s) T i (q s : ℝ)) (FastFashion.Structure.hA N P T {s} q) := by
  have hb : FastFashion.Structure.hA N P T {s} q = b (lam s) T (q s) := by
    rw [(eq_4_5_single_size P lam N hN hlam T hT s q).2]
    unfold b a
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) (fun k _ => ?_)
    rw [show 1 + k = k + 1 by ring, Nat.add_sub_cancel]
  have hanti : Antitone (a (lam s) T) :=
    antitone_nat_of_succ_le (fun k => (tangent_slopes_pos_decreasing (lam s) T (hlam s) hT k).2.le)
  refine ⟨⟨((q s : ℕ) : WithTop ℕ), ?_⟩, ?_⟩
  · show a (lam s) T (q s) * ((q s : ℝ) - ((q s : ℕ) : ℝ)) + b (lam s) T (q s) = _
    rw [sub_self, mul_zero, zero_add]
    exact hb.symm
  · rintro _ ⟨i, rfl⟩
    induction i using WithTop.recTopCoe with
    | top => exact hA_le_T P N T hT {s} q
    | coe n =>
      simp only [tangent]
      rw [hb]
      exact partial_sum_le_tangent _ hanti (q s) n
