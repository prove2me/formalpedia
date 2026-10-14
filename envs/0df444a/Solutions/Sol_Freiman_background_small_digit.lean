-- Prove2me | solution 1 for Freiman.background_small_digit
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-09T17:14:09.850682+00:00
-- url     : https://prove2.me/submissions/3a96b4c9-aa50-4518-ad2b-944c571ff4f5

import Definitions.Def_Freiman_backgroundWords

/-!
Proof of `Freiman.background_small_digit`:
if the central digit satisfies `a i ≤ 2`, then `localValue a i < 4`.

The argument is that every continued-fraction tail value `cfValue b` is
strictly below `1`, uniformly in `b`.
-/

namespace BackgroundSmallDigitAux

open Freiman

private lemma pnat_one_le_real (b : ℕ+) : (1:ℝ) ≤ ((b : ℕ) : ℝ) := by
  have hb : 1 ≤ (b : ℕ) := b.property
  exact_mod_cast hb

private lemma finiteCF_nonneg (w : List ℕ+) : 0 ≤ finiteCF w := by
  induction w with
  | nil => simp [finiteCF]
  | cons b w ih =>
      simp only [finiteCF]
      have h1 := pnat_one_le_real b
      have hden : 0 < ((b : ℕ) : ℝ) + finiteCF w := by linarith
      exact le_of_lt (div_pos one_pos hden)

private lemma finiteCF_le_one (w : List ℕ+) : finiteCF w ≤ 1 := by
  induction w with
  | nil => simp [finiteCF]
  | cons b w ih =>
      simp only [finiteCF]
      have h1 := pnat_one_le_real b
      have h2 := finiteCF_nonneg w
      have hden : (0:ℝ) < ((b : ℕ) : ℝ) + finiteCF w := by linarith
      rw [div_le_one hden]
      linarith

private lemma finiteCF_cons_lower (b : ℕ+) (w : List ℕ+) :
    1 / (((b : ℕ) : ℝ) + 1) ≤ finiteCF (b :: w) := by
  simp only [finiteCF]
  have h1 := pnat_one_le_real b
  have h2 := finiteCF_nonneg w
  have h3 := finiteCF_le_one w
  apply one_div_le_one_div_of_le
  · linarith
  · linarith

private lemma range_map_two (b : ℕ → ℕ+) (k : ℕ) :
    (List.range (k + 2)).map b
      = b 0 :: b 1 :: ((List.range k).map (fun j => b (j + 2))) := by
  simp [List.range_succ_eq_map, List.map_map, Function.comp_def]

private noncomputable def cfBound (b : ℕ → ℕ+) : ℝ :=
  1 / (1 + 1 / (((b 1 : ℕ) : ℝ) + 1))

private lemma cfBound_pos (b : ℕ → ℕ+) : 0 < cfBound b := by
  have h1 := pnat_one_le_real (b 1)
  unfold cfBound
  positivity

private lemma cfBound_lt_one (b : ℕ → ℕ+) : cfBound b < 1 := by
  have h1 := pnat_one_le_real (b 1)
  have hpos : 0 < 1 / (((b 1 : ℕ) : ℝ) + 1) := by positivity
  unfold cfBound
  rw [div_lt_one (by linarith)]
  linarith

private lemma cfConvergent_le_bound (b : ℕ → ℕ+) (k : ℕ) :
    cfConvergent b (k + 2) ≤ cfBound b := by
  unfold cfConvergent cfBound
  rw [range_map_two]
  simp only [finiteCF]
  have hlow := finiteCF_cons_lower (b 1) ((List.range k).map (fun j => b (j + 2)))
  have hb0 := pnat_one_le_real (b 0)
  have hb1 := pnat_one_le_real (b 1)
  have hpos : 0 < 1 / (((b 1 : ℕ) : ℝ) + 1) := by positivity
  simp only [finiteCF] at hlow
  apply one_div_le_one_div_of_le
  · linarith
  · linarith

lemma cfValue_lt_one (b : ℕ → ℕ+) : cfValue b < 1 := by
  have hbound : ∀ x ∈ Set.range (fun n : ℕ => cfConvergent b (2 * n)), x ≤ cfBound b := by
    rintro x ⟨n, rfl⟩
    cases n with
    | zero =>
        show cfConvergent b (2 * 0) ≤ cfBound b
        simpa [cfConvergent, finiteCF] using le_of_lt (cfBound_pos b)
    | succ m =>
        show cfConvergent b (2 * (m + 1)) ≤ cfBound b
        have h : 2 * (m + 1) = 2 * m + 2 := by ring
        rw [h]
        exact cfConvergent_le_bound b (2 * m)
  have hle : cfValue b ≤ cfBound b :=
    Real.sSup_le hbound (le_of_lt (cfBound_pos b))
  exact lt_of_le_of_lt hle (cfBound_lt_one b)

end BackgroundSmallDigitAux

theorem solution (a : ℤ → ℕ+) (i : ℤ) (hi : (a i : ℕ) ≤ 2) :
    Freiman.localValue a i < 4 := by
  unfold Freiman.localValue
  have h1 := BackgroundSmallDigitAux.cfValue_lt_one (fun n : ℕ => a (i - (n : ℤ) - 1))
  have h2 := BackgroundSmallDigitAux.cfValue_lt_one (fun n : ℕ => a (i + (n : ℤ) + 1))
  have ha : ((a i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hi
  linarith
