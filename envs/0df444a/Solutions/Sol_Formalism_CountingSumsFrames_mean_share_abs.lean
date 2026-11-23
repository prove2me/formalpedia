-- Prove2me | solution 1 for Formalism.CountingSumsFrames.mean_share_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:54.959239+00:00
-- url     : https://prove2.me/submissions/a895c09a-afbd-419b-8a3f-e312dcea0716

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {α β R : Type} [Fintype β] [Fintype R] (W : Finset α) (compat : β → α → Prop)
    [∀ ρ aa, Decidable (compat ρ aa)] (ny : ℕ) (hny : 0 < ny)
    (hcount : ∀ aa ∈ W, ((univ : Finset β).filter (fun ρ => compat ρ aa)).card = ny)
    (bad rk : β → R → α → ℝ) (Mlo Mhi : R → ℝ) (eps K : ℝ) (hW : W.Nonempty) (heps : 0 ≤ eps) (hK : 0 ≤ K)
    (hbad : ∀ ρ q aa, 0 ≤ bad ρ q aa) (hMlo : ∀ q, 0 ≤ Mlo q) (hMhi : ∀ q, Mhi q ≤ K * Mlo q)
    (hrk : ∀ ρ q, ∀ aa ∈ W, compat ρ aa → Mlo q / 2 ≤ rk ρ q aa)
    (hsum : ∀ ρ q, ∑ aa ∈ W.filter (fun aa => compat ρ aa), bad ρ q aa ≤
      eps * ((W.filter (fun aa => compat ρ aa)).card : ℝ) * Mhi q) :
    (∑ aa ∈ W, (∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, bad ρ q aa) /
      (∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, rk ρ q aa)) / (W.card : ℝ) ≤ 2 * K * eps := by
  classical
  have hM0 : 0 ≤ ∑ q, Mlo q := Finset.sum_nonneg fun q _ => hMlo q
  have hWc : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hnyR : (0 : ℝ) < ny := by exact_mod_cast hny
  set N : α → ℝ := fun aa => ∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, bad ρ q aa with hN
  set D : α → ℝ := fun aa => ∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, rk ρ q aa with hD
  show (∑ aa ∈ W, N aa / D aa) / (W.card : ℝ) ≤ 2 * K * eps
  have hN0 : ∀ aa, 0 ≤ N aa := fun aa =>
    Finset.sum_nonneg fun ρ _ => Finset.sum_nonneg fun q _ => hbad ρ q aa
  have hDlow : ∀ aa ∈ W, (ny : ℝ) * (∑ q, Mlo q) / 2 ≤ D aa := by
    intro aa haa
    calc (ny : ℝ) * (∑ q, Mlo q) / 2 = ∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, Mlo q / 2 := by
          rw [Finset.sum_const, hcount aa haa, nsmul_eq_mul, ← Finset.sum_div]
          ring
      _ ≤ D aa := Finset.sum_le_sum fun ρ hρ => Finset.sum_le_sum fun q _ =>
          hrk ρ q aa haa (Finset.mem_filter.mp hρ).2
  have hcard : ∑ ρ : β, ((W.filter (fun aa => compat ρ aa)).card : ℝ) = (W.card : ℝ) * ny := by
    have e : ∑ ρ : β, ((W.filter (fun aa => compat ρ aa)).card : ℝ) =
        ∑ aa ∈ W, (((univ : Finset β).filter (fun ρ => compat ρ aa)).card : ℝ) := by
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact Finset.sum_comm' (t' := W) (s' := fun aa => (univ : Finset β).filter fun ρ => compat ρ aa)
        (fun ρ aa => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto)
    rw [e, Finset.sum_congr rfl (fun aa haa => by rw [hcount aa haa]), Finset.sum_const, nsmul_eq_mul]
  have hNsum : ∑ aa ∈ W, N aa ≤ eps * K * (∑ q, Mlo q) * ((W.card : ℝ) * ny) := by
    have hsw : ∑ aa ∈ W, N aa =
        ∑ ρ : β, ∑ q, ∑ aa ∈ W.filter (fun aa => compat ρ aa), bad ρ q aa := by
      simp only [hN]
      rw [Finset.sum_comm' (t' := univ) (s' := fun ρ => W.filter fun aa => compat ρ aa)
        (fun aa ρ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto)]
      exact Finset.sum_congr rfl fun ρ _ => Finset.sum_comm
    rw [hsw, ← hcard, Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ _ => ?_
    calc ∑ q, ∑ aa ∈ W.filter (fun aa => compat ρ aa), bad ρ q aa
        ≤ ∑ q, eps * ((W.filter (fun aa => compat ρ aa)).card : ℝ) * Mhi q :=
          Finset.sum_le_sum fun q _ => hsum ρ q
      _ ≤ ∑ q, eps * ((W.filter (fun aa => compat ρ aa)).card : ℝ) * (K * Mlo q) :=
          Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hMhi q) (by positivity)
      _ = eps * K * (∑ q, Mlo q) * ((W.filter (fun aa => compat ρ aa)).card : ℝ) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun q _ => by ring
  rcases hM0.lt_or_eq with hMpos | hMz
  · have hMne : (∑ q, Mlo q) ≠ 0 := hMpos.ne'
    have hnyne : (ny : ℝ) ≠ 0 := hnyR.ne'
    have hper : ∀ aa ∈ W, N aa / D aa ≤ N aa * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := by
      intro aa haa
      have hpos : 0 < (ny : ℝ) * (∑ q, Mlo q) / 2 := by positivity
      calc N aa / D aa ≤ N aa / ((ny : ℝ) * (∑ q, Mlo q) / 2) :=
            div_le_div_of_nonneg_left (hN0 aa) hpos (hDlow aa haa)
        _ = N aa * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := by rw [div_div_eq_mul_div]
    rw [div_le_iff₀ hWc]
    calc ∑ aa ∈ W, N aa / D aa ≤ ∑ aa ∈ W, N aa * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := Finset.sum_le_sum hper
      _ = (∑ aa ∈ W, N aa) * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := by
          rw [← Finset.sum_div, ← Finset.sum_mul]
      _ ≤ (eps * K * (∑ q, Mlo q) * ((W.card : ℝ) * ny)) * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := by
          gcongr
      _ = 2 * K * eps * W.card := by
          field_simp
  · have hsum0 : ∑ aa ∈ W, N aa = 0 := by
      apply le_antisymm
      · calc ∑ aa ∈ W, N aa ≤ eps * K * (∑ q, Mlo q) * ((W.card : ℝ) * ny) := hNsum
          _ = 0 := by rw [← hMz]; ring
      · exact Finset.sum_nonneg fun aa _ => hN0 aa
    have hz : ∀ aa ∈ W, N aa = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun aa _ => hN0 aa).mp hsum0
    rw [Finset.sum_congr rfl (fun aa haa => by rw [hz aa haa, zero_div]), Finset.sum_const_zero, zero_div]
    positivity
end Formalism.CountingSumsFrames
