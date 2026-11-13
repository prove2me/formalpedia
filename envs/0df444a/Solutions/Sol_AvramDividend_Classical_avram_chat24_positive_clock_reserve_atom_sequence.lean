-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_positive_clock_reserve_atom_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:19:37.523644+00:00
-- url     : https://prove2.me/submissions/1a038709-5e04-4304-86c8-2aa1e2435fca

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_chat24_monotone_envelope_common_left_limit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem solution
    (f d : ℝ≥0 → ℝ) (hd : Monotone d) (t : ℝ≥0) (ht : 0 < t)
    (hc : ContinuousWithinAt d (Iic t) t) (l x δ q a b : ℝ)
    (hf : Tendsto f (𝓝[<] t) (nhds l)) (hδ : 0 < δ)
    (hpre : ∀ u, 0 < u → u < t → 0 ≤ x + f u - d u)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (hn : ∀ y, 0 ≤ w y) :
    let Y := Function.leftLim (fun u => x + δ + f u - ⨅ s : Ioi u, d s) t
    let z := f t - Function.leftLim f t
    let J := if Y ∈ Icc a b ∧ z < 0 then
      Real.exp (-(q * (t : ℝ))) * (w (Y + z) - w Y) else 0
    ∃ (u : ℕ → ℝ≥0) (v : ℝ),
      (∀ n, 0 < u n ∧ u n < t) ∧ Monotone u ∧ Tendsto u atTop (nhds t) ∧
      Tendsto (fun n => Real.exp (-(q * (u n : ℝ))) * w (x + f (u n) - d (u n) + δ))
        atTop (nhds v) ∧ 0 ≤ v + J := by

  classical
  let L : ℝ := x + δ + l - d t
  have hLimits :=
    avram_chat24_monotone_envelope_common_left_limit f d hd t l x δ hf hc
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  let Y : ℝ := Function.leftLim
    (fun u : ℝ≥0 => x + δ + f u - ⨅ s : Ioi u, d s) t
  let z : ℝ := f t - Function.leftLim f t
  let J : ℝ := if Y ∈ Icc a b ∧ z < 0 then
    Real.exp (-(q * (t : ℝ))) * (w (Y + z) - w Y) else 0
  have hY : Y = L := leftLim_eq_of_tendsto hLimits.2
  obtain ⟨u, hStrict, hIn, hT⟩ :=
    exists_seq_strictMono_tendsto' ht
  have hWithin : Tendsto u atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hT, Filter.Eventually.of_forall (fun n => (hIn n).2)⟩
  have hArg : Tendsto
      (fun n : ℕ => x + f (u n) - d (u n) + δ)
      atTop (nhds L) := by
    have hIdent :
        (fun n : ℕ => x + f (u n) - d (u n) + δ) =
          (fun n : ℕ => x + δ + f (u n) - d (u n)) := by
      funext n
      ring
    rw [hIdent]
    exact hLimits.1.comp hWithin
  have hArgPos (n : ℕ) :
      0 ≤ x + f (u n) - d (u n) + δ := by
    have hp := hpre (u n) (hIn n).1 (hIn n).2
    linarith
  have hLpos : 0 ≤ L :=
    ge_of_tendsto hArg (Filter.Eventually.of_forall hArgPos)
  have hWithinL : Tendsto
      (fun n : ℕ => x + f (u n) - d (u n) + δ)
      atTop (𝓝[Ici 0] L) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hArg, Filter.Eventually.of_forall hArgPos⟩
  have hW : Tendsto
      (fun n : ℕ => w (x + f (u n) - d (u n) + δ))
      atTop (nhds (w L)) :=
    (hw L hLpos).tendsto.comp hWithinL
  have hExp : Tendsto
      (fun n : ℕ => Real.exp (-(q * (u n : ℝ))))
      atTop (nhds (Real.exp (-(q * (t : ℝ))))) := by
    have hCont : Continuous
        (fun r : ℝ≥0 => Real.exp (-(q * (r : ℝ)))) := by fun_prop
    exact (hCont.tendsto t).comp hT
  let v : ℝ := Real.exp (-(q * (t : ℝ))) * w L
  refine ⟨u, v, fun n => hIn n, hStrict.monotone, hT, ?_, ?_⟩
  · exact hExp.mul hW
  · change 0 ≤ Real.exp (-(q * (t : ℝ))) * w L +
      (if Y ∈ Icc a b ∧ z < 0 then
         Real.exp (-(q * (t : ℝ))) * (w (Y + z) - w Y) else 0)
    rw [hY]
    by_cases hcase : L ∈ Icc a b ∧ z < 0
    · simp only [if_pos hcase]
      have he : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
        (Real.exp_pos _).le
      nlinarith [mul_nonneg he (hn (L + z))]
    · simpa only [if_neg hcase, add_zero] using
        (mul_nonneg (Real.exp_pos _).le (hn L))

end
