-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_piecewise_affine_no_positive_left_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:13:52.955519+00:00
-- url     : https://prove2.me/submissions/33881f30-1db4-4bdd-a666-c5674e723f35

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Nonpositive marks force each forward jump-count increment to decrease
the path's finite-sum component; pass the bound to the left limit. -/
theorem solution
    (x₀ b : ℝ) (T Y : ℕ → ℝ)
    (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (hneg : ∀ n, Y n ≤ 0) :
    ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 =>
        LevyFoundations.piecewisePath x₀ b T Y (s : ℝ))
        (nhdsWithin t (Iio t)) (nhds l) →
      LevyFoundations.piecewisePath x₀ b T Y (t : ℝ) ≤ l := by
  have hcount : Monotone (LevyFoundations.jumpCount T) := by
    intro a c hac
    unfold LevyFoundations.jumpCount
    have hne : {n : ℕ | c < T n}.Nonempty := by
      obtain ⟨n, hn⟩ := (htop.eventually_gt_atTop c).exists
      exact ⟨n, hn⟩
    have hk : c < T (sInf {n : ℕ | c < T n}) := Nat.sInf_mem hne
    exact Nat.sInf_le
      (show sInf {n : ℕ | c < T n} ∈ {n : ℕ | a < T n} from
        lt_of_le_of_lt hac hk)
  intro t l ht hl
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  let f : ℝ≥0 → ℝ := fun s =>
    LevyFoundations.piecewisePath x₀ b T Y (s : ℝ)
  have hbudget (s : ℝ≥0) (hst : s ≤ t) :
      f t ≤ f s + b * ((t : ℝ) - (s : ℝ)) := by
    have hstR : (s : ℝ) ≤ (t : ℝ) := NNReal.coe_le_coe.mpr hst
    have hN := hcount hstR
    have hsub := Finset.range_mono hN
    have hdiff :
        (∑ i ∈ (Finset.range (LevyFoundations.jumpCount T (t : ℝ)) \
          Finset.range (LevyFoundations.jumpCount T (s : ℝ))), Y i) ≤ 0 :=
      Finset.sum_nonpos (by intro i hi; exact hneg i)
    have hsplit := Finset.sum_sdiff (f := Y) hsub
    have hsums :
        (∑ i ∈ Finset.range (LevyFoundations.jumpCount T (t : ℝ)), Y i) ≤
          ∑ i ∈ Finset.range (LevyFoundations.jumpCount T (s : ℝ)), Y i := by
      nlinarith [hdiff, hsplit]
    calc
      f t = x₀ + b * (t : ℝ) +
          ∑ i ∈ Finset.range (LevyFoundations.jumpCount T (t : ℝ)), Y i := rfl
      _ ≤ x₀ + b * (t : ℝ) +
          ∑ i ∈ Finset.range (LevyFoundations.jumpCount T (s : ℝ)), Y i :=
        add_le_add_right hsums _
      _ = f s + b * ((t : ℝ) - (s : ℝ)) := by
        simp only [f, LevyFoundations.piecewisePath]
        ring
  have hcontinuous : Continuous (fun s : ℝ≥0 =>
      b * ((t : ℝ) - (s : ℝ))) := by fun_prop
  have hzero : Tendsto (fun s : ℝ≥0 =>
      b * ((t : ℝ) - (s : ℝ)))
      (𝓝[<] t) (nhds (0 : ℝ)) := by
    have hc0 := (hcontinuous.continuousAt (x := t)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio t))
    simpa using hc0
  have hlimit : Tendsto (fun s : ℝ≥0 =>
      f s + b * ((t : ℝ) - (s : ℝ)))
      (𝓝[<] t) (nhds l) := by
    simpa [f] using hl.add hzero
  have hevent : ∀ᶠ s in 𝓝[<] t,
      f t ≤ f s + b * ((t : ℝ) - (s : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hst
    exact hbudget s hst.le
  exact ge_of_tendsto hlimit hevent
