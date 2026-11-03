-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:16:50.898828+00:00
-- url     : https://prove2.me/submissions/03ea480b-bca0-4f14-8bfd-420f9f9b61b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- The actual original-source local pre/postpayment timing error vanishes on fine,
    pathwise dividend-bounded, locally Lipschitz stopped grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ L * |s - t|)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (hPre : ∀ n i, i < k n →
      x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω ∈ Icc a b)
    (hPost : ∀ n i, i < k n →
      x + X.X (u n (i + 1)) ω - rightLimit D (u n (i + 1)) ω ∈ Icc a b)
    (htotal : ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      rightLimit D (u n (k n)) ω - rightLimit D (u n 0) ω ≤ B)
    (hmesh0 : Tendsto m atTop (𝓝 0)) :
    Tendsto (fun n =>
      ∑ i ∈ Finset.range (k n),
        (Real.exp (-(q * (u n i : ℝ))) -
          Real.exp (-(q * (u n (i + 1) : ℝ)))) *
          |w (x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω) -
            w (x + X.X (u n (i + 1)) ω - rightLimit D (u n (i + 1)) ω)|)
      atTop (𝓝 0) := by
  rcases htotal with ⟨B, hB0, hB⟩
  let F : ℕ → ℝ := fun n =>
    ∑ i ∈ Finset.range (k n),
      (Real.exp (-(q * (u n i : ℝ))) -
        Real.exp (-(q * (u n (i + 1) : ℝ)))) *
        |w (x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω) -
          w (x + X.X (u n (i + 1)) ω - rightLimit D (u n (i + 1)) ω)|
  have hlo : ∀ n, 0 ≤ F n := by
    intro n
    dsimp [F]
    apply Finset.sum_nonneg
    intro i hi
    have hui : u n i ≤ u n (i + 1) := (hu n) (Nat.le_succ i)
    have htime : (u n i : ℝ) ≤ (u n (i + 1) : ℝ) := by
      exact_mod_cast hui
    have hqtime := mul_le_mul_of_nonneg_left htime hq
    have harg : -(q * (u n (i + 1) : ℝ)) ≤ -(q * (u n i : ℝ)) :=
      neg_le_neg hqtime
    have hExp :
        Real.exp (-(q * (u n (i + 1) : ℝ))) ≤
          Real.exp (-(q * (u n i : ℝ))) :=
      Real.exp_le_exp.mpr harg
    exact mul_nonneg (sub_nonneg.mpr hExp) (abs_nonneg _)
  have hhi : ∀ n, F n ≤ q * m n * L * B := by
    intro n
    have hgap :=
      avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
        X x D hD ω q hq w L hL a b hLip
        (u n) (hu n) (k n) (m n) (hm n)
        (hmesh n) (hPre n) (hPost n)
    calc
      F n ≤ q * m n * L *
        (rightLimit D (u n (k n)) ω - rightLimit D (u n 0) ω) := hgap
      _ ≤ q * m n * L * B :=
        mul_le_mul_of_nonneg_left (hB n)
          (mul_nonneg (mul_nonneg hq (hm n)) hL)
  have hqconst : Tendsto (fun _ : ℕ => q) atTop (𝓝 q) :=
    tendsto_const_nhds
  have hLconst : Tendsto (fun _ : ℕ => L) atTop (𝓝 L) :=
    tendsto_const_nhds
  have hBconst : Tendsto (fun _ : ℕ => B) atTop (𝓝 B) :=
    tendsto_const_nhds
  have hupper : Tendsto (fun n => q * m n * L * B) atTop (𝓝 0) := by
    simpa using (((hqconst.mul hmesh0).mul hLconst).mul hBconst)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Eventually.of_forall hlo) (Eventually.of_forall hhi)

