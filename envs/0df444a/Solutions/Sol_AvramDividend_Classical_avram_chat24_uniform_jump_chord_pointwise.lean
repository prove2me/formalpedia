-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_uniform_jump_chord_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:44:15.855614+00:00
-- url     : https://prove2.me/submissions/7c59cedd-654b-494a-b3c8-09fcfb6245c5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_mesh_cell_geometry
import Theorems.Thm_AvramDividend_Classical_avram_chat24_strict_mono_cell_selector
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_cell_path_increment_limits
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section

theorem solution
    (f K : ℝ≥0 → ℝ) (v d a b q y : ℝ) (B t : ℝ≥0)
    (hB : 0 < B) (ht : 0 < t) (htB : t ≤ B) (ha : 0 < a)
    (hfr : ContinuousWithinAt f (Ici t) t)
    (hfl : ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hK : Monotone K)
    (hband : ∀ s : ℝ≥0, s ≤ B → v + f s - K s ∈ Icc a b)
    (hy : y ∈ Icc a b)
    (hpre : Tendsto (fun s => v + f s - K s) (𝓝[<] t) (nhds y))
    (hjump : f t - Function.leftLim f t < 0)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0)) (n0 : ℕ) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let V : ℕ → ℕ → ℝ := fun n i => v + f (u n i) - K (u n i)
    let m : ℕ → ℕ → ℝ := fun n i => d * h n - (f (u n (i + 1)) - f (u n i))
    let F : ℕ → ℝ := fun n => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < t ∧ t ≤ u n (i + 1) then
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            ((w (V n i - m n i) - w (V n i)) / m n i) *
              (-(f t - Function.leftLim f t)) else 0
      else 0
    Tendsto F atTop (nhds (Real.exp (-(q * (t : ℝ))) *
      (w (y + (f t - Function.leftLim f t)) - w y))) := by
  classical
  intro u h V m F
  let δ : ℝ := f t - Function.leftLim f t
  have hδ : δ < 0 := hjump
  change Tendsto F atTop (nhds (Real.exp (-(q * (t : ℝ))) * (w (y + δ) - w y)))
  have geom := AvramDividend.Classical.avram_chat24_uniform_mesh_cell_geometry B hB
  have hend (n : ℕ) : u n (n + 1) = B := by
    dsimp only [u]
    exact mul_div_cancel_right₀ _ (by positivity)
  have hs (n : ℕ) := AvramDividend.Classical.avram_chat24_strict_mono_cell_selector
    (u n) (geom.1 n) (n + 1) t
    (by simpa only [u, Nat.cast_zero, mul_zero, zero_div] using ht)
    (by simpa only [hend] using htB)
  choose k hk using hs
  have hkr (n : ℕ) : k n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (hk n).1
  have hcell (n : ℕ) : u n (k n) < t ∧ t ≤ u n (k n + 1) :=
    ⟨(hk n).2.1, (hk n).2.2.1⟩
  have hp := AvramDividend.Classical.avram_chat24_uniform_cell_path_increment_limits
    f (fun s => v + f s - K s) d y B t hB ht k hkr hcell hfr hfl hpre
  have hV : Tendsto (fun n => V n (k n)) atTop (nhds y) := hp.2.2.1
  have hmass : Function.leftLim f t - f t = -δ := by dsimp only [δ]; ring
  have hm : Tendsto (fun n => m n (k n)) atTop (nhds (-δ)) := by
    rw [← hmass]
    exact hp.2.2.2
  have hVm : Tendsto (fun n => V n (k n) - m n (k n)) atTop (nhds (y + δ)) := by
    have he : y - (-δ) = y + δ := by ring
    rw [← he]
    exact hV.sub hm
  have hsafe : Tendsto (fun n => V n (k n) - m n (k n) + d * h n)
      atTop (nhds (y + δ)) := by
    have he : y - (-δ) + d * 0 = y + δ := by ring
    rw [← he]
    exact (hV.sub hm).add ((tendsto_const_nhds : Tendsto (fun _ : ℕ => d)
      atTop (nhds d)).mul hp.2.1)
  have hsafeBound (n : ℕ) : a ≤ V n (k n) - m n (k n) + d * h n := by
    have hb := (hband (u n (k n + 1)) (geom.2.2 n (k n) (hkr n)).2.1).1
    have hmono := hK ((geom.1 n).monotone (show k n ≤ k n + 1 by omega))
    dsimp only [V, m]
    linarith
  have hpost : a ≤ y + δ := by
    have hneg : -(y + δ) ≤ -a := le_of_tendsto' hsafe.neg
      (fun n => by linarith [hsafeBound n])
    linarith
  have hwy := (ContDiffOn.contDiffAt hw (Ioi_mem_nhds (lt_of_lt_of_le ha hy.1))).continuousAt
  have hwp := (ContDiffOn.contDiffAt hw (Ioi_mem_nhds (lt_of_lt_of_le ha hpost))).continuousAt
  have hquot := ((hwp.tendsto.comp hVm).sub (hwy.tendsto.comp hV)).div hm
    (neg_ne_zero.mpr hδ.ne)
  have hupp : Tendsto (fun n => (u n (k n + 1) : ℝ)) atTop (nhds (t : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (hp.1.mono_right nhdsWithin_le_nhds)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hupp.const_mul q).neg
  have hfinal := (hexp.mul hquot).mul_const (-δ)
  have hvalue : (Real.exp (-(q * (t : ℝ))) * ((w (y + δ) - w y) / (-δ))) * (-δ) =
      Real.exp (-(q * (t : ℝ))) * (w (y + δ) - w y) := by
    rw [mul_assoc, div_mul_cancel₀ _ (neg_ne_zero.mpr hδ.ne)]
  rw [hvalue] at hfinal
  have heq : F =ᶠ[atTop] (fun n => Real.exp (-(q * (u n (k n + 1) : ℝ))) *
      ((w (V n (k n) - m n (k n)) - w (V n (k n))) / m n (k n)) * (-δ)) := by
    filter_upwards [eventually_ge_atTop n0] with n hn
    dsimp only [F]
    rw [if_pos hn, Finset.sum_eq_single (k n)]
    · rw [if_pos (hcell n)]
    · intro j hj hjne
      exact if_neg (fun hc => hjne ((hk n).2.2.2 j hc.1 hc.2))
    · intro hnot
      exact (hnot (hkr n)).elim
  exact (tendsto_congr' heq).2 hfinal
