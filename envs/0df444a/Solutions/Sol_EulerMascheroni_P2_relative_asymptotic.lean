-- Prove2me | solution 1 for EulerMascheroni.P2.relative_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:03:01.930981+00:00
-- url     : https://prove2.me/submissions/1a30c56a-d9b8-491c-9cde-a089a90e32a6

import Definitions.Def_eulerMascheroni_p2Approximation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Filter Topology
open EulerMascheroni.P2

private lemma oscillatory_transfer (s u v : ℝ) (hs : |s| ≤ 1) (hu : |u| ≤ 1/2) :
    |(s+v)/(1+u)-s| ≤ 2 * (|v|+|u|) := by
  have hu0 : (1/2 : ℝ) ≤ 1+u := by
    have := (abs_le.mp hu).1
    linarith
  have hd : 0 < 1+u := by linarith
  have heq : (s+v)/(1+u)-s = (v-u*s)/(1+u) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hnum : |v-u*s| ≤ |v|+|u| := by
    calc
      |v-u*s| ≤ |v|+|u*s| := by simpa using abs_sub_le v 0 (u*s)
      _ = |v|+|u| * |s| := by rw [abs_mul]
      _ ≤ |v|+|u| := by nlinarith [abs_nonneg u]
  nlinarith [abs_nonneg u, abs_nonneg v]


private lemma models_pos (n : ℕ) : 0 < qModel (n+1) ∧ 0 < fModel (n+1) := by
  have hs : 0 < scale (n+1) := by unfold scale; positivity
  constructor
  · unfold qModel; positivity
  · unfold fModel; positivity

/-- The saddle limits imply a relative-error expansion with an additive o(1).
The saddle limits remain explicit hypotheses, not silently asserted facts. -/
theorem solution (h : SaddleLimits) :
    ∃ w : ℕ → ℝ, Tendsto w atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        Real.eulerMascheroniConstant - (P (n+1) : ℝ) / (Q (n+1) : ℝ) =
          (fModel (n+1) / qModel (n+1)) * (Real.sin (phase (n+1)) + w n) := by
  let u : ℕ → ℝ := fun n => (Q (n+1) : ℝ) / qModel (n+1) - 1
  let v : ℕ → ℝ := fun n => F (n+1) / fModel (n+1) - Real.sin (phase (n+1))
  let w : ℕ → ℝ := fun n =>
    (Real.sin (phase (n+1)) + v n) / (1+u n) - Real.sin (phase (n+1))
  have hu : Tendsto u atTop (nhds 0) := h.1
  have hv : Tendsto v atTop (nhds 0) := h.2
  have heu : ∀ᶠ n in atTop, |u n| ≤ 1/2 := by
    have hau : Tendsto (fun n => |u n|) atTop (nhds 0) := by simpa using hu.abs
    have hh := hau.eventually (gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))
    exact hh.mono (fun n hn => le_of_lt (by simpa using hn))
  have hw : Tendsto w atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun n => 2 * (|v n| + |u n|))
    · filter_upwards [heu] with n hn
      exact oscillatory_transfer _ _ _ (Real.abs_sin_le_one _) hn
    · simpa using (hv.abs.add hu.abs).const_mul 2
  refine ⟨w, hw, ?_⟩
  filter_upwards [heu] with n hn
  have hqp := (models_pos n).1.ne'
  have hfp := (models_pos n).2.ne'
  have hd : 1 + u n ≠ 0 := by
    have := (abs_le.mp hn).1
    linarith
  have hQ : (Q (n+1) : ℝ) ≠ 0 := by
    intro hh
    apply hd
    simp [u, hh]
  have hb : 1 + u n = (Q (n+1) : ℝ) / qModel (n+1) := by dsimp [u]; ring
  have hvn : Real.sin (phase (n+1)) + v n = F (n+1) / fModel (n+1) := by
    dsimp [v]; ring
  have hwn : Real.sin (phase (n+1)) + w n =
      (F (n+1) / fModel (n+1)) / ((Q (n+1) : ℝ) / qModel (n+1)) := by
    dsimp [w]
    rw [hb, hvn]
    ring
  rw [hwn]
  unfold F
  field_simp [hQ, hqp, hfp]
  <;> ring

#print axioms solution
