-- Prove2me | solution 1 for EllsbergLearning.gs_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:55:16.322037+00:00
-- url     : https://prove2.me/submissions/c23cd025-516d-4b95-a1a4-bc9ddb4b0677

import Definitions.Def_EllsbergLearning_Params

open Set

open EllsbergLearning in
theorem solution (p : Params) (hp : p.Valid) (t z : ℝ) :
    p.gs 0 t z = (p.u 0 0 - p.u 0 1) * (1 - p.mUp t z) + p.u 0 1 ∧
      p.gs 1 t z = (p.u 1 1 - p.u 1 0) * p.mLo t z + p.u 1 0 := by
  have hle : p.mLo t z ≤ p.mUp t z := by
    have hφ : 0 < p.phi t z := by unfold Params.phi; exact Real.exp_pos _
    have h0 := hp.mLo0_pos
    have h1 := hp.mLo0_lt_mUp0
    have h2 := hp.mUp0_lt_one
    have ha : p.mLo0 / (1 - p.mLo0) ≤ p.mUp0 / (1 - p.mUp0) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have hA : 0 ≤ p.mLo0 / (1 - p.mLo0) * p.phi t z :=
      mul_nonneg (div_nonneg h0.le (by linarith)) hφ.le
    have hAB : p.mLo0 / (1 - p.mLo0) * p.phi t z ≤ p.mUp0 / (1 - p.mUp0) * p.phi t z :=
      mul_le_mul_of_nonneg_right ha hφ.le
    unfold Params.mLo Params.mUp Params.post
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  constructor
  · unfold Params.gs
    have : IsLeast ((fun m => (1 - m) * p.u 0 0 + m * p.u 0 1) '' Icc (p.mLo t z) (p.mUp t z))
        ((p.u 0 0 - p.u 0 1) * (1 - p.mUp t z) + p.u 0 1) := by
      refine ⟨⟨p.mUp t z, ⟨hle, le_rfl⟩, by ring⟩, ?_⟩
      rintro _ ⟨m, ⟨_, hm2⟩, rfl⟩
      nlinarith [hp.u01_lt_u00]
    exact this.csInf_eq
  · unfold Params.gs
    have : IsLeast ((fun m => (1 - m) * p.u 1 0 + m * p.u 1 1) '' Icc (p.mLo t z) (p.mUp t z))
        ((p.u 1 1 - p.u 1 0) * p.mLo t z + p.u 1 0) := by
      refine ⟨⟨p.mLo t z, ⟨le_rfl, hle⟩, by ring⟩, ?_⟩
      rintro _ ⟨m, ⟨hm1, _⟩, rfl⟩
      nlinarith [hp.u10_lt_u11]
    exact this.csInf_eq
