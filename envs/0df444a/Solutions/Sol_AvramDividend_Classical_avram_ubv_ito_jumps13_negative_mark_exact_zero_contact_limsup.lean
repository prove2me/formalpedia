-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps13_negative_mark_exact_zero_contact_limsup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:46:29.728952+00:00
-- url     : https://prove2.me/submissions/f5070a27-b9ec-42c9-80ea-afb7992c10ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps13_zero_extension_upper_contact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-! An atom of the negative Levy measure may land exactly at reserve zero. -/
theorem solution
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ v : ℝ, v < 0 → w v = 0)
    (y z : ℝ) (hy : 0 < y) (hz : z < 0) (hcontact : y + z = 0)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, w (u n + z) ≤ w 0 + ε := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ :=
    avram_ubv_ito_jumps13_zero_extension_upper_contact
      w hw0 hwcont hwneg ε hε
  have hlim : Tendsto (fun n : ℕ => u n + z) atTop (nhds (0 : ℝ)) := by
    simpa only [hcontact] using (hu.add (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => z) atTop (nhds z)))
  have hnear : ∀ᶠ n : ℕ in atTop, u n + z ∈ Metric.ball (0 : ℝ) δ :=
    hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hδ)
  filter_upwards [hnear] with n hn
  apply hbound
  simpa [Metric.mem_ball, Real.dist_eq] using hn
