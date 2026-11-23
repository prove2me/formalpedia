-- Prove2me | solution 1 for Formalism.logDerivZeroFree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:10.789058+00:00
-- url     : https://prove2.me/submissions/4f9f1fa3-1c1a-4679-8622-9e756e7ef298

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution : LogDerivZeroFree := by
  intro P q U hU hP ⟨z, hz⟩ hq hPq s hs hPs
  have hPa : ∀ w, AnalyticAt ℂ P w := fun w => hP.analyticAt w
  have hqa : AnalyticAt ℂ q s := hq.analyticAt (hU.mem_nhds hs)

  have hne : analyticOrderAt P s ≠ ⊤ := by
    rw [Ne, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s hPa]
    intro h
    exact hz (by simp [h])
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne

  have hn0 : n ≠ 0 := by
    rintro rfl
    have : analyticOrderAt P s = 0 := by rw [← hn]; rfl
    rcases analyticOrderAt_eq_zero.mp this with h | h
    · exact h (hPa s)
    · exact h hPs
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hord : analyticOrderAt P s = (m : ℕ∞) + 1 := by rw [← hn]; push_cast; rfl
  have hd : analyticOrderAt (deriv P) s = m := analyticOrderAt_deriv_of_pos (hPa s) hord

  have hev : deriv P =ᶠ[𝓝 s] q * P :=
    Filter.eventually_of_mem (hU.mem_nhds hs) (fun w hw => by simpa using hPq w hw)
  have hmul : analyticOrderAt (deriv P) s = analyticOrderAt q s + ((m : ℕ∞) + 1) := by
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hqa (hPa s), hord]
  rw [hd] at hmul
  have hle : (m : ℕ∞) + 1 ≤ (m : ℕ∞) := by
    calc (m : ℕ∞) + 1 ≤ analyticOrderAt q s + ((m : ℕ∞) + 1) := le_add_self
      _ = m := hmul.symm
  exact absurd hle (by
    rw [not_le]
    exact ENat.lt_add_one_iff (ENat.natCast_ne_top m) |>.mpr le_rfl)
end Formalism
