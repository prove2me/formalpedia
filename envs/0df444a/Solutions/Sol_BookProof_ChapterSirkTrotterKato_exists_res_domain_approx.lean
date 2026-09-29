-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.exists_res_domain_approx
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:11:25.320718+00:00
-- url     : https://prove2.me/submissions/2ab53c93-668e-4c45-8718-4649f4493276

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.exists_res_domain_approx
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato











noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution (v : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : T.domain, ‖v - T.resCLM 1 (w : H)‖ < ε := by

  obtain ⟨u, hu, hdu⟩ := T.denseDomain.exists_dist_lt v (by positivity : (0:ℝ) < ε / 2)
  obtain ⟨w, hw, hdw⟩ := T.denseDomain.exists_dist_lt (T.shift 1 ⟨u, hu⟩)
    (by positivity : (0:ℝ) < ε / 2)
  refine ⟨⟨w, hw⟩, ?_⟩
  have hures : T.resCLM 1 (T.shift 1 ⟨u, hu⟩) = u := by
    have := T.res_shift (l := 1) one_ne_zero ⟨u, hu⟩
    simpa using congrArg (fun (x : T.domain) => (x : H)) this
  have h1 : ‖u - T.resCLM 1 w‖ ≤ ‖T.shift 1 (⟨u, hu⟩ : T.domain) - w‖ := by
    have := T.norm_resCLM_apply_le 1 (T.shift 1 (⟨u, hu⟩ : T.domain) - w)
    rw [map_sub, hures] at this
    simpa using this
  have h2 : ‖v - u‖ < ε / 2 := by simpa [dist_eq_norm] using hdu
  have h3 : ‖T.shift 1 (⟨u, hu⟩ : T.domain) - w‖ < ε / 2 := by simpa [dist_eq_norm] using hdw
  calc ‖v - T.resCLM 1 w‖ ≤ ‖v - u‖ + ‖u - T.resCLM 1 w‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub v u (T.resCLM 1 w)
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring
