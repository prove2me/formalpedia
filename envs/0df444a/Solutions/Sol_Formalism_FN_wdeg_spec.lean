-- Prove2me | solution 1 for Formalism.FN.wdeg_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:25.585507+00:00
-- url     : https://prove2.me/submissions/1ab59b27-dd71-4817-9d89-079142377396

import Definitions.Def_Formalism_SuccessiveMinima_StatementNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Theorems.Thm_Formalism_FN_gNorm_bdd_of_conv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FN
open Filter Topology
variable {K : Type*} [NormedField K]
namespace Formalism.FN
theorem _root_.solution (a : ℕ → K) (r : ℝ) (hr : 0 < r) (h : ConvOn a r) (ha : a ≠ 0) :
    ‖a (wdeg a r)‖ * r ^ (wdeg a r) = gNorm a r ∧ 0 < gNorm a r := by
  set f : ℕ → ℝ := fun k => ‖a k‖ * r ^ k with hf
  obtain ⟨k0, hk0⟩ : ∃ k0, a k0 ≠ 0 := by
    by_contra hc; push Not at hc; exact ha (funext hc)
  have fpos : 0 < f k0 := by simp only [hf]; positivity
  have ev : ∀ᶠ k in atTop, f k < f k0 := (h : Tendsto f atTop (𝓝 0)).eventually (gt_mem_nhds fpos)
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 ev
  set M := max M0 (k0 + 1)
  have hM : ∀ k ≥ M, f k < f k0 := fun k hk => hM0 k (le_trans (le_max_left _ _) hk)
  obtain ⟨k1, hk1m, hk1⟩ := Finset.exists_max_image (Finset.range M) f ⟨k0, by simp [M]⟩
  have hall : ∀ k, f k ≤ f k1 := by
    intro k
    by_cases hk : k < M
    · exact hk1 k (by simpa using hk)
    · exact (hM k (by omega)).le.trans (hk1 k0 (by simp [M]))
  have hg : gNorm a r = f k1 :=
    le_antisymm (ciSup_le hall) (le_ciSup (gNorm_bdd_of_conv a r h) k1)
  have hS : {k : ℕ | ‖a k‖ * r ^ k = gNorm a r}.Nonempty := ⟨k1, by simp [hg, f]⟩
  have hB : BddAbove {k : ℕ | ‖a k‖ * r ^ k = gNorm a r} := by
    refine ⟨M, fun k hk => ?_⟩
    by_contra hc; push Not at hc
    have := hM k hc.le
    have e : f k = f k1 := by simpa [hg, f] using hk
    linarith [hall k0]
  refine ⟨Nat.sSup_mem hS hB, ?_⟩
  rw [hg]; exact fpos.trans_le (hall k0)
end Formalism.FN
