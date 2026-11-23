-- Prove2me | solution 1 for Formalism.FN.unit_eps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:55.148344+00:00
-- url     : https://prove2.me/submissions/daef48b8-d994-4661-b8ac-af25fb42565b

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPUnit
import Theorems.Thm_Formalism_FN_gNorm_bdd_of_conv
import Theorems.Thm_Formalism_FN_wdeg_spec


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
namespace Formalism.FN
theorem _root_.solution {K : Type*} [NormedField K] (b : ℕ → K) (r : ℝ) (hr : 0 < r) (hc : ConvOn b r)
    (hb : b ≠ 0) (hw : wdeg b r = 0) :
    ‖b 0‖ = gNorm b r ∧ 0 < gNorm b r ∧
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ ∀ k, 1 ≤ k → ‖b k‖ * r ^ k ≤ ε * gNorm b r := by
  obtain ⟨h0, hM⟩ := wdeg_spec b r hr hc hb
  rw [hw, pow_zero, mul_one] at h0
  refine ⟨h0, hM, ?_⟩
  have hle : ∀ k, ‖b k‖ * r ^ k ≤ gNorm b r := fun k => le_ciSup (gNorm_bdd_of_conv b r hc) k
  obtain ⟨k0, hk0⟩ := eventually_atTop.1
    ((hc : Tendsto (fun k : ℕ => ‖b k‖ * r ^ k) atTop (𝓝 0)).eventually
      (gt_mem_nhds (half_pos hM)))
  have hlt : ∀ k, 1 ≤ k → ‖b k‖ * r ^ k < gNorm b r := by
    intro k hk
    rcases (hle k).lt_or_eq with h | h
    · exact h
    · exfalso
      have hB : BddAbove {k : ℕ | ‖b k‖ * r ^ k = gNorm b r} := by
        refine ⟨k0, fun j hj => ?_⟩
        by_contra hc'
        push Not at hc'
        have h1 := hk0 j hc'.le
        have e : ‖b j‖ * r ^ j = gNorm b r := hj
        linarith
      have h2 : k ≤ wdeg b r := le_csSup hB h
      omega
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.range (k0 + 1))
    (fun k => ‖b (k + 1)‖ * r ^ (k + 1)) ⟨0, by simp⟩
  refine ⟨max (1 / 2) (‖b (j + 1)‖ * r ^ (j + 1) / gNorm b r), le_max_of_le_left (by norm_num),
    max_lt (by norm_num) ((div_lt_one hM).2 (hlt _ (by omega))), ?_⟩
  intro k hk
  rw [max_mul_of_nonneg _ _ hM.le]
  by_cases hkk : k ≤ k0 + 1
  · apply le_max_of_le_right
    rw [div_mul_cancel₀ _ hM.ne']
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact hj k' (by simp; omega)
  · apply le_max_of_le_left
    have := hk0 k (by omega)
    linarith
end Formalism.FN
