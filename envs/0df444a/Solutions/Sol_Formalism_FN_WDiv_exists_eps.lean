-- Prove2me | solution 1 for Formalism.FN.WDiv.exists_eps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:12.939233+00:00
-- url     : https://prove2.me/submissions/1e026da7-aace-4650-b9ae-a0eebcc1d90c

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision
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
open Filter Topology Polynomial
noncomputable section
open Formalism Formalism.FN Formalism.FN.WDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
omit [CompleteSpace K]
namespace Formalism.FN.WDiv
theorem _root_.solution (g : ℕ → K) (r : ℝ) (hr : 0 < r) (hg : ConvOn g r) (hne : g ≠ 0) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ ∀ k, wdeg g r < k → ‖g k‖ * r ^ k ≤ ε * gNorm g r := by
  obtain ⟨-, hM⟩ := wdeg_spec g r hr hg hne
  have hle : ∀ k, ‖g k‖ * r ^ k ≤ gNorm g r := fun k => le_ciSup (gNorm_bdd_of_conv g r hg) k
  obtain ⟨K0, hK0⟩ := eventually_atTop.1
    ((hg : Tendsto _ atTop _).eventually (eventually_le_nhds (half_pos hM)))
  have hbdd : BddAbove {k : ℕ | ‖g k‖ * r ^ k = gNorm g r} := ⟨K0, fun k hk => by
    simp only [Set.mem_ofPred_eq] at hk
    by_contra h; push Not at h
    have := hK0 k h.le
    rw [hk] at this; linarith⟩
  have hlt : ∀ k, wdeg g r < k → ‖g k‖ * r ^ k < gNorm g r := by
    intro k hk
    refine lt_of_le_of_ne (hle k) fun h => ?_
    have : k ≤ wdeg g r := le_csSup hbdd h
    omega
  obtain ⟨k1, hk1T, hk1⟩ := Finset.exists_max_image (Finset.Icc (wdeg g r + 1) (max K0 (wdeg g r + 1)))
    (fun k => ‖g k‖ * r ^ k) ⟨wdeg g r + 1, by simp⟩
  have hk1lt : ‖g k1‖ * r ^ k1 < gNorm g r := hlt k1 (by simp at hk1T; omega)
  refine ⟨max (‖g k1‖ * r ^ k1 / gNorm g r) (1 / 2), le_max_of_le_right (by norm_num),
    max_lt ((div_lt_one hM).2 hk1lt) (by norm_num), fun k hk => ?_⟩
  rw [max_mul_of_nonneg _ _ hM.le]
  by_cases hkK : k ≤ max K0 (wdeg g r + 1)
  · have := hk1 k (by simp; omega)
    exact le_max_of_le_left (by rw [div_mul_cancel₀ _ hM.ne']; exact this)
  · exact le_max_of_le_right (by have := hK0 k (by omega); linarith)
end Formalism.FN.WDiv
