-- Prove2me | solution 1 for D1Bound5.exists_sign_root_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:47.472671+00:00
-- url     : https://prove2.me/submissions/42d7792f-3276-43b9-ac7a-69ee356a32eb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_normalized_root_perturbation

section
namespace D1Bound5



/-- Choose the sign of a square root close to a prescribed nonzero target.
The error estimate is multiplicative, with no division by the root. -/
theorem _root_.solution (u t : ℂ) (c E : ℝ)
    (ht : t ≠ 0) (hc : 0 ≤ c) (hE : 0 < E)
    (herr : ‖u^2-t^2‖ ≤ E) (hgap : E < (1-c^2)*‖t‖^2) :
    ∃ v : ℂ, (v = u ∨ v = -u) ∧ (1+c)*‖t‖*‖v-t‖ < E := by
  have htN : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have htN2 : 0 < ‖t‖^2 := sq_pos_of_pos htN
  let q := u/t
  have hq2 : q^2-1 = (u^2-t^2)/(t^2) := by
    dsimp only [q]
    field_simp
  have hqN : ‖q^2-1‖ ≤ E/(‖t‖^2) := by
    rw [hq2, norm_div, norm_pow]
    exact div_le_div_of_nonneg_right herr htN2.le
  have hgap' : E/(‖t‖^2) < 1-c^2 := (div_lt_iff₀ htN2).mpr hgap
  have hE' : 0 < E/(‖t‖^2) := div_pos hE htN2
  have transfer (v : ℂ) (H : (1+c)*‖v/t-1‖ < E/(‖t‖^2)) :
      (1+c)*‖t‖*‖v-t‖ < E := by
    have hid : v/t-1 = (v-t)/t := by field_simp
    rw [hid, norm_div] at H
    have H' := (lt_div_iff₀ htN2).mp H
    have hidR : (1+c)*(‖v-t‖/‖t‖)*‖t‖^2 = (1+c)*‖t‖*‖v-t‖ := by
      field_simp
    rwa [hidR] at H'
  by_cases hRe : 0 ≤ q.re
  · exact ⟨u, Or.inl rfl, transfer u (normalized_root_perturbation q c _ hc hE' hgap' hRe hqN)⟩
  · refine ⟨-u, Or.inr rfl, transfer (-u) ?_⟩
    have hneg : 0 ≤ (-q).re := by simp only [Complex.neg_re]; linarith
    have hsq : ‖(-q)^2-1‖ ≤ E/(‖t‖^2) := by simpa only [neg_sq] using hqN
    have H := normalized_root_perturbation (-q) c _ hc hE' hgap' hneg hsq
    simpa only [q, neg_div] using H

end D1Bound5
end
