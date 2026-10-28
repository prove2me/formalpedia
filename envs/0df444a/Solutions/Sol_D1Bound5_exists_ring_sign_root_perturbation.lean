-- Prove2me | solution 1 for D1Bound5.exists_ring_sign_root_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:43.522289+00:00
-- url     : https://prove2.me/submissions/1b82b29f-f48e-4c93-bd06-4d33b994b24a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_exists_sign_root_perturbation

section
namespace D1Bound5

/-- Sign selection preserves a square root in the original ring. The
complex perturbation lemma does not require division in that ring. -/
theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (u : R) (t : ℂ) (c E : ℝ)
    (ht : t ≠ 0) (hc : 0 ≤ c) (hE : 0 < E)
    (herr : ‖(f u)^2-t^2‖ ≤ E) (hgap : E < (1-c^2)*‖t‖^2) :
    ∃ v : R, v^2 = u^2 ∧ (1+c)*‖t‖*‖f v-t‖ < E := by
  obtain ⟨v,hv,H⟩ := exists_sign_root_perturbation (f u) t c E ht hc hE herr hgap
  rcases hv with rfl | rfl
  · exact ⟨u,rfl,H⟩
  · exact ⟨-u,by ring,by simpa only [map_neg] using H⟩



end D1Bound5
end
