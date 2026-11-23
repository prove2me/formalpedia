-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.chord_field
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:26.02809+00:00
-- url     : https://prove2.me/submissions/3475772b-8089-4576-bc11-14643dd7596f

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {F : Type*} [Field F]
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (a1 a2 a3 a4 a6 z1 z2 z3 v1 v2 v3 l n f u D : F)
    (hv1 : v1 = l * z1 + n) (hv2 : v2 = l * z2 + n) (hv3 : v3 = l * z3 + n)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0)
    (he2 : c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0)
    (he3 : c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0)
    (hc3 : c3 a2 a4 a6 l ≠ 0) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0) (hn : n ≠ 0)
    (hz : z1 ≠ z2) (hD : D = -1 + a1 * z3 + a3 * v3) (hD0 : D ≠ 0) (hf : f * D = z3)
    (hu : u * D = v3) :
    f / u = ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2 ∧
    -1 / u = -((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2) *
        ((((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2) - z1 / v1)
        + -1 / v1) - a1 * (((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2) - a3 := by
  simp only [c3, c2, c1, c0] at he1 he2 he3 hc3
  have hz' : z1 - z2 ≠ 0 := sub_ne_zero.mpr hz
  have hf' := (eq_div_iff hD0).mpr hf
  have hu' := (eq_div_iff hD0).mpr hu
  have hxd : z1 / v1 - z2 / v2 = n * (z1 - z2) / (v1 * v2) := by
    rw [div_sub_div _ _ h1 h2]
    congr 1
    rw [hv1, hv2]
    ring
  have hyd : -1 / v1 - -1 / v2 = l * (z1 - z2) / (v1 * v2) := by
    rw [div_sub_div _ _ h1 h2]
    congr 1
    rw [hv1, hv2]
    ring
  have hl : (-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2) = l / n := by
    rw [hxd, hyd]
    first
      | rw [div_div_div_cancel_right₀ (mul_ne_zero h1 h2), mul_div_mul_right _ _ hz']
      | (field_simp; done)
      | (field_simp
         ring)
  have hG : n ^ 2 * (z3 * (l * z1 + n) * (l * z2 + n) + z1 * (l * z2 + n) * (l * z3 + n) + z2 * (l * z1 + n) * (l * z3 + n)) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * ((l * z1 + n) * (l * z2 + n) * (l * z3 + n)) = 0 := by
    have hc : (1 + a2 * l + a4 * l ^ 2 + a6 * l ^ 3) * (n ^ 2 * (z3 * (l * z1 + n) * (l * z2 + n) + z1 * (l * z2 + n) * (l * z3 + n) + z2 * (l * z1 + n) * (l * z3 + n)) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * ((l * z1 + n) * (l * z2 + n) * (l * z3 + n))) = 0 := by
      linear_combination (n ^ 2 * (n ^ 2 - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * l)) * he1 + (l * n * (2 * n ^ 2 - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * l)) * he2 + (l ^ 2 * (3 * n ^ 2 - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * l)) * he3
    exact (mul_eq_zero.mp hc).resolve_left hc3
  have hG' : n ^ 2 * (z3 * v1 * v2 + z1 * v2 * v3 + z2 * v1 * v3) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * (v1 * v2 * v3) = 0 := by
    rw [hv1, hv2, hv3]
    exact hG
  have hsum : z3 / v3 = (l / n) ^ 2 + a1 * (l / n) - a2 - z1 / v1 - z2 / v2 := by
    rw [← sub_eq_zero]
    have e : z3 / v3 - ((l / n) ^ 2 + a1 * (l / n) - a2 - z1 / v1 - z2 / v2)
        = (n ^ 2 * (z3 * v1 * v2 + z1 * v2 * v3 + z2 * v1 * v3) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * (v1 * v2 * v3)) / (n ^ 2 * (v1 * v2 * v3)) := by
      field_simp
      ring
    rw [e, hG', zero_div]
  have hx3 : f / u = z3 / v3 := by
    rw [hf', hu']
    first
      | exact div_div_div_cancel_right₀ hD0 _ _
      | (field_simp; done)
      | (field_simp
         ring)
  refine ⟨?_, ?_⟩
  · rw [hl, hx3]
    exact hsum
  · rw [hl, ← hsum, hu']
    field_simp
    subst hD hv1 hv2 hv3
    ring
end Formalism.ELL.WeierstrassChordSeries
