-- Prove2me | solution 1 for Formalism.L2.Th1.A.flowThirdPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:28:34.613079+00:00
-- url     : https://prove2.me/submissions/b7661c24-9a1d-4441-b401-8d345145a7cf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird
import Theorems.Thm_Formalism_L2_Th1_A_CubicFlow_gE_line
import Theorems.Thm_Formalism_L2_Th1_A_CubicFlow_gE_line_der
import Theorems.Thm_Formalism_L2_Th1_A_CubicFlow_wEq_iff
import Theorems.Thm_Formalism_L2_Th1_A_CubicFlow_der_gE
import Theorems.Thm_Formalism_L2_Th1_A_CubicFlow_cubic_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open QuadraticFlow CubicFlow
namespace Formalism.L2.Th1.A
theorem _root_.solution : FlowThird.{u} := by
  intro A _ _ W D u1 w1 u2 w2 l n u3 hD hC hF hW2 hDu2 hDw2 hl hn hsum hk3 h12 h31 h32
  obtain ⟨hW1, hDu1, hDw1⟩ := hF
  have hD' := hD
  obtain ⟨hadd, hmul⟩ := hD'
  have hw1 : w1 = l * u1 + n := by linear_combination -hn
  have hw2 : w2 = l * u2 + n := by linear_combination hl - hn
  have r1 : k3 W l * u1 ^ 3 + k2 W l n * u1 ^ 2 + k1 W l n * u1 + k0 W n = 0 := by
    rw [← gE_line, ← hw1]; exact (wEq_iff W u1 w1).1 hW1
  have r2 : k3 W l * u2 ^ 3 + k2 W l n * u2 ^ 2 + k1 W l n * u2 + k0 W n = 0 := by
    rw [← gE_line, ← hw2]; exact (wEq_iff W u2 w2).1 hW2
  have hs : k3 W l * (u1 + u2 + u3) + k2 W l n = 0 := hsum
  have hk : k3 W l ≠ 0 := hk3
  obtain ⟨r3, e2, -⟩ := cubic_roots h12 r1 r2 hs
  have hD0 : D 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hDline : ∀ z, D (l * z + n) = l * D z + z * D l + D n := by
    intro z; rw [hadd, hmul]

  have T1 : u1 * D l + D n = 3 * k3 W l * u1 ^ 2 + 2 * k2 W l n * u1 + k1 W l n := by
    have h := hDline u1
    rw [← hw1, hDw1, hDu1] at h
    have hd := gE_line_der W l n u1
    rw [← hw1] at hd
    linear_combination hd - h
  have T2 : u2 * D l + D n = 0 := by
    have h := hDline u2
    rw [← hw2, hDw2, hDu2] at h
    linear_combination -h
  have hq : (u1 - u2) * (D l - k3 W l * (u1 - u3)) = 0 := by
    linear_combination T1 - T2 + 2 * u1 * hs - e2
  have hDl := sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left (sub_ne_zero.mpr h12))
  have hg3 : gE W u3 (l * u3 + n) = 0 := by rw [gE_line]; exact r3
  have hd3 := der_gE hD hC u3 (l * u3 + n)
  rw [hg3, hD0, hDline] at hd3
  have hd3' := gE_line_der W l n u3
  have hK : k3 W l * (u3 - u1) * (u3 - u2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hk (sub_ne_zero.mpr h31)) (sub_ne_zero.mpr h32)
  have hkey : (k3 W l * (u3 - u1) * (u3 - u2)) * (D u3 + fwAt W u3 (l * u3 + n)) = 0 := by
    linear_combination -hd3 - D u3 * hd3' - D u3 * (2 * u3 * hs - e2)
      + fwAt W u3 (l * u3 + n) * (u3 - u2) * hDl + fwAt W u3 (l * u3 + n) * T2
  have hX : D u3 = -fwAt W u3 (l * u3 + n) := by
    have := (mul_eq_zero.mp hkey).resolve_left hK
    linear_combination this
  refine ⟨(wEq_iff W u3 _).2 hg3, hX, ?_⟩
  rw [hDline]
  linear_combination l * hX + hd3' + 2 * u3 * hs - e2 + (u3 - u2) * hDl + T2
end Formalism.L2.Th1.A
