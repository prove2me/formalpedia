-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.wsub_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:14.957796+00:00
-- url     : https://prove2.me/submissions/902f8464-0c4b-44eb-99b7-b6d0200f858c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (Bd : Finset (Letter Ty r n →₀ ℕ)) (z : ℤ) (x : Bd → ℤ) (hz : z ≠ 0)
    (hx : z • x ∈ Wsub r n cc isX a Bd) : x ∈ Wsub r n cc isX a Bd := by
  have e : map (Int.castRingHom ℚ) (poly Bd (z • x)) = (z : ℚ) • map (Int.castRingHom ℚ) (poly Bd x) := by
    ext m
    rw [coeff_smul, coeff_map_poly, coeff_map_poly]
    split_ifs <;> simp
  have hx' : map (Int.castRingHom ℚ) (poly Bd (z • x)) ∈ HHa r n ℚ cc isX a := hx
  rw [e] at hx'
  have hz' : (z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hz
  have h2 := hha_smul r n ℚ cc isX a ((z : ℚ)⁻¹) hx'
  rw [smul_smul, inv_mul_cancel₀ hz', one_smul] at h2
  show map (Int.castRingHom ℚ) (poly Bd x) ∈ HHa r n ℚ cc isX a
  exact h2
end Formalism.L2.FormalSeriesBounds.HaP
