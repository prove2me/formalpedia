-- Prove2me | solution 1 for Formalism.L2.Th1.F.LegendreModelEllipticTorsion.sumB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:28:53.933045+00:00
-- url     : https://prove2.me/submissions/a2c3ac33-43d5-430a-83a8-9e512c6d1969

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Legendre
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_tsum_e2Summand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open UpperHalfPlane hiding I
open EisensteinSeries Complex SummationFilter ModularGroup
open scoped Real
namespace Formalism.L2.Th1.F.LegendreModelEllipticTorsion
private lemma one_div_sq_eq_of_eq_mul (X Y c : ℂ) (h : X = c * Y) :
    1 / X ^ 2 = (c ^ 2)⁻¹ * Y ^ (-2 : ℤ) := by
  subst h
  rw [mul_pow, one_div, mul_inv, zpow_neg]
  norm_cast
end Formalism.L2.Th1.F.LegendreModelEllipticTorsion
namespace Formalism.L2.Th1.F
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open UpperHalfPlane hiding I
open EisensteinSeries Complex SummationFilter ModularGroup
open scoped Real
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F Formalism.L2.Th1.F.LegendreModelEllipticTorsion
namespace Formalism.L2.Th1.F.LegendreModelEllipticTorsion
theorem _root_.solution (u v : ℂ) (h : 0 < (v / u).im) :
    ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 = (v ^ 2)⁻¹ * G2 (S • ⟨v / u, h⟩) := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  have hv : v ≠ 0 := by
    rintro rfl
    simp at h
  have hw : ((S • (⟨v / u, h⟩ : ℍ) : ℍ) : ℂ) = -(u / v) := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(v / u))⁻¹ = -(u / v)
    rw [inv_neg, inv_div]
  rw [← tsum_e2Summand, ← tsum_mul_left]
  congr 1
  funext m
  have he : e2Summand (-m) (S • (⟨v / u, h⟩ : ℍ)) = e2Summand m (S • (⟨v / u, h⟩ : ℍ)) :=
    EisensteinSeries.e2Summand_even _ m
  rw [← he]
  unfold EisensteinSeries.e2Summand
  rw [← tsum_mul_left]
  congr 1
  funext n
  simp only [eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hw]
  apply one_div_sq_eq_of_eq_mul
  field_simp
  push_cast
  ring
end Formalism.L2.Th1.F.LegendreModelEllipticTorsion
