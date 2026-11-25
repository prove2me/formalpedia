-- Prove2me | solution 1 for Formalism.L2.Geo.ExtensionFiltration.sq_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:18:41.014923+00:00
-- url     : https://prove2.me/submissions/34e1d78d-e7b9-4306-8319-43ed76299992

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_OperatorNormFibers_PDescentCutA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
set_option linter.deprecated false
open Module NumberField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.ExtensionFiltration
namespace Formalism.L2.Geo.ExtensionFiltration
theorem _root_.solution {C Hb : Type} [AddCommGroup C] [Fintype Hb] (B : C →+ C →+ ℂ)
    (hpos : ∀ x, 0 ≤ (B x x).re) (y : Hb → C) :
    (B (∑ g, y g) (∑ g, y g)).re ≤ (Fintype.card Hb : ℝ) * ∑ g, (B (y g) (y g)).re := by
  classical
  have hS : (B (∑ g, y g) (∑ g, y g)).re = ∑ g, ∑ h, (B (y g) (y h)).re := by
    simp only [map_sum, AddMonoidHom.finset_sum_apply, Complex.re_sum]
    first
      | rfl
      | exact Finset.sum_comm
  have hD : ∀ g h, (B (y g - y h) (y g - y h)).re =
      (B (y g) (y g)).re + (B (y h) (y h)).re - (B (y g) (y h)).re - (B (y h) (y g)).re := by
    intro g h
    simp only [map_sub, AddMonoidHom.sub_apply, Complex.sub_re]
    ring
  have hnn : 0 ≤ ∑ g, ∑ h, (B (y g - y h) (y g - y h)).re :=
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun h _ => hpos _
  have expand : ∑ g, ∑ h, (B (y g - y h) (y g - y h)).re =
      ∑ g, ∑ h : Hb, (B (y g) (y g)).re + ∑ g : Hb, ∑ h, (B (y h) (y h)).re -
        ∑ g, ∑ h, (B (y g) (y h)).re - ∑ g, ∑ h, (B (y h) (y g)).re := by
    simp only [hD, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have a1 : ∑ g, ∑ h : Hb, (B (y g) (y g)).re = (Fintype.card Hb : ℝ) * ∑ g, (B (y g) (y g)).re := by
    rw [Finset.mul_sum]
    simp
  have a2 : ∑ g : Hb, ∑ h, (B (y h) (y h)).re = (Fintype.card Hb : ℝ) * ∑ g, (B (y g) (y g)).re := by
    simp
  have a3 : ∑ g, ∑ h, (B (y h) (y g)).re = ∑ g, ∑ h, (B (y g) (y h)).re := Finset.sum_comm
  rw [expand, a1, a2, a3] at hnn
  rw [hS]
  linarith
end Formalism.L2.Geo.ExtensionFiltration
