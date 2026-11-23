-- Prove2me | solution 1 for Formalism.L2.SG.Pf.WuDec.tens_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:45.448878+00:00
-- url     : https://prove2.me/submissions/cc006538-538a-440d-b961-4608d958f238

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_TensInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.WuDec
variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vπ : Type} [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ] {tens : (∀ v, V v) → Vπ}
namespace Formalism.L2.SG.Pf.WuDec
theorem _root_.solution (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (c : ι → ℂ) (x : ∀ v, V v) :
    tens (fun v => c v • x v) = (∏ v, c v) • tens x := by
  have key : ⟪tens (fun v => c v • x v) - (∏ v, c v) • tens x,
      tens (fun v => c v • x v) - (∏ v, c v) • tens x⟫_ℂ = 0 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hi,
      Finset.prod_mul_distrib, map_prod]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp key)
end Formalism.L2.SG.Pf.WuDec
