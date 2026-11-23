-- Prove2me | solution 1 for Formalism.L2.SG.Pf.WuDec.norm_tens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:24.598718+00:00
-- url     : https://prove2.me/submissions/f35f7837-52a7-45b0-8a36-abcbc2015f52

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
theorem _root_.solution (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) :
    ‖tens x‖ = ∏ v, ‖x v‖ := by
  have h := hi x x
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖tens x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
    rw [← Finset.prod_pow]
    exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (tens x)), h2,
    Real.sqrt_sq (Finset.prod_nonneg fun v _ => norm_nonneg (x v))]
end Formalism.L2.SG.Pf.WuDec
