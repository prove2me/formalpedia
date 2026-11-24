-- Prove2me | solution 1 for Formalism.L2.SG.Pf.WuDec.inner_tens_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:41.375546+00:00
-- url     : https://prove2.me/submissions/a82e3db6-8ce1-4238-8026-d82c3d73749a

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
theorem _root_.solution [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (ξ : ∀ v, V v)
    (v : ι) (a b : V v) :
    ⟪tens (Function.update ξ v a), tens (Function.update ξ v b)⟫_ℂ =
      ⟪a, b⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ := by
  rw [hi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw), Function.update_of_ne (Finset.ne_of_mem_erase hw)]
end Formalism.L2.SG.Pf.WuDec
