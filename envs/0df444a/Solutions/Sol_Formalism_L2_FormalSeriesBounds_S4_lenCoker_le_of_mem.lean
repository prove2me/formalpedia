-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.lenCoker_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:50.17164+00:00
-- url     : https://prove2.me/submissions/86858b4b-cfd0-4e18-9524-242342373f2a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x)
    {m h : ℕ} (B : Matrix (Fin m) (Fin h) R) {x : R} (hx : x ∈ fitt0 B) :
    lenCoker v B ≤ v x := by
  unfold fitt0 at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact Finset.inf_le (Finset.mem_univ g)
  | zero => simp
  | add a b _ _ ha hb => exact le_trans (le_min ha hb) (v.map_add a b)
  | smul c a _ ha =>
    rw [smul_eq_mul, v.map_mul]
    exact le_trans ha (le_add_of_nonneg_left (hv c))
end Formalism.L2.FormalSeriesBounds.S4
