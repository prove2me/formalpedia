-- Prove2me | solution 1 for Formalism.GM.M.SSD.eq_of_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:43.400563+00:00
-- url     : https://prove2.me/submissions/a0869dbb-0de9-4a1b-96e5-15b9be839de9

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ ι K ι' : Type} [Field K] [DecidableEq σ] [Fintype ι] (sv : ι → σ)
namespace Formalism.GM.M.SSD
theorem _root_.solution {x y : ι → ℕ} (h : x ≤ y) (hs : ∑ k, y k ≤ ∑ k, x k) : x = y := by
  have hle : ∀ k ∈ (univ : Finset ι), x k ≤ y k := fun k _ => h k
  have := (Finset.sum_eq_sum_iff_of_le hle).mp (le_antisymm (Finset.sum_le_sum hle) hs)
  funext k; exact this k (mem_univ k)
end Formalism.GM.M.SSD
