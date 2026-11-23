-- Prove2me | solution 1 for Formalism.FN.GjScaling.card_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:27.690794+00:00
-- url     : https://prove2.me/submissions/dd449185-a4d5-4f3f-9661-c8923d52e7a0

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
open Formalism.FN.GjScaling
variable {ι : Type*} [Fintype ι]
variable (n j : ℕ)
namespace Formalism.FN.GjScaling
theorem _root_.solution (hj : j ≤ n) : Fintype.card {i : Fin n // ¬ (i : ℕ) < j} = n - j := by
  rw [← Fintype.card_fin (n - j)]
  exact Fintype.card_congr
    { toFun := fun i => ⟨(i.1 : ℕ) - j, by have := i.1.2; have := i.2; omega⟩
      invFun := fun k => ⟨⟨(k : ℕ) + j, by have := k.2; omega⟩, by
        show ¬ ((k : ℕ) + j < j); omega⟩
      left_inv := fun i => Subtype.ext (Fin.ext (by
        show (i.1 : ℕ) - j + j = i.1
        have := i.2
        omega))
      right_inv := fun k => Fin.ext (by
        show (k : ℕ) + j - j = k
        omega) }
end Formalism.FN.GjScaling
