-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.tri_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:47.690365+00:00
-- url     : https://prove2.me/submissions/30d6a462-7079-4229-8a6e-4d1c52b323f3

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (k : ℕ) : tri R n (k + 1) =
    ∑ i ∈ range (k + 1), (-1) ^ i * yv R n (i + 1) * tri R n (k - i) := by
  rw [tri]
  exact Fin.sum_univ_eq_sum_range (fun i => (-1) ^ i * yv R n (i + 1) * tri R n (k - i)) (k + 1)
end Formalism.FT.SymmetricSeries
