-- Prove2me | solution 1 for Formalism.GM.M.SSD.SFree.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:34.225199+00:00
-- url     : https://prove2.me/submissions/8c3172c0-4062-4f02-b700-12ba4e0ff4fd

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
variable {σ ι K : Type} [CommRing K] [Nontrivial K] [DecidableEq σ] (sv : ι → σ)
omit [Nontrivial K]
namespace Formalism.GM.M.SSD
namespace SFree
theorem _root_.solution {α : Type} (u : Finset α) (f : α → MvPolynomial σ K) (h : ∀ i ∈ u, SFree sv (f i)) :
    SFree sv (∑ i ∈ u, f i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using SFree.C sv (0 : K)
  | insert i u hi ih =>
    rw [sum_insert hi]
    exact (h i (mem_insert_self _ _)).add sv (ih fun k hk => h k (mem_insert_of_mem hk))
end SFree
end Formalism.GM.M.SSD
