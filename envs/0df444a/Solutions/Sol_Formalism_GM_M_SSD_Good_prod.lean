-- Prove2me | solution 1 for Formalism.GM.M.SSD.Good.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:22.200484+00:00
-- url     : https://prove2.me/submissions/c8965cb9-0eb7-4eee-a1d3-dd002329af83

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_Good_one

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
namespace Formalism.GM.M.SSD
namespace Good
theorem _root_.solution {α : Type} (u : Finset α) (f : α → MvPolynomial σ K) (a : α → ι → ℕ) (s : α → σ →₀ ℕ)
    (h : ∀ i ∈ u, Good sv (f i) (a i) (s i)) :
    Good sv (∏ i ∈ u, f i) (∑ i ∈ u, a i) (∑ i ∈ u, s i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using Good.one sv
  | insert i u hi ih =>
    rw [prod_insert hi, sum_insert hi, sum_insert hi]
    exact (h i (mem_insert_self _ _)).mul sv (ih fun k hk => h k (mem_insert_of_mem hk))
end Good
end Formalism.GM.M.SSD
