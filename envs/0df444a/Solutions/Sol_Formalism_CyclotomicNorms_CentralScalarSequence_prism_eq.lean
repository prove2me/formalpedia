-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.prism_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:24.995492+00:00
-- url     : https://prove2.me/submissions/9d860ed5-6421-46a6-b524-b641c5083ebc

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_ins_agree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.CentralScalarSequence
variable {G : Type} [Group G]
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.CyclotomicNorms.CentralScalarSequence
theorem _root_.solution {n : ℕ} (z : G) (f : (Fin (n + 1) → G) → W) (x : Fin n → G) (v : ℕ → G)
    (hx : ∀ k : Fin n, x k = v k) :
    prism R z f x = ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z v k) := by
  unfold prism
  rw [← Fin.sum_univ_eq_sum_range (fun i => (-1 : R) ^ i • f (fun k => insN i z v k)) (n + 1)]
  refine sum_congr rfl fun i _ => ?_
  congr 2
  funext k
  exact ins_agree i z x v hx k
end Formalism.CyclotomicNorms.CentralScalarSequence
