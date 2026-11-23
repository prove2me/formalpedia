-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.prism_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:26.228992+00:00
-- url     : https://prove2.me/submissions/652dbc10-9e86-4e2d-8caa-2d6cbabf89ef

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central

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
theorem _root_.solution [TopologicalSpace G] [TopologicalSpace W] [DiscreteTopology W] {n : ℕ}
    (z : G) (f : (Fin (n + 1) → G) → W) (hf : Continuous f) : Continuous (prism R z f) := by
  have hV : Continuous fun x : Fin n → G => fun i : Fin (n + 1) =>
      f (Fin.insertNth (α := fun _ => G) i z x) :=
    continuous_pi fun i => hf.comp (continuous_const.finInsertNth i continuous_id)
  exact (continuous_of_discreteTopology
    (f := fun v : Fin (n + 1) → W => ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • v i)).comp hV
end Formalism.CyclotomicNorms.CentralScalarSequence
