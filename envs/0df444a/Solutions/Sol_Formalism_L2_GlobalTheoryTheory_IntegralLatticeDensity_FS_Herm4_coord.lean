-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:03:15.1898+00:00
-- url     : https://prove2.me/submissions/9a5596e0-a925-4ea9-bd5b-f176670d0401

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Module
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)
variable {c h}
private theorem coord_lemma (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (v : V) (i : n) : h v (b i) = b.repr v i * h (b i) (b i) := by
  have e : h v (b i) = H.hl (b i) (∑ j, b.repr v j • b j) := by
    rw [b.sum_repr v]
    rfl
  rw [e, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rfl
  · intro j _ hj
    show b.repr v j * h (b j) (b i) = 0
    rw [hb j i hj, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)
variable {c h}
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace Herm4
theorem _root_.solution (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (v : V) (i : n) : h v (b i) = b.repr v i * h (b i) (b i) :=
  coord_lemma H b hb v i
end Herm4
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
