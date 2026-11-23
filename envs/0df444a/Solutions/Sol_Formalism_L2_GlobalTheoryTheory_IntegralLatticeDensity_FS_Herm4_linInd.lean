-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.linInd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:33.043633+00:00
-- url     : https://prove2.me/submissions/447d5162-d6f5-410a-96a6-700bb8127f75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (H : Herm4 c h) {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) (hv0 : ∀ i, v i ≠ 0)
    (hv : ∀ i j, i ≠ j → h (v i) (v j) = 0) : LinearIndependent K v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 : H.hl (v i) (∑ j ∈ s, g j • v j) = 0 := by rw [hg, map_zero]
  rw [map_sum] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [Finset.sum_eq_single i] at h1
  · exact (mul_eq_zero.mp h1).resolve_right (H.pos (v i) (hv0 i)).1
  · intro j _ hji
    show g j * h (v j) (v i) = 0
    rw [hv j i hji, mul_zero]
  · intro his
    exact absurd hi his
end Herm4
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
