-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.weight_posWt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:43.243388+00:00
-- url     : https://prove2.me/submissions/85601162-ce7b-48bf-a8b3-ea500609c0d8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (s : σ) (n : σ × Fin r0 × Fin r1 →₀ ℕ) :
    Finsupp.weight (posWt r0 r1 s) n = ∑ x : Fin r0 × Fin r1, n (s, x) := by
  classical
  have hinj : Set.InjOn (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1))
      ((Finset.univ : Finset (Fin r0 × Fin r1)) : Set (Fin r0 × Fin r1)) :=
    fun x _ y _ h => by simpa using h
  have hsub : n.support ⊆ n.support ∪
      Finset.univ.image (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1)) :=
    fun i hi => Finset.mem_union_left _ hi
  rw [Finsupp.weight_apply]
  refine (Finsupp.sum_of_support_subset n hsub (fun i c => c • posWt r0 r1 s i) ?hz).trans ?hs
  case hz =>
    intro i _
    first
      | exact zero_smul ℕ _
      | simp
  case hs =>
    calc ∑ i ∈ n.support ∪ Finset.univ.image (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1)),
          n i • posWt r0 r1 s i
        = ∑ i ∈ Finset.univ.image (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1)),
          n i • posWt r0 r1 s i := by
          refine (Finset.sum_subset (fun i hi => Finset.mem_union_right _ hi) ?_).symm
          intro i _ hi
          have hne : i.1 ≠ s := by
            intro h
            apply hi
            rw [Finset.mem_image]
            exact ⟨i.2, Finset.mem_univ _, by rw [← h]⟩
          simp [posWt, hne]
      _ = ∑ x : Fin r0 × Fin r1, n (s, x) • posWt r0 r1 s (s, x) := Finset.sum_image hinj
      _ = ∑ x : Fin r0 × Fin r1, n (s, x) := by simp [posWt]
end Formalism.InvariantFactorPaths.G7
