-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_qindep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:22.057596+00:00
-- url     : https://prove2.me/submissions/6978f45e-6cf5-4357-a3cc-1bea3b0f5e56

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Trace
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
end Trace
section Real
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
private theorem addHom_ratCast_smul_lemma_3 {K V : Type*} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n)) (q : ℚ) (x : V) :
    ι ((q : K) • x) = (q : ℝ) • ι x := by
  exact map_ratCast_smul ι K ℝ q x
end Real
section Finite
variable {V : Type*} [AddCommGroup V]
end Finite
section Isom
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
end Isom
section Main
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
end Main
end Formalism.HermitianLatticesTheory
end
end

set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (g : Fin n → ℚ)
    (hg : ∑ i, (g i : K) • u i = 0) : g = 0 := by
  have hsum : ∑ i, ((g i : ℚ) : ℝ) • (ι ∘ u) i = 0 := by
    have e := congrArg ι hg
    rw [map_sum, map_zero] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.comp_apply, addHom_ratCast_smul_lemma_3 ι (g i) (u i)]
  funext i
  have := Fintype.linearIndependent_iff.mp hu (fun i => ((g i : ℚ) : ℝ)) hsum i
  simpa using this
end Formalism.HermitianLatticesTheory
