-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_span_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:05.887322+00:00
-- url     : https://prove2.me/submissions/6629ab57-44a7-47a9-ade0-6008e963c930

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_prod_mem_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial PiTensorProduct
open scoped Pointwise
open Module
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S]
    {k n : ℕ} {ι : S → Type*}
    (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K) (F : S → MvPolynomial (Fin k × Fin n) K)
    (hF : ∀ s, F s ∈ Submodule.span R (Set.range (b s))) :
    ∏ s, blockEmb K s (F s) ∈
      Submodule.span R (Set.range fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) := by
  have h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (Set.range fun j => blockEmb K s (b s j)) := by
    intro s
    have h := Submodule.mem_map_of_mem (f := ((blockEmb K s).toLinearMap.restrictScalars R)) (hF s)
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  have h2 := ldtensor_prod_mem_prod Finset.univ _ _ fun s _ => h1 s
  rw [Submodule.prod_span] at h2
  refine Submodule.span_mono ?_ h2
  intro y hy
  rw [Set.mem_finset_prod] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  choose i hi using fun s => hg (Finset.mem_univ s)
  exact ⟨i, Finset.prod_congr rfl fun s _ => hi s⟩
end Formalism.GradedWeylDivisibility
