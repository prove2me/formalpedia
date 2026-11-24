-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.span_map_weightBasis_eq_dualWeyl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:10.158904+00:00
-- url     : https://prove2.me/submissions/3f630152-2328-4810-ad7a-a00149d3cfbc

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLKBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_map_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] {k n : ℕ}
    {ν : Fin n → ℕ} {ι : Type} {b : ι → MvPolynomial (Fin k × Fin n) R} {μ : ι → (Fin k → ℕ)}
    (hb : IsWeightBasis R k n ν b μ) :
    Submodule.span K (Set.range fun i => map (algebraMap R K) (b i)) = dualWeyl K k n ν := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : b i ∈ dualWeyl R k n ν := hb.2.1 ▸ Submodule.subset_span ⟨i, rfl⟩
    exact dualWeylMap R K (algebraMap R K) k n ν (b i) hi
  · rw [standardMonomialSpanDomain K k n ν, Submodule.span_le]
    rintro f ⟨K', sz, hsz, I, hsh, rfl⟩
    rw [← ldlat_map_bidet (algebraMap R K)]
    have hmem : bideterminant R sz hsz I ∈ Submodule.span R (Set.range b) := by
      rw [hb.2.1, ← hsh]
      exact bidetMem R k n K' sz hsz I
    have h1 := Submodule.mem_map_of_mem (f := (mapAlgHom (Algebra.ofId R K)).toLinearMap) hmem
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact Submodule.span_le_restrictScalars R K _ h1
end Formalism.GradedWeylDivisibility
