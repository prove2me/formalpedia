-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.mem_of_isInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:42.892327+00:00
-- url     : https://prove2.me/submissions/a6c35f27-d86d-4811-ac28-2576721238f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
private theorem memO_lemma (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1 := by
  first
  | exact IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers ..
  | exact Iff.rfl
  | exact Valuation.mem_valuationSubring_iff _ _
  | simp [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
private theorem algKApp_lemma_6 (k : K) (v : HeightOneSpectrum R) :
    (algebraMap K (FiniteAdeleRing R K) k) v = algebraMap K (v.adicCompletion K) k := by
  first
  | rfl
  | simp
  | (simp; rfl)
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
theorem _root_.solution (k : K) (h : IsInt (algebraMap K (FiniteAdeleRing R K) k)) :
    k ∈ (algebraMap R K).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K k (fun v => ?_)
  have h1 := h v
  rw [algKApp_lemma_6, memO_lemma] at h1
  first
  | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k).symm.le.trans h1
  | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := K) v k).symm.le.trans h1
  | (rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1)
  | (erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1; exact h1)
  | simpa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using h1
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
