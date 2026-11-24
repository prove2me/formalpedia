-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:10:39.154803+00:00
-- url     : https://prove2.me/submissions/d4f09456-8e8b-40aa-8053-e8794e3e29ac

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_int_R
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_exists_den_local
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
private theorem fin_lemma_3 (b : FiniteAdeleRing R K) :
    {v : HeightOneSpectrum R | b v ∉ v.adicCompletionIntegers K}.Finite := by
  first
  | exact Filter.eventually_cofinite.1 b.2
  | exact b.2
  | exact Filter.eventually_cofinite.1 b.property
  | (have h := b.2; rw [Filter.eventually_cofinite] at h; exact h)
private theorem mulApp_lemma_4 (a b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := by
  first
  | rfl
  | simp
  | exact RestrictedProduct.mul_apply a b v
private theorem algApp_lemma_5 (r : R) (v : HeightOneSpectrum R) :
    (algebraMap R (FiniteAdeleRing R K) r) v = algebraMap K (v.adicCompletion K) (algebraMap R K r) := by
  first
  | rfl
  | (rw [IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K)]; rfl)
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
theorem _root_.solution (b : FiniteAdeleRing R K) :
    ∃ r : R, r ≠ 0 ∧ IsInt (algebraMap R (FiniteAdeleRing R K) r * b) := by
  classical
  have hS := fin_lemma_3 b
  choose s hs0 hs using fun w : HeightOneSpectrum R => exists_den_local w (b w)
  refine ⟨∏ w ∈ hS.toFinset, s w, Finset.prod_ne_zero_iff.2 (fun w _ => hs0 w), ?_⟩
  intro v
  rw [mulApp_lemma_4, algApp_lemma_5]
  by_cases hv : v ∈ hS.toFinset
  · rw [← Finset.mul_prod_erase hS.toFinset s hv]
    simp only [map_mul]
    rw [show ∀ x y z : v.adicCompletion K, x * y * z = y * (x * z) from
      fun x y z => by ring]
    exact mul_mem (int_R v _) (hs v)
  · have hb : b v ∈ v.adicCompletionIntegers K := by
      by_contra h
      exact hv (hS.mem_toFinset.2 h)
    exact mul_mem (int_R v _) hb
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
