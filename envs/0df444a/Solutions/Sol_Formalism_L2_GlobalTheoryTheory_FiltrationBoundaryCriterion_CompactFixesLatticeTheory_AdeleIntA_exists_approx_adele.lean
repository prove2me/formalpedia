-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:35.443901+00:00
-- url     : https://prove2.me/submissions/178f2a22-c53e-4960-beb8-df73096047e1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_exists_den
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_exists_approx
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
private theorem valR_lemma_2 (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  first
  | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans
      (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap v _)
  | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := K) v _).trans
      (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v _)
  | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap])
  | (erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap])
  | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap])
  | simp [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
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
theorem _root_.solution (b : FiniteAdeleRing R K) :
    ∃ u : K, IsInt (b - algebraMap K (FiniteAdeleRing R K) u) := by
  obtain ⟨r, hr, hrb⟩ := exists_den b
  obtain ⟨a, ha⟩ := exists_approx _ hrb r hr
  have hrK : algebraMap R K r ≠ 0 := by
    first
    | exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
    | exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr
  refine ⟨algebraMap R K a / algebraMap R K r, ?_⟩
  intro v
  have hv := ha v
  rw [mulApp_lemma_4, algApp_lemma_5] at hv
  have hsub : (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v
      = b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r) := by
    first
    | rfl
    | simp [algKApp_lemma_6]
    | (rw [← algKApp_lemma_6]; rfl)
  rw [hsub, memO_lemma]
  have e1 : algebraMap R K r * (algebraMap R K a / algebraMap R K r) = algebraMap R K a := by
    first
    | (field_simp; done)
    | (rw [← mul_div_assoc]; exact mul_div_cancel_left₀ _ hrK)
    | (field_simp; ring)
  have e2 : algebraMap K (v.adicCompletion K) (algebraMap R K r) *
      (b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r)) =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v - algebraMap K (v.adicCompletion K) (algebraMap R K a) := by
    rw [mul_sub, ← map_mul (algebraMap K (v.adicCompletion K)), e1]
  have hv2 : v.intValuation r *
      Valued.v (b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r)) ≤
      v.intValuation r := by
    have h3 := hv
    rw [← e2, Valuation.map_mul, valR_lemma_2] at h3
    exact h3
  have hne : v.intValuation r ≠ 0 := by
    first
    | exact v.intValuation_ne_zero r hr
    | exact IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v r hr
    | (rw [← valR_lemma_2 (K := K) v r, Valuation.ne_zero_iff, map_ne_zero]; exact hrK)
  calc Valued.v (b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r))
      = (v.intValuation r)⁻¹ * (v.intValuation r *
          Valued.v (b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ ≤ (v.intValuation r)⁻¹ * v.intValuation r := by
        first
        | gcongr
        | exact mul_le_mul_left' hv2 _
        | exact mul_le_mul_left hv2 _
    _ = 1 := inv_mul_cancel₀ hne
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
