-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:51.789385+00:00
-- url     : https://prove2.me/submissions/9c4fb7fe-a14a-4b8a-b924-ac7814e81937

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_val_R
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_exists_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
theorem _root_.solution (v : HeightOneSpectrum R) (c : v.adicCompletion K)
    (hc : c ∈ v.adicCompletionIntegers K) (r : R) (hr : r ≠ 0) :
    ∃ a : R, Valued.v (c - algebraMap K _ (algebraMap R K a)) ≤ v.intValuation r := by
  have hrK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr
  have hrv : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).mpr hrK
  obtain ⟨k', hk'⟩ := exists_near v ((algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ * c)
  have h1 : Valued.v (c - algebraMap K _ (algebraMap R K r * k')) ≤ v.intValuation r := by
    have : c - algebraMap K (v.adicCompletion K) (algebraMap R K r * k') =
        algebraMap K _ (algebraMap R K r) *
          ((algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ * c - algebraMap K _ k') := by
      rw [map_mul, mul_sub, ← mul_assoc, mul_inv_cancel₀ hrv, one_mul]
    rw [this, Valuation.map_mul, val_R]
    exact mul_le_of_le_one_right' hk'
  have hk : v.valuation K (algebraMap R K r * k') ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    have : (((algebraMap R K r * k' : K)) : v.adicCompletion K) =
        c - (c - algebraMap K (v.adicCompletion K) (algebraMap R K r * k')) := by
      rw [sub_sub_cancel]; rfl
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hc (h1.trans (v.intValuation_le_one r)))
  have hγ : v.intValuation r ≠ 0 := v.intValuation_ne_zero r hr
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk (Units.mk0 _ hγ)
  refine ⟨a, ?_⟩
  have e : c - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      (c - algebraMap K _ (algebraMap R K r * k')) -
        algebraMap K _ (algebraMap R K a - algebraMap R K r * k') := by
    rw [map_sub]; ring
  rw [e]
  refine (Valuation.map_sub _ _ _).trans (max_le h1 ?_)
  have := valuedAdicCompletion_eq_valuation' v (algebraMap R K a - algebraMap R K r * k')
  exact this.trans_le ha.le
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
