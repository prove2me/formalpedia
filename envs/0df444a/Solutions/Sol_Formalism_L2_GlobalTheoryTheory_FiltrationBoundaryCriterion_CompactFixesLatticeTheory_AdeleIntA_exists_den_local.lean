-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_den_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:03:17.246499+00:00
-- url     : https://prove2.me/submissions/2f0e74dd-9ca5-44f1-a4f6-9cd8178b7426

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_int_R
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
theorem _root_.solution (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ s : R, s ≠ 0 ∧
      algebraMap K (v.adicCompletion K) (algebraMap R K s) * y ∈ v.adicCompletionIntegers K := by
  obtain ⟨k, hk⟩ := exists_near v y
  obtain ⟨a, b, hb, hab⟩ :
      ∃ a b : R, b ∈ nonZeroDivisors R ∧ algebraMap R K a / algebraMap R K b = k := by
    first
    | exact IsFractionRing.div_surjective (A := R) k
    | (obtain ⟨a, b, h⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) k;
        exact ⟨a, b, b.2, by rw [← h, IsFractionRing.mk'_eq_div]⟩)
  subst hab
  have hb0 : b ≠ 0 := by
    first
    | exact nonZeroDivisors.ne_zero hb
    | exact mem_nonZeroDivisors_iff_ne_zero.1 hb
  have hbK : algebraMap R K b ≠ 0 := by
    first
    | exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    | exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hb0
  refine ⟨b, hb0, ?_⟩
  have e1 : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a := by
    first
    | (field_simp; done)
    | (rw [← mul_div_assoc]; exact mul_div_cancel_left₀ _ hbK)
    | (field_simp; ring)
  have e2 : algebraMap K (v.adicCompletion K) (algebraMap R K b) *
      (y - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K b)) +
      algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      algebraMap K (v.adicCompletion K) (algebraMap R K b) * y := by
    rw [mul_sub, ← map_mul (algebraMap K (v.adicCompletion K)), e1, sub_add_cancel]
  rw [← e2]
  exact add_mem (mul_mem (int_R v b) hk) (int_R v a)
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
