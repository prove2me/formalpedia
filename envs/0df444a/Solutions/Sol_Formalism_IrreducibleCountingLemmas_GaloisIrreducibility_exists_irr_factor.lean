-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_irr_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:10.87921+00:00
-- url     : https://prove2.me/submissions/a84f95b8-eb42-42b7-9495-908449ab2db3

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section sets
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
variable {K L}
private theorem monicOf_coeff_eq_of_monic {F : Type} [Field F] (P : F[X]) (hP : P.Monic) :
    monicOf (fun i : Fin P.natDegree => P.coeff (i : ℕ)) = P := by
  unfold monicOf
  rw [Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i) P.natDegree]
  exact hP.as_sum.symm
private theorem ne_zero_of_aeval_eq_zero_of_coeff_zero_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E] {f : F[X]}
    (h0 : f.coeff 0 ≠ 0) {x : E} (hx : aeval x f = 0) : x ≠ 0 := by
  rintro rfl
  apply h0
  rw [← coeff_zero_eq_aeval_zero'] at hx
  exact (algebraMap F E).injective (hx.trans (map_zero _).symm)
end sets
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
variable {K L}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {f : K[X]} (hf : f ≠ 0) (h0 : f.coeff 0 ≠ 0) {x : L}
    (hx : aeval x f = 0) :
    ∃ δ, 1 ≤ δ ∧ δ ≤ f.natDegree ∧ ∃ c' : Fin δ → K, Irreducible (monicOf c') ∧
      (monicOf c').coeff 0 ≠ 0 ∧ monicOf c' ∣ f ∧ aeval x (monicOf c') = 0 := by
  have hxne : x ≠ 0 := ne_zero_of_aeval_eq_zero_of_coeff_zero_ne_zero h0 hx
  have hint : IsIntegral K x := IsAlgebraic.isIntegral ⟨f, hf, hx⟩
  have hPm : (minpoly K x).Monic := minpoly.monic hint
  have hPd : minpoly K x ∣ f := minpoly.dvd K x hx
  refine ⟨(minpoly K x).natDegree, minpoly.natDegree_pos hint, natDegree_le_of_dvd hPd hf,
    fun i => (minpoly K x).coeff (i : ℕ), ?_⟩
  rw [monicOf_coeff_eq_of_monic _ hPm]
  exact ⟨minpoly.irreducible hint, minpoly.coeff_zero_ne_zero hint hxne, hPd, minpoly.aeval K x⟩
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
