-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_mem_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:34.023967+00:00
-- url     : https://prove2.me/submissions/0bfb5681-3ae1-44e7-b5bb-cfcf62037236

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_op_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_le_valS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
private theorem flt_cost_false_eq_covDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    flt_cost LL S false al = (covDeg LL S al : ℤ) := by
  simp only [flt_cost, Finsupp.liftAddHom_apply, covDeg, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp
private theorem flt_cost_true_eq_vecDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) :
    flt_cost LL S true al = (vecDeg LL S al : ℤ) := by
  simp only [flt_cost, Finsupp.liftAddHom_apply, vecDeg, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {t : ℤ} (ht : (t : WithTop ℤ) ≤ valS LL S F) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    twistSub LL S (lastIdx n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F (t - N) := by
  have hF := (flt_le_valS LL S F t).1 ht
  have hm := flt_op_mem LL S (lastIdx n) (Or.inl ⟨rfl, rfl⟩ : flt_compat 1 false) hF al be
  refine (laurentCoeffFiltration R n (ι × Fin n) 1).anti ?_ hm
  simp only [Bool.not_false, flt_cost_false_eq_covDeg, flt_cost_true_eq_vecDeg]
  have hN' : ((covDeg LL S al + vecDeg LL S be : ℕ) : ℤ) ≤ N := by exact_mod_cast hN
  push_cast at hN'
  linarith
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
