-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehw_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:30:37.425015+00:00
-- url     : https://prove2.me/submissions/d7a68a25-5622-4cdc-8938-b8962d7edb4b

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylDominanceZ
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylIntRat
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) ℚ) (hf : f ∈ dualWeyl ℚ r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by
  classical
  intro m hm k
  let N : ℕ := ∏ d ∈ f.support, (coeff d f).den
  let u : MvPolynomial (Fin r × Fin n) ℤ := ∑ d ∈ f.support,
    monomial d ((∏ d' ∈ f.support.erase d, ((coeff d' f).den : ℤ)) * (coeff d f).num)
  have hu : map (Int.castRingHom ℚ) u = (N : ℚ) • f := by
    conv_rhs => rw [f.as_sum]
    rw [Finset.smul_sum]
    simp only [u, map_sum, map_monomial, smul_monomial]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    push_cast
    have hN : (N : ℚ) = (∏ d' ∈ f.support.erase d, ((coeff d' f).den : ℚ)) * (coeff d f).den := by
      simp only [N]
      push_cast
      rw [Finset.prod_erase_mul _ _ hd]
    rw [smul_eq_mul, hN, mul_assoc, Rat.den_mul_eq_num]
    simp [eq_intCast]
  have hN0 : (N : ℚ) ≠ 0 := by
    simp only [N]
    push_cast
    exact Finset.prod_ne_zero_iff.mpr fun d _ => Nat.cast_ne_zero.mpr (coeff d f).den_nz
  have huD : u ∈ dualWeyl ℤ r n ν :=
    (dualWeylIntRat r n ν u).mpr (by rw [hu]; exact (dualWeyl ℚ r n ν).smul_mem _ hf)
  have hmu : m ∈ u.support := by
    rw [mem_support_iff]
    intro h0
    have e := congrArg (coeff m) hu
    rw [coeff_map, h0, map_zero, coeff_smul, smul_eq_mul] at e
    exact (mem_support_iff.mp hm) ((mul_eq_zero.mp e.symm).resolve_left hN0)
  exact (dualWeylDominanceZ r n ν hnr hν u huD m hmu).1 k
end Formalism.GradedWeylDivisibility
