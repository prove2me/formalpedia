-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.op_hc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:26.68819+00:00
-- url     : https://prove2.me/submissions/cb2fa1a9-6b55-41d7-9c3c-a4f565b44db7

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_X_mul_monomial__a165fb611689
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
section
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
section Parts
variable {N r : ℕ}
end Parts
section Coeff
variable {K : Type*} [CommRing K] {N r : ℕ}
end Coeff
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
section Coeff2
variable {K : Type*} [CommRing K] {N r : ℕ}
end Coeff2
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Gl
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
end Gl
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Ops
variable {K : Type*} [CommRing K] {σ : Type*}
private theorem homogeneousComponent_monomial_eq_ite (t : ℕ) (u : σ →₀ ℕ) (a : K) :
    homogeneousComponent t (monomial u a : MvPolynomial σ K) = if t = u.degree then monomial u a else 0 := by
  exact homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial a rfl))
private theorem degree_add_single_one_eq (s : σ →₀ ℕ) (x y : σ) :
    (s + Finsupp.single x 1).degree = (s + Finsupp.single y 1).degree := by
  first
  | simp [Finsupp.degree_add, Finsupp.degree_single]
  | simp [map_add]
end Ops
section Rest
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
end Rest
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Freeze
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end Freeze
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Base
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
end Base
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Pol
variable {K : Type*} [CommRing K]
end Pol
section Pol2
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end Pol2
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.FrozenVariableComponents
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable {K : Type*} [CommRing K] {σ : Type*}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (x y : σ) (t : ℕ) (F : MvPolynomial σ K) :
    homogeneousComponent t (X x * pderiv y F) = X x * pderiv y (homogeneousComponent t F) := by
  classical
  refine MvPolynomial.induction_on' F (fun s c => ?_) (fun p q hp hq => ?_)
  · by_cases hs : s y = 0
    · have h0 : pderiv y (monomial s c : MvPolynomial σ K) = 0 := by
        rw [pderiv_monomial, hs]
        simp
      rw [h0, mul_zero, map_zero, homogeneousComponent_monomial_eq_ite]
      split_ifs
      · rw [h0, mul_zero]
      · simp
    · obtain ⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single y 1 :=
        ⟨s - Finsupp.single y 1,
          (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hs))).symm⟩
      rw [pderiv_monomial, add_tsub_cancel_right, X_mul_monomial', homogeneousComponent_monomial_eq_ite,
        homogeneousComponent_monomial_eq_ite, degree_add_single_one_eq s' x y]
      split_ifs
      · rw [pderiv_monomial, add_tsub_cancel_right, X_mul_monomial']
      · simp
  · simp only [map_add, mul_add, hp, hq]
end Formalism.GM.FrozenVariableComponents
