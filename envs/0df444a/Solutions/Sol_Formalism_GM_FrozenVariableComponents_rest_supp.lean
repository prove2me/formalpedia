-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.rest_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:34.320439+00:00
-- url     : https://prove2.me/submissions/fe942e0b-4260-4697-b8cf-d4976697698a

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_supp_X_mul_pderiv
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_top_apply
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
end Ops
section Rest
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
private theorem wt_eq_of_eq_away_from_index (LL : Formalism.GM.M.Letters N) (j : ℕ) (i : Fin N) (hij : j ≤ (i : ℕ))
    (m m0 : Fin N × Fin r →₀ ℕ) (c0 : Fin r) (h : ∀ x : Fin N × Fin r, x.1 ≠ i → m x = m0 x) :
    Formalism.GM.M.wt LL j c0 m = Formalism.GM.M.wt LL j c0 m0 := by
  unfold Formalism.GM.M.wt
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  by_cases h1 : (i' : ℕ) < j
  · have e : m (i', c0) = m0 (i', c0) := h _ (fun e => by
      have e' : (i' : ℕ) = i := congrArg Fin.val e
      omega)
    simp only [e]
  · simp [h1]
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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) (hm : m ∈ (restAct p LL j c d F).support) :
    ∃ m0 ∈ F.support, wt LL j 0 m = wt LL j 0 m0 := by
  classical
  have hsum : ∃ i : Fin N, m ∈ ((if j ≤ (i : ℕ) then top p LL i c d else 0) F).support := by
    by_contra hcon
    push Not at hcon
    apply mem_support_iff.1 hm
    unfold restAct
    rw [LinearMap.sum_apply, coeff_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h := hcon i
    rw [mem_support_iff, not_not] at h
    exact h
  obtain ⟨i, hi⟩ := hsum
  split_ifs at hi with hij
  · rw [top_apply] at hi
    split_ifs at hi with hv
    · obtain ⟨m0, hm0, hx⟩ := supp_X_mul_pderiv _ _ F m hi
      exact ⟨m0, hm0, wt_eq_of_eq_away_from_index LL j i hij m m0 0
        (fun x hx' => hx x (fun e => hx' (by rw [e])) (fun e => hx' (by rw [e])))⟩
    · rw [support_neg] at hi
      obtain ⟨m0, hm0, hx⟩ := supp_X_mul_pderiv _ _ F m hi
      exact ⟨m0, hm0, wt_eq_of_eq_away_from_index LL j i hij m m0 0
        (fun x hx' => hx x (fun e => hx' (by rw [e])) (fun e => hx' (by rw [e])))⟩
  · simp at hi
end Formalism.GM.FrozenVariableComponents
