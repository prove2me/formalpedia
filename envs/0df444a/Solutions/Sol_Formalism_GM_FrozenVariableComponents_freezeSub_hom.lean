-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.freezeSub_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:07.389804+00:00
-- url     : https://prove2.me/submissions/198516cd-f76b-402b-9370-7862cb872758

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_freezeSub_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_hX2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
private theorem isWeightedHomogeneous_finset_sum {τ ι : Type*} {w : τ → ℕ} (s : Finset ι) (φ : ι → MvPolynomial τ K) {n : ℕ}
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) n) : IsWeightedHomogeneous w (∑ i ∈ s, φ i) n := by
  intro d hd
  rw [coeff_sum] at hd
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  exact h i hi hne
private theorem isWeightedHomogeneous_sub {τ : Type*} {w : τ → ℕ} {φ ψ : MvPolynomial τ K} {n : ℕ}
    (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ - ψ) n := by
  intro d hd
  rw [coeff_sub] at hd
  by_cases h1 : coeff d φ = 0
  · rw [h1, zero_sub, neg_ne_zero] at hd
    exact hψ hd
  · exact hφ h1
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
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (i' : Fin (N + 1)) (x : Fin N × Fin r) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => if y.1 = i' then 1 else 0) (freezeSub p LL ρ x)
      ((if Fin.castSucc x.1 = i' then 1 else 0) + (if Fin.last N = i' then 1 else 0)) := by
  obtain ⟨i, c⟩ := x
  rw [freezeSub_apply]
  by_cases hv : LL.vec i = true <;> by_cases hc : c = ρ
  · rw [if_pos hv, if_pos hc]
    exact isWeightedHomogeneous_finset_sum _ _ (fun c' _ => hX2 p _ _ _ _ (by rfl))
  · rw [if_pos hv, if_neg hc]
    exact hX2 p _ _ _ _ (by exact add_comm _ _)
  · rw [if_neg hv, if_pos hc]
    exact hX2 p _ _ _ _ (by exact add_comm _ _)
  · rw [if_neg hv, if_neg hc]
    exact isWeightedHomogeneous_sub (hX2 p _ _ _ _ (by exact add_comm _ _))
      (hX2 p _ _ _ _ (by rfl))
end Formalism.GM.FrozenVariableComponents
