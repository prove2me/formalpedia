-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.freeze_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:41.132898+00:00
-- url     : https://prove2.me/submissions/6d20ae63-17b5-45d8-a562-88891bff8da4

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_deg_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_hom_aeval
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_weight_row
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_weight_one__32b8ae2c834a
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_freezeSub_hom
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
private theorem fin_castSucc_ne_last (i : Fin N) : Fin.castSucc i ≠ Fin.last N :=
  (Fin.castSucc_lt_last i).ne
private theorem fin_eq_last_or_exists_castSucc (i : Fin (N + 1)) : i = Fin.last N ∨ ∃ j : Fin N, i = Fin.castSucc j := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact Or.inl rfl
  · exact Or.inr ⟨j, rfl⟩
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
private theorem isWeightedHomogeneous_of_eq_deg {τ : Type*} {w : τ → ℕ} {φ : MvPolynomial τ K} {a b : ℕ}
    (h : IsWeightedHomogeneous w φ a) (e : a = b) : IsWeightedHomogeneous w φ b := e ▸ h
private theorem isWeightedHomogeneous_one' {τ : Type*} (w : τ → ℕ) : IsWeightedHomogeneous w (1 : MvPolynomial τ K) 0 := by
  first
  | exact isWeightedHomogeneous_one w
  | exact isWeightedHomogeneous_one _ w
  | (intro d hd
     rw [coeff_one] at hd
     split_ifs at hd with h0
     · subst h0
       simp
     · exact absurd rfl hd)
private theorem isWeightedHomogeneous_pow {τ : Type*} (w : τ → ℕ) (φ : MvPolynomial τ K) (n : ℕ)
    (h : IsWeightedHomogeneous w φ n) (k : ℕ) : IsWeightedHomogeneous w (φ ^ k) (k * n) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_mul]
    exact isWeightedHomogeneous_one' w
  | succ k ih =>
    rw [pow_succ, add_one_mul]
    exact ih.mul h
private theorem isWeightedHomogeneous_X' {τ : Type*} (w : τ → ℕ) (a : τ) : IsWeightedHomogeneous w (X a : MvPolynomial τ K) (w a) := by
  first
  | exact isWeightedHomogeneous_X K w a
  | exact isWeightedHomogeneous_X w a
  | exact isWeightedHomogeneous_X _ w a
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
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (n : ℕ) (hn : LL.total ≤ n)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : f ∈ Pol p r LL) :
    freeze p LL ρ n f ∈ Pol p r (LL.snoc n) := by
  unfold Formalism.GM.M.Pol at hf ⊢
  rw [mem_restrictSupport_iff] at hf ⊢
  have hf' : ∀ m ∈ f.support, Formalism.GM.M.MultiDeg LL m := fun m hm => hf (Finset.mem_coe.2 hm)
  have key : ∀ i' : Fin (N + 1), IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => if y.1 = i' then 1 else 0)
      (Formalism.GM.M.freeze p LL ρ n f) ((LL.snoc n).deg i') := by
    intro i'
    unfold Formalism.GM.M.freeze
    rcases fin_eq_last_or_exists_castSucc i' with rfl | ⟨i0, rfl⟩
    · have hfv : IsWeightedHomogeneous (fun x : Fin N × Fin r =>
          (if Fin.castSucc x.1 = Fin.last N then 1 else 0) + (if Fin.last N = Fin.last N then 1 else 0)) f LL.total := by
        intro m hm
        have e : (fun x : Fin N × Fin r =>
            (if Fin.castSucc x.1 = Fin.last N then 1 else 0) + (if Fin.last N = Fin.last N then 1 else 0)) =
            fun _ => 1 := by
          funext x
          simp [fin_castSucc_ne_last]
        rw [e, weight_one']
        unfold Formalism.GM.M.Letters.total
        exact Finset.sum_congr rfl (fun i _ => hf' m (mem_support_iff.2 hm) i)
      have hA := hom_aeval _ _ (Formalism.GM.M.freezeSub p LL ρ)
        (fun x => freezeSub_hom p LL ρ (Fin.last N) x) f _ hfv
      have hX := isWeightedHomogeneous_pow (fun y : Fin (N + 1) × Fin r => if y.1 = Fin.last N then 1 else 0) _ _
        (isWeightedHomogeneous_X' (K := ℚ_[p]) (fun y : Fin (N + 1) × Fin r => if y.1 = Fin.last N then 1 else 0) (Fin.last N, ρ))
        (n - LL.total)
      refine isWeightedHomogeneous_of_eq_deg (hX.mul hA) ?_
      (simp [snoc_deg_last]) <;> omega
    · have hfv : IsWeightedHomogeneous (fun x : Fin N × Fin r =>
          (if Fin.castSucc x.1 = Fin.castSucc i0 then 1 else 0) +
            (if Fin.last N = Fin.castSucc i0 then 1 else 0)) f (LL.deg i0) := by
        intro m hm
        have e : (fun x : Fin N × Fin r =>
            (if Fin.castSucc x.1 = Fin.castSucc i0 then 1 else 0) +
              (if Fin.last N = Fin.castSucc i0 then 1 else 0)) =
            fun x => if x.1 = i0 then 1 else 0 := by
          funext x
          simp [(fin_castSucc_ne_last i0).symm]
        rw [e, weight_row]
        exact hf' m (mem_support_iff.2 hm) i0
      have hA := hom_aeval _ _ (Formalism.GM.M.freezeSub p LL ρ)
        (fun x => freezeSub_hom p LL ρ (Fin.castSucc i0) x) f _ hfv
      have hX := isWeightedHomogeneous_pow (fun y : Fin (N + 1) × Fin r => if y.1 = Fin.castSucc i0 then 1 else 0) _ _
        (isWeightedHomogeneous_X' (K := ℚ_[p]) (fun y : Fin (N + 1) × Fin r => if y.1 = Fin.castSucc i0 then 1 else 0) (Fin.last N, ρ))
        (n - LL.total)
      refine isWeightedHomogeneous_of_eq_deg (hX.mul hA) ?_
      (simp [snoc_deg_castSucc, (fin_castSucc_ne_last i0).symm]) <;> omega
  intro m hm
  show Formalism.GM.M.MultiDeg (LL.snoc n) m
  intro i'
  have h := key i' (mem_support_iff.1 (Finset.mem_coe.1 hm))
  rwa [weight_row] at h
end Formalism.GM.FrozenVariableComponents
