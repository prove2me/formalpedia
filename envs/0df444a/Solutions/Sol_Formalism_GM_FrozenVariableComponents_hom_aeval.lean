-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.hom_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:07.985825+00:00
-- url     : https://prove2.me/submissions/56537af8-691d-4e2e-85f1-848984d7cad6

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
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
private theorem isWeightedHomogeneous_finset_prod {τ ι : Type*} (w : τ → ℕ) (s : Finset ι) (φ : ι → MvPolynomial τ K) (n : ι → ℕ)
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) (n i)) :
    IsWeightedHomogeneous w (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact isWeightedHomogeneous_one' w
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
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
variable {K : Type*} [CommRing K]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution {σ τ : Type*} (w : τ → ℕ) (v : σ → ℕ) (g : σ → MvPolynomial τ K)
    (hg : ∀ x, IsWeightedHomogeneous w (g x) (v x)) (f : MvPolynomial σ K) (d : ℕ)
    (hf : IsWeightedHomogeneous v f d) : IsWeightedHomogeneous w (aeval g f) d := by
  classical
  rw [f.as_sum, map_sum]
  refine isWeightedHomogeneous_finset_sum _ _ (fun m hm => ?_)
  show IsWeightedHomogeneous w (aeval g (monomial m (coeff m f))) d
  have hmd : Finsupp.weight v m = d := hf (mem_support_iff.1 hm)
  have h1 := (isWeightedHomogeneous_C w (coeff m f)).mul
    (isWeightedHomogeneous_finset_prod w m.support (fun x => g x ^ m x) (fun x => m x * v x) (fun x _ => isWeightedHomogeneous_pow w (g x) (v x) (hg x) (m x)))
  have e : 0 + ∑ x ∈ m.support, m x * v x = d := by
    first
    | (rw [zero_add, ← hmd, Finsupp.weight_apply, Finsupp.sum]; simp only [smul_eq_mul])
    | simp [← hmd, Finsupp.weight_apply, Finsupp.sum]
  rw [aeval_monomial, Finsupp.prod]
  exact isWeightedHomogeneous_of_eq_deg h1 e
end Formalism.GM.FrozenVariableComponents
