-- Prove2me | solution 1 for FunctionField.exists_isCanonical
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T14:33:42.783982+00:00
-- url     : https://prove2.me/submissions/6778b6df-a096-424f-a7b1-ddd796065f1f

import Mathlib
import Definitions.Def_RiemannRoch_WeilDifferentials
/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/
set_option linter.style.haveILetI false
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
attribute [local instance] FunctionField.Chart.instDecidableEqRatFuncRRspace
namespace memRRspace
variable {D : DivisorA k K}
end memRRspace
theorem RRspace_neg_deg_ell {D : DivisorA k K} (h : deg k K D < 0) : ell k K D = 0 := by
  show Module.finrank k (RRspace k K D) = 0
  rw [RRspace_neg_deg k K h]
  exact finrank_bot k K
end FunctionField.Chart
end
end
end
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
variable [IsFullConstantField k K]
attribute [local instance] FunctionField.Chart.instDecidableEqRatFuncGenus
section RiemannFamily
end RiemannFamily
section PolarDivisor
omit [IsFullConstantField k K] in
theorem polar_deg_pos {x : K} (hx : ¬IsAlgebraic k x) :
    0 < deg k K (polarDivisor k K x) := by
  by_cases hx0 : x = 0
  · subst hx0
    exact absurd isAlgebraic_zero hx
  · exact polarDivisor_pos k K hx0 hx
end PolarDivisor
section RatFunc
end RatFunc
end FunctionField.Chart
end
end
end
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
variable [IsFullConstantField k K]
attribute [local instance] FunctionField.Chart.instDecidableEqRatFuncWeil
attribute [local instance] adeleFiltAddCommGroup adeleFiltModule
namespace WeilDifferential
variable {k K}
theorem exists_nontrivial_omega :
    ∃ D : DivisorA k K, differentialSpace D ≠ ⊥ := by
  letI : IsScalarTower k k⟮X⟯ K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k k[X] K,
        IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K,
        ← IsScalarTower.algebraMap_apply k k[X] k⟮X⟯]
  let x : K := algebraMap k⟮X⟯ K (RatFunc.X : k⟮X⟯)
  have hx : ¬IsAlgebraic k x := by
    exact (transcendental_algebraMap_iff (algebraMap k⟮X⟯ K).injective).2
      RatFunc.transcendental_X
  let E : DivisorA k K := polarDivisor k K x
  let D : DivisorA k K := -(E + E)
  have hE : 0 < deg k K E := polar_deg_pos k K hx
  have hD : deg k K D < 0 := by
    simp only [D, deg_neg, deg_add]
    omega
  have hℓ : ell k K D = 0 := RRspace_neg_deg_ell k K hD
  have hi := indexOfSpecialty_eq k K D
  have hindex : 0 < indexOfSpecialty k K D := by
    have hg : 0 ≤ (genus k K : ℤ) := Int.natCast_nonneg _
    have hdegD : deg k K D = -(deg k K E + deg k K E) := by
      simp only [D, deg_neg, deg_add]
    rw [hℓ, hdegD] at hi
    exact_mod_cast (show (0 : ℤ) < (indexOfSpecialty k K D : ℤ) by omega)
  refine ⟨D, fun hbot => ?_⟩
  have hfin : 0 < Module.finrank k (differentialSpace D) := by
    rw [finrank_differentialSpace]
    exact hindex
  rw [hbot, finrank_bot] at hfin
  omega
end WeilDifferential
theorem exists_isCanonical : ∃ W : DivisorA k K, IsCanonical k K W := by
  obtain ⟨D, hD⟩ := WeilDifferential.exists_nontrivial_omega (k := k) (K := K)
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  let ω : WeilDifferential k K := ⟨φ, ⟨D, hφ⟩⟩
  have hω : WeilDifferential.IsNonzero ω := hφ0
  exact ⟨WeilDifferential.divOmega ω hω, ω, hω, rfl⟩
end FunctionField.Chart
end
end
end
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
namespace WeilDifferential
variable {k K}
end WeilDifferential
theorem isCanonical_iff_chart (W : Divisor k K) :
    IsCanonical k K W ↔
      Chart.IsCanonical k K ((divisorEquivChart k K).symm W) := by
  constructor
  · rintro ⟨omega, homega, rfl⟩
    refine ⟨WeilDifferential.toChart omega,
      (WeilDifferential.isNonzero_toChart omega).mp homega, ?_⟩
    simp [WeilDifferential.divOmega]
  · rintro ⟨omega, homega, hdiv⟩
    let eta := WeilDifferential.ofChart omega
    have hetaChart : WeilDifferential.toChart eta = omega :=
      (WeilDifferential.weilDifferentialAddEquivChart
        (k := k) (K := K)).apply_symm_apply omega
    have heta : WeilDifferential.IsNonzero eta := by
      apply (WeilDifferential.isNonzero_toChart eta).mpr
      rw [hetaChart]
      exact homega
    refine ⟨eta, heta, ?_⟩
    apply (divisorEquivChart k K).symm.injective
    simp only [WeilDifferential.divOmega, AddEquiv.symm_apply_apply]
    simpa only [hetaChart] using hdiv
end FunctionField
end
end
end
open scoped nonZeroDivisors Polynomial RatFunc WithZero
open FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
namespace FunctionField
theorem _root_.solution : ∃ W : Divisor k K, IsCanonical k K W := by
  obtain ⟨W, hW⟩ := Chart.exists_isCanonical k K
  refine ⟨divisorEquivChart k K W, ?_⟩
  apply (isCanonical_iff_chart k K _).mpr
  simpa using hW
end FunctionField
