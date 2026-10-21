-- Prove2me | solution 1 for FunctionField.ell_eq_of_deg_ge
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T14:43:49.454298+00:00
-- url     : https://prove2.me/submissions/72456d60-8a91-4661-b737-518a723fb9ba

import Mathlib
import Definitions.Def_RiemannRoch_WeilDifferentials
import Theorems.Thm_FunctionField_genus_eq_genusChart
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
namespace FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
attribute [local instance] FunctionField.instDecidableEqRatFuncCoordinateFreeDivisor
namespace Place
attribute [local instance] FunctionField.Place.finiteVspTower
attribute [local instance] FunctionField.Place.infiniteVspTower
end Place
namespace Divisor
omit [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
    [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
    [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_add (D E : Divisor k K) : deg k K (D + E) = deg k K D + deg k K E := by
  classical
  simp [deg, Finsupp.sum_add_index, add_mul]
theorem deg_equivChart (D : DivisorA k K) :
    deg k K (divisorEquivChart k K D) = Chart.deg k K D := by
  classical
  induction D using Finsupp.induction with
  | zero => simp [deg, Chart.deg, divisorEquivChart]
  | single_add a b f ha hb ih =>
      rw [map_add, deg_add, Chart.deg_add, ih]
      congr 1
      simp [deg, Chart.deg, divisorEquivChart, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_single, placeDegree_eq]
end Divisor
end FunctionField
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
omit [IsFullConstantField k K] in
theorem mem_vanishingDivisors_of_le {ω : WeilDifferential k K} {D D' : DivisorA k K}
    (hle : D' ≤ D) (hD : D ∈ vanishingDivisors ω) : D' ∈ vanishingDivisors ω := by
  intro α hα
  apply hD
  have hsub : adeleFilt k K D' + diagonalSubmodule k K ≤
      adeleFilt k K D + diagonalSubmodule k K := by
    simpa only [Submodule.add_eq_sup] using
      sup_le_sup (adeleFilt_mono k K hle) (le_refl (diagonalSubmodule k K))
  exact hsub hα
omit [IsFullConstantField k K] in
theorem add_toFun (ω η : WeilDifferential k K) :
    (ω + η).toFun = ω.toFun + η.toFun := rfl
theorem finrank_weilDifferential_eq_one :
    Module.finrank K (WeilDifferential k K) = 1 := by
  obtain ⟨D₀', hD₀'⟩ := exists_nontrivial_omega (k := k) (K := K)
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD₀'
  set ω₀ : WeilDifferential k K := ⟨φ, ⟨D₀', hφ⟩⟩ with hω₀def
  have hω₀ne : ω₀ ≠ 0 := by
    intro h
    apply hφ0
    have hval : ω₀.toFun = φ := rfl
    rw [← hval, h]; rfl
  refine (finrank_eq_one_iff_of_nonzero' ω₀ hω₀ne).mpr ?_
  intro ω
  by_contra hspan
  push Not at hspan
  have hindep : ∀ f g : K, f • ω₀ + g • ω = 0 → f = 0 ∧ g = 0 := by
    intro f g hfg
    by_cases hg : g = 0
    · subst hg
      rw [zero_smul, add_zero] at hfg
      refine ⟨?_, rfl⟩
      by_contra hf
      exact hω₀ne ((smulWeil_eq_zero_iff f hf ω₀).mp hfg)
    · exfalso
      apply hspan (g⁻¹ * (-f))
      have hgω : g • ω = (-f) • ω₀ := by
        have hneg : g • ω = -(f • ω₀) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]; exact hfg
        rw [hneg, neg_smul]
      have hω : ω = (g⁻¹ * (-f)) • ω₀ := by
        rw [mul_smul, ← hgω, ← mul_smul, inv_mul_cancel₀ hg, one_smul]
      exact hω.symm
  obtain ⟨D₁, hD₁⟩ := ω₀.vanishes_on
  obtain ⟨D₂, hD₂⟩ := ω.vanishes_on
  set D₀ : DivisorA k K := D₁ ⊓ D₂ with hD₀def
  have h₀ : D₀ ∈ vanishingDivisors ω₀ :=
    mem_vanishingDivisors_of_le inf_le_left hD₁
  have h₂ : D₀ ∈ vanishingDivisors ω :=
    mem_vanishingDivisors_of_le inf_le_right hD₂
  set B : DivisorA k K := polarDivisor k K (XK k K) with hBdef
  have hBpos : 0 < deg k K B := polar_deg_pos k K (not_algebraic_XK k K)
  have hb1 : 1 ≤ deg k K B := hBpos
  have hcount : ∀ n : ℕ,
      2 * (ell k K (n • B) : ℤ) ≤ indexOfSpecialty k K (D₀ - n • B) := by
    intro n
    set E : DivisorA k K := n • B with hEdef
    have hinj : Function.Injective
        (LinearMap.coprod (smulIntoOmega ω₀ h₀ E) (smulIntoOmega ω h₂ E)) := by
      intro x y hxy
      have hd : (LinearMap.coprod (smulIntoOmega ω₀ h₀ E)
          (smulIntoOmega ω h₂ E)) (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      rw [LinearMap.coprod_apply] at hd
      have hcoe : (smulWeil (((x - y).1 : RRspace k K E) : K) ω₀).toFun
          + (smulWeil (((x - y).2 : RRspace k K E) : K) ω).toFun = 0 := by
        have h1 := congrArg Subtype.val hd
        simpa only [Submodule.coe_add, smulIntoOmega_coe, Submodule.coe_zero] using h1
      have hsum : ((((x - y).1 : RRspace k K E) : K) • ω₀
          + (((x - y).2 : RRspace k K E) : K) • ω).toFun = 0 := by
        rw [add_toFun]; exact hcoe
      have hzero : (((x - y).1 : RRspace k K E) : K) • ω₀
          + (((x - y).2 : RRspace k K E) : K) • ω = 0 := ext hsum
      obtain ⟨hf0, hg0⟩ := hindep _ _ hzero
      have hxy0 : x - y = 0 := Prod.ext (Subtype.ext hf0) (Subtype.ext hg0)
      exact sub_eq_zero.mp hxy0
    have hfrle : Module.finrank k (RRspace k K E × RRspace k K E) ≤
        Module.finrank k (differentialSpace (k := k) (K := K) (D₀ - E)) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_prod, finrank_differentialSpace] at hfrle
    have hLfr : Module.finrank k (RRspace k K E) = ell k K E := rfl
    rw [hLfr] at hfrle
    omega
  set M : ℤ := max (deg k K D₀) (3 * (genus k K : ℤ) - 3 - deg k K D₀) with hMdef
  set n : ℕ := M.toNat + 1 with hndef
  have hn_ge : (n : ℤ) ≥ M + 1 := by
    have hself := Int.self_le_toNat M
    push_cast [hndef]
    omega
  have hn_d0 : (n : ℤ) > deg k K D₀ := by
    have hle : deg k K D₀ ≤ M := le_max_left _ _
    omega
  have hn_g : (n : ℤ) > 3 * (genus k K : ℤ) - 3 - deg k K D₀ := by
    have hle : 3 * (genus k K : ℤ) - 3 - deg k K D₀ ≤ M := le_max_right _ _
    omega
  have hnb_ge : (n : ℤ) * deg k K B ≥ (n : ℤ) := by
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    nlinarith [hb1, hn0]
  have hdegsub : deg k K (D₀ - n • B) = deg k K D₀ - (n : ℤ) * deg k K B := by
    rw [deg_sub, deg_nsmul]
  have hdeg_neg : deg k K (D₀ - n • B) < 0 := by
    rw [hdegsub]; omega
  have hℓ0 : ell k K (D₀ - n • B) = 0 := RRspace_neg_deg_ell k K hdeg_neg
  have hi := indexOfSpecialty_eq (k := k) (K := K) (D₀ - n • B)
  rw [hℓ0, hdegsub] at hi
  have hrr := riemann_ineq (k := k) (K := K) (n • B)
  rw [deg_nsmul] at hrr
  have hc := hcount n
  omega
omit [IsFullConstantField k K] in
theorem add_principal_mem_vanishingDivisors_smul_iff (x : Kˣ)
    (ω : WeilDifferential k K) (D : DivisorA k K) :
    D + principalDivisorA k K (Additive.ofMul x) ∈
        vanishingDivisors ((x : K) • ω) ↔
      D ∈ vanishingDivisors ω := by
  constructor
  · intro h a ha
    let P := principalDivisorA k K (Additive.ofMul x)
    have hsource :
        (D + P) + principalDivisorA k K (Additive.ofMul (x⁻¹ : Kˣ)) = D := by
      have hinv : Additive.ofMul (x⁻¹ : Kˣ) = -(Additive.ofMul x) := rfl
      rw [hinv, map_neg]
      abel
    have haSource : a ∈ adeleFilt k K
          ((D + P) + principalDivisorA k K (Additive.ofMul (x⁻¹ : Kˣ))) +
          diagonalSubmodule k K := by
      simpa only [hsource] using ha
    have ha' := mul_mem_adeleFilt_add_diagonal (k := k) (K := K)
      (x⁻¹ : Kˣ) (D + P) haSource
    have hz := h (((x⁻¹ : Kˣ) : K) • a) ha'
    change (smulWeil (x : K) ω).toFun (((x⁻¹ : Kˣ) : K) • a) = 0 at hz
    rw [smulWeil_toFun_apply] at hz
    simpa [mul_smul] using hz
  · intro h a ha
    change (smulWeil (x : K) ω).toFun a = 0
    rw [smulWeil_toFun_apply]
    exact h _ (mul_mem_adeleFilt_add_diagonal (k := k) (K := K) x D ha)
end WeilDifferential
open WeilDifferential in
theorem duality {W : DivisorA k K} (hW : IsCanonical k K W) (D : DivisorA k K) :
    ell k K (W - D) = indexOfSpecialty k K D := by
  obtain ⟨ω₀, hω₀, hdivW⟩ := hW
  have hω₀' : ω₀.toFun ≠ 0 := hω₀
  have hω₀ne : ω₀ ≠ 0 := fun h => hω₀ (by rw [h]; rfl)
  have hWspec : W ∈ vanishingDivisors ω₀ ∧
      ∀ D' ∈ vanishingDivisors ω₀, D' ≤ W := by
    have h := (Classical.choose_spec
      (WeilDifferential.exists_max_vanishingDivisor (k := k) (K := K) hω₀)).1
    have he : Classical.choose
        (WeilDifferential.exists_max_vanishingDivisor (k := k) (K := K) hω₀) = W := hdivW
    rw [he] at h
    exact h
  obtain ⟨hWmem, hWmax⟩ := hWspec
  have hWD : W - (W - D) = D := sub_sub_cancel W D
  set μ := smulIntoOmega ω₀ hWmem (W - D) with hμdef
  have hμinj : Function.Injective μ := smulIntoOmega_injective ω₀ hWmem (W - D) hω₀'
  have hμsurj : Function.Surjective μ := by
    intro ψ
    set φ : AdeleSpace k K →ₗ[k] k := (ψ : AdeleSpace k K →ₗ[k] k) with hφdef
    by_cases hψ0 : φ = 0
    · exact ⟨0, by rw [map_zero]; exact (Subtype.ext hψ0).symm⟩
    ·
      have hψmem : ∀ α ∈ adeleFilt k K D + diagonalSubmodule k K, φ α = 0 := by
        have hp : ∀ α ∈ adeleFilt k K (W - (W - D)) + diagonalSubmodule k K, φ α = 0 :=
          ψ.property
        rw [hWD] at hp
        exact hp
      set η : WeilDifferential k K := ⟨φ, ⟨D, hψmem⟩⟩ with hηdef
      have hηnt : η.toFun ≠ 0 := hψ0
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := K)
        (WeilDifferential.finrank_weilDifferential_eq_one (k := k) (K := K)) hω₀ne η
      have hc0 : c ≠ 0 := by
        intro h
        subst h
        apply hηnt
        have hη0 : η = 0 := by rw [← hc, zero_smul]
        rw [hη0]; rfl
      set cu : Kˣ := Units.mk0 c hc0 with hcudef
      set P : DivisorA k K := principalDivisorA k K (Additive.ofMul cu) with hPdef
      have hDmem : D ∈ vanishingDivisors ((cu : K) • ω₀) := by
        have hcω : (cu : K) • ω₀ = η := by
          rw [Units.val_mk0]; exact hc
        rw [hcω]
        intro α hα
        exact hψmem α hα
      have hDPmem : D - P ∈ vanishingDivisors ω₀ := by
        apply (add_principal_mem_vanishingDivisors_smul_iff (k := k) (K := K) cu ω₀ (D - P)).1
        have hsub : (D - P) + P = D := by rw [hPdef]; abel
        rw [hsub]; exact hDmem
      have hDPle : D - P ≤ W := hWmax (D - P) hDPmem
      have hcmem : memRRspace k K (W - D) c := by
        intro v
        have hval := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul cu) v
        change placeValuation k K v c ≤ WithZero.exp ((W - D) v)
        have hcv : placeValuation k K v c =
            WithZero.exp (-(P v)) := by
          rw [hPdef]
          have hcuc : (cu : K) = c := by simp [hcudef]
          rw [← hcuc]; exact hval
        rw [hcv]
        apply WithZero.exp_le_exp.mpr
        have hlev := hDPle v
        simp only [Finsupp.sub_apply] at hlev ⊢
        omega
      refine ⟨⟨c, (mem_RRspace_iff k K (W - D) c).mpr hcmem⟩, ?_⟩
      apply Subtype.ext
      rw [hμdef, smulIntoOmega_coe]
      change ((c : K) • ω₀).toFun = φ
      rw [hc]
  have hfr : Module.finrank k (RRspace k K (W - D)) =
      Module.finrank k (differentialSpace (k := k) (K := K) (W - (W - D))) :=
    (LinearEquiv.ofBijective μ ⟨hμinj, hμsurj⟩).finrank_eq
  show Module.finrank k (RRspace k K (W - D)) = indexOfSpecialty k K D
  rw [hfr, hWD, finrank_differentialSpace]
theorem indexOfSpecialty_eq_ell_sub {W : DivisorA k K} (hW : IsCanonical k K W) (D : DivisorA k K) :
    (indexOfSpecialty k K D : ℤ) = ell k K (W - D) := by
  exact_mod_cast (duality k K hW D).symm
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
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
theorem riemann_roch {W : DivisorA k K} (hW : IsCanonical k K W) (D : DivisorA k K) :
    (ell k K D : ℤ) = deg k K D + 1 - (genus k K : ℤ) + ell k K (W - D) := by
  have hi := indexOfSpecialty_eq k K D
  have hdual := indexOfSpecialty_eq_ell_sub k K hW D
  omega
end FunctionField.Chart
end
end
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
section Canonical
variable {W : DivisorA k K} (hW : IsCanonical k K W)
include hW
theorem ell_canonical : ell k K W = genus k K := by
  have hRR := riemann_roch k K hW (0 : DivisorA k K)
  rw [ell_zero k K, deg_zero, zero_add, sub_zero] at hRR
  omega
theorem deg_canonical : deg k K W = 2 * (genus k K : ℤ) - 2 := by
  have hRR := riemann_roch k K hW W
  rw [sub_self, ell_zero k K, ell_canonical k K hW] at hRR
  omega
theorem ell_eq_of_deg_ge (D : DivisorA k K) (hdeg : deg k K D ≥ 2 * (genus k K : ℤ) - 1) :
    (ell k K D : ℤ) = deg k K D + 1 - (genus k K : ℤ) := by
  have hcanonical := deg_canonical k K hW
  have hneg : deg k K (W - D) < 0 := by
    rw [deg_sub, hcanonical]
    omega
  have hell := RRspace_neg_deg_ell k K hneg
  rw [riemann_roch k K hW D, hell, Int.ofNat_zero, add_zero]
end Canonical
end FunctionField.Chart
end
end
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
namespace memRRspace
variable {k K} {D : Divisor k K}
end memRRspace
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
omit [IsFullConstantField k K] in
theorem memRRspace_equivChart (D : Divisor k K) (f : K) :
    memRRspace k K D f ↔
      Chart.memRRspace k K ((divisorEquivChart k K).symm D) f := by
  constructor
  · intro hf w
    have hv := hf (chartToPlace k K w)
    rw [placeValuation_eq] at hv
    simpa [divisorEquivChart, Finsupp.domCongr_apply] using hv
  · intro hf v
    let w := (chartToPlace k K).symm v
    have hw := hf w
    rw [← placeValuation_eq] at hw
    simpa [w, divisorEquivChart, Finsupp.domCongr_apply] using hw
omit [IsFullConstantField k K] in
theorem RRspace_eq_chart (D : Divisor k K) :
    RRspace k K D = Chart.RRspace k K ((divisorEquivChart k K).symm D) := by
  ext f
  exact memRRspace_equivChart k K D f
omit [IsFullConstantField k K] in
theorem ell_eq_chart (D : Divisor k K) :
    ell k K D = Chart.ell k K ((divisorEquivChart k K).symm D) := by
  rw [ell, Chart.ell, RRspace_eq_chart k K D]
omit [IsFullConstantField k K] in
@[simp]
theorem Divisor.chart_deg (D : Divisor k K) :
    Chart.deg k K ((divisorEquivChart k K).symm D) = D.deg := by
  have h := Divisor.deg_equivChart k K ((divisorEquivChart k K).symm D)
  simpa using h.symm
section Canonical
variable {W : Divisor k K} (hW : IsCanonical k K W)
include hW
end Canonical
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
variable {W : Divisor k K} (hW : IsCanonical k K W)
include hW
namespace FunctionField
theorem _root_.solution (D : Divisor k K)
    (hdeg : D.deg ≥ 2 * (genus k K : ℤ) - 1) :
    (ell k K D : ℤ) = D.deg + 1 - (genus k K : ℤ) := by
  have hW' := (isCanonical_iff_chart k K W).mp hW
  have hdeg' : Chart.deg k K ((divisorEquivChart k K).symm D) ≥
      2 * (Chart.genus k K : ℤ) - 1 := by simpa [genus_eq_genusChart] using hdeg
  rw [ell_eq_chart]
  simpa [genus_eq_genusChart] using
    Chart.ell_eq_of_deg_ge k K hW' ((divisorEquivChart k K).symm D) hdeg'
end FunctionField
