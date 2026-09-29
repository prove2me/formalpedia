-- Prove2me | solution 1 for CerednikDrinfeld.vdet_unitsMap_eq_padicValRat_nrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/639b69ae-9612-5106-8036-0ab29313b6db

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_ValuationSubring_valuation_ratCast_eq_one_iff_padicValRat_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_vdet_unitsMap_eq_padicValRat_nrd

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega ValuationSubring QuaternionAlgebra IsDedekindDomain

namespace DETNRD42

section generic

variable {K : Type} [Field K] [CharZero K] [Algebra ℚ K]

theorem ratSmul_eq (r : ℚ) (M : Matrix (Fin 2) (Fin 2) K) : r • M = (r : K) • M := by
  rw [← algebraMap_smul K r M, eq_ratCast]

theorem algHom_coe {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K) (r : ℚ) :
    ι ((r : ℚ) : ℍ[ℚ, a, b]) = (r : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h : ((r : ℚ) : ℍ[ℚ, a, b]) = algebraMap ℚ ℍ[ℚ, a, b] r :=
    (congrFun QuaternionAlgebra.coe_algebraMap r).symm
  rw [h, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, ratSmul_eq]

theorem trd_add' {a b : ℚ} (x y : ℍ[ℚ, a, b]) : trd (x + y) = trd x + trd y := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.trd_mk]
  ring

theorem quad {a b : ℚ} (x : ℍ[ℚ, a, b]) :
    x * x - ((trd x : ℚ) : ℍ[ℚ, a, b]) * x + ((nrd x : ℚ) : ℍ[ℚ, a, b]) = 0 := by
  rw [← QuaternionAlgebra.add_star_eq_coe_trd, ← QuaternionAlgebra.star_mul_eq_coe_nrd x, add_mul]
  abel

theorem cayleyHamilton (M : Matrix (Fin 2) (Fin 2) K) :
    M * M - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem key_identity {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K) (y : ℍ[ℚ, a, b]) :
    ((ι y).trace - ((trd y : ℚ) : K)) • ι y =
      ((ι y).det - ((nrd y : ℚ) : K)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h1 : ι y * ι y - ((trd y : ℚ) : K) • ι y +
      ((nrd y : ℚ) : K) • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
    have h := congrArg ι (quad y)
    rw [map_add, map_sub, map_mul, map_mul, algHom_coe, algHom_coe, map_zero, smul_one_mul] at h
    exact h
  have h2 := cayleyHamilton (ι y)
  have h := sub_eq_zero.2 (h2.trans h1.symm)
  have e : ι y * ι y - (ι y).trace • ι y + (ι y).det • (1 : Matrix (Fin 2) (Fin 2) K) -
      (ι y * ι y - ((trd y : ℚ) : K) • ι y + ((nrd y : ℚ) : K) • 1) =
      -((ι y).trace • ι y - ((trd y : ℚ) : K) • ι y) +
        ((ι y).det • 1 - ((nrd y : ℚ) : K) • 1) := by abel
  rw [e] at h
  rw [sub_smul, sub_smul]
  exact neg_add_eq_zero.1 h

theorem det_eq_nrd {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K)
    (hι : Function.Injective ι) (x : ℍ[ℚ, a, b]) :
    (ι x).det = ((nrd x : ℚ) : K) := by
  by_cases htr : (ι x).trace - ((trd x : ℚ) : K) = 0
  · have h3 := key_identity ι x
    rw [htr, zero_smul] at h3
    have h00 := congrFun (congrFun h3 0) 0
    simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    exact (sub_eq_zero.mp h00.symm)
  · exfalso

    have scal : ∀ y : ℍ[ℚ, a, b], (ι y).trace - ((trd y : ℚ) : K) ≠ 0 →
        ∃ c : K, ι y = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
      intro y hy
      have h3 := key_identity ι y
      have h := congrArg (fun M => ((ι y).trace - ((trd y : ℚ) : K))⁻¹ • M) h3
      simp only [smul_smul, inv_mul_cancel₀ hy, one_smul] at h
      exact ⟨_, h⟩

    have hall : ∀ y : ℍ[ℚ, a, b], ∃ c : K, ι y = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
      intro y
      by_cases hy : (ι y).trace - ((trd y : ℚ) : K) = 0
      · have hxy : (ι (x + y)).trace - ((trd (x + y) : ℚ) : K) ≠ 0 := by
          rw [map_add, Matrix.trace_add, trd_add', Rat.cast_add]
          intro h
          apply htr
          linear_combination h - hy
        obtain ⟨c, hc⟩ := scal (x + y) hxy
        obtain ⟨c', hc'⟩ := scal x htr
        refine ⟨c - c', ?_⟩
        rw [sub_smul, ← hc, ← hc', map_add, add_sub_cancel_left]
      · exact scal y hy
    obtain ⟨ci, hci⟩ := hall ⟨0, 1, 0, 0⟩
    obtain ⟨cj, hcj⟩ := hall ⟨0, 0, 1, 0⟩
    have hcomm : ι ((⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩) =
        ι ((⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 1, 0, 0⟩) := by
      rw [map_mul, map_mul, hci, hcj, smul_one_mul, smul_one_mul, smul_smul, smul_smul, mul_comm]
    have hk := congrArg QuaternionAlgebra.imK (hι hcomm)
    simp only [QuaternionAlgebra.mk_mul_mk] at hk
    norm_num at hk

end generic

theorem padicValRat_self_zpow (q : ℕ) [hq : Fact q.Prime] (m : ℤ) :
    padicValRat q ((q : ℚ) ^ m) = m := by
  have h1 : 1 < q := hq.out.one_lt
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, padicValRat.pow _, padicValRat.self h1, mul_one]
  · rw [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow _, padicValRat.self h1, mul_one]

theorem v_algebraMap_ratCast (A : ValuationSubring (AlgebraicClosure ℚ)) (s : ℚ) :
    Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion ((s : ℚ) : ↥(ratClosure A))) =
      A.valuation ((s : ℚ) : AlgebraicClosure ℚ) := by
  rw [map_ratCast]
  have h1 : ((s : ℚ) : A.valuation.Completion) =
      ((s : WithVal A.valuation) : A.valuation.Completion) :=
    (map_ratCast (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)) s).symm
  rw [h1, Valued.valuedCompletion_apply]
  show A.valuation (WithVal.equiv A.valuation (s : WithVal A.valuation)) = _
  rw [map_ratCast]

theorem main
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (𝒪₀ : Type) [CommRing 𝒪₀] [Algebra 𝒪₀ ↥(ratClosure A)] [IsFractionRing 𝒪₀ ↥(ratClosure A)] (π : 𝒪₀)
    (hπq : algebraMap 𝒪₀ ↥(ratClosure A) π = ((q : ℕ) : ↥(ratClosure A)))
    (h𝒪₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap 𝒪₀ ↥(ratClosure A)) ↔ Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ↥(ratClosure A) →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ↥(ratClosure A)) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪₀ˣ, (Matrix.GeneralLinearGroup.det g : ↥(ratClosure A)) = algebraMap 𝒪₀ ↥(ratClosure A) (u : 𝒪₀) * (algebraMap 𝒪₀ ↥(ratClosure A) π) ^ n)
    {a₁ b₁ : ℚ} (ι : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) (hι : Function.Injective ι)
    (x : (ℍ[ℚ, a₁, b₁])ˣ) :
    vdet (Units.map (ι : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x) =
      Multiplicative.ofAdd (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))) := by
  have hq : q.Prime := Fact.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqK : ((q : ℕ) : ↥(ratClosure A)) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [hvdet]

  have hdet : (ι (x : ℍ[ℚ, a₁, b₁])).det = ((nrd (x : ℍ[ℚ, a₁, b₁]) : ℚ) : ↥(ratClosure A)) :=
    det_eq_nrd ι hι _
  have hr0 : nrd (x : ℍ[ℚ, a₁, b₁]) ≠ 0 := by
    intro h
    have hu : IsUnit (ι (x : ℍ[ℚ, a₁, b₁])) := by
      have := (Units.map (ι : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x).isUnit
      rwa [Units.coe_map] at this
    have hu' := (Matrix.isUnit_iff_isUnit_det _).mp hu
    rw [hdet, h, Rat.cast_zero] at hu'
    exact not_isUnit_zero hu'
  set r : ℚ := nrd (x : ℍ[ℚ, a₁, b₁]) with hr
  set n : ℤ := padicValRat q r with hn
  set u₀ : ℚ := r * (q : ℚ) ^ (-n) with hu₀
  have hu₀0 : u₀ ≠ 0 := mul_ne_zero hr0 (zpow_ne_zero _ hq0)
  have hval : padicValRat q u₀ = 0 := by
    rw [hu₀, padicValRat.mul hr0 (zpow_ne_zero _ hq0), padicValRat_self_zpow, ← hn]; ring

  have hA' : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
  have hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 :=
    (A.mem_nonunits_iff).mp hA'
  have hv1 : A.valuation ((u₀ : ℚ) : AlgebraicClosure ℚ) = 1 :=
    (ValuationSubring.valuation_ratCast_eq_one_iff_padicValRat_eq_zero A hq hq1 hu₀0).mpr hval
  have hv1' : A.valuation ((u₀⁻¹ : ℚ) : AlgebraicClosure ℚ) = 1 := by
    rw [Rat.cast_inv, map_inv₀, hv1, inv_one]

  obtain ⟨y, hy⟩ : ((u₀ : ℚ) : ↥(ratClosure A)) ∈ Set.range (algebraMap 𝒪₀ ↥(ratClosure A)) :=
    (h𝒪₀ _).mpr (by rw [v_algebraMap_ratCast, hv1])
  obtain ⟨y', hy'⟩ : ((u₀⁻¹ : ℚ) : ↥(ratClosure A)) ∈ Set.range (algebraMap 𝒪₀ ↥(ratClosure A)) :=
    (h𝒪₀ _).mpr (by rw [v_algebraMap_ratCast, hv1'])
  have hyy' : y * y' = 1 := by
    apply IsFractionRing.injective 𝒪₀ ↥(ratClosure A)
    rw [map_mul, hy, hy', map_one, ← Rat.cast_mul, mul_inv_cancel₀ hu₀0, Rat.cast_one]
  refine ⟨Units.mkOfMulEqOne y y' hyy', ?_⟩
  rw [Units.val_mkOfMulEqOne, hy, hπq, Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map,
    MonoidHom.coe_coe, hdet, hu₀, Rat.cast_mul, Rat.cast_zpow, Rat.cast_natCast, zpow_neg,
    inv_mul_cancel_right₀ (zpow_ne_zero n hqK)]

end DETNRD42

theorem solution
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (𝒪₀ : Type) [CommRing 𝒪₀] [Algebra 𝒪₀ ↥(ratClosure A)] [IsFractionRing 𝒪₀ ↥(ratClosure A)] (π : 𝒪₀)
    (hπq : algebraMap 𝒪₀ ↥(ratClosure A) π = ((q : ℕ) : ↥(ratClosure A)))
    (h𝒪₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap 𝒪₀ ↥(ratClosure A)) ↔ Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ↥(ratClosure A) →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ↥(ratClosure A)) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪₀ˣ, (Matrix.GeneralLinearGroup.det g : ↥(ratClosure A)) = algebraMap 𝒪₀ ↥(ratClosure A) (u : 𝒪₀) * (algebraMap 𝒪₀ ↥(ratClosure A) π) ^ n)
    {a₁ b₁ : ℚ} (ι : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) (hι : Function.Injective ι)
    (x : (ℍ[ℚ, a₁, b₁])ˣ) :
    vdet (Units.map (ι : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x) =
      Multiplicative.ofAdd (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))) :=
  DETNRD42.main q A hA 𝒪₀ π hπq h𝒪₀ vdet hvdet ι hι x

end S_CerednikDrinfeld_vdet_unitsMap_eq_padicValRat_nrd
end P2MW
export P2MW.S_CerednikDrinfeld_vdet_unitsMap_eq_padicValRat_nrd (solution)
