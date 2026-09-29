-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.atkinLehner_relations_levelGroups_place
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ac5c145d-18ae-5a5c-99d8-42385ef1cfe3

import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Theorems.Thm_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_finiteIdeleDiagonal_eq_inf_map_conj
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_atkinLehner_relations_levelGroups_place
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

namespace ALRel21

variable {a b : ℚ}

local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open CerednikDrinfeld.CosetGraph

theorem exists_natCast_smul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (x : ℍ[ℚ, a, b]) :
    ∃ D : ℕ, D ≠ 0 ∧ ((D : ℤ) • x) ∈ Λ := by
  have hx : x ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) := by rw [hΛ.spanTop]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [Nat.cast_one, one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨D, hD, hyD⟩ := hy
    obtain ⟨E, hE, hzE⟩ := hz
    refine ⟨D * E, Nat.mul_ne_zero hD hE, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine add_mem ?_ ?_
    · rw [mul_comm, ← smul_smul]; exact Submodule.smul_mem _ _ hyD
    · rw [← smul_smul]; exact Submodule.smul_mem _ _ hzE
  | smul c y _ hy =>
    obtain ⟨D, hD, hyD⟩ := hy
    refine ⟨c.den * D, Nat.mul_ne_zero c.den_nz hD, ?_⟩
    have e : ((c.den * D : ℕ) : ℤ) • (c • y) = c.num • ((D : ℤ) • y) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ c.num, ← Int.cast_smul_eq_zsmul ℚ (D : ℤ), smul_smul, smul_smul]
      congr 1
      push_cast
      rw [mul_assoc, mul_comm (D : ℚ) c, ← mul_assoc, Rat.den_mul_eq_num]
    rw [e]
    exact Submodule.smul_mem _ _ hyD

theorem nrd_smul (c : ℚ) (x : ℍ[ℚ, a, b]) : QuaternionAlgebra.nrd (c • x) = c ^ 2 * QuaternionAlgebra.nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk, smul_eq_mul]
  ring

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_units_ne_zero (γ : (ℍ[ℚ, a, b])ˣ) : QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) ≠ 0 := by
  intro h
  have := nrd_mul' (γ : ℍ[ℚ, a, b]) ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, QuaternionAlgebra.nrd_one, h, zero_mul] at this
  exact one_ne_zero this

theorem exists_eq_pow_smul_of_padicValRat_nrd_eq {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) :
    ∀ (e : ℕ) {h : ℍ[ℚ, a, b]}, h ∈ Λ → QuaternionAlgebra.nrd h ≠ 0 →
      padicValRat q' (QuaternionAlgebra.nrd h) = 2 * (e : ℤ) →
      ∃ h' ∈ Λ, h = ((q' : ℚ) ^ e) • h' ∧ padicValRat q' (QuaternionAlgebra.nrd h') = 0 := by
  have hq' : q'.Prime := Fact.out
  have hq'0 : (q' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero
  intro e
  induction e with
  | zero =>
    intro h hh _ hv
    exact ⟨h, hh, by rw [pow_zero, one_smul], by simpa using hv⟩
  | succ e ih =>
    intro h hh hn0 hv
    have h2 : 2 ≤ padicValRat q' (QuaternionAlgebra.nrd h) := by rw [hv]; push_cast; omega
    obtain ⟨h₁, hh₁, he⟩ := QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd hq' hdef hΛ hh (Or.inr h2)
    have he' : h = (q' : ℚ) • h₁ := by rw [he, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    have hn1 : QuaternionAlgebra.nrd h₁ ≠ 0 := by
      intro h0; apply hn0; rw [he', nrd_smul, h0, mul_zero]
    have hv1 : padicValRat q' (QuaternionAlgebra.nrd h₁) = 2 * (e : ℤ) := by
      have := hv
      rw [he', nrd_smul, padicValRat.mul (pow_ne_zero 2 hq'0) hn1, padicValRat.pow _, padicValRat.self hq'.one_lt] at this
      push_cast at this ⊢; omega
    obtain ⟨h', hh', he'', hv'⟩ := ih hh₁ hn1 hv1
    refine ⟨h', hh', ?_, hv'⟩
    rw [he', he'', smul_smul, pow_succ, mul_comm]

end ALRel21

namespace ALRel21

variable {a b : ℚ}

open CerednikDrinfeld.CosetGraph

theorem val_toLoc (u : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) :
    ((toLoc u γ : (Loc a b u)ˣ) : Loc a b u) = (γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) := rfl

theorem padicValRat_natCast_of_not_dvd {p D : ℕ} [Fact p.Prime] (h : ¬ p ∣ D) : padicValRat p (D : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd h

theorem padicValRat_pow_self {p : ℕ} [Fact p.Prime] (e : ℕ) : padicValRat p ((p : ℚ) ^ e) = (e : ℤ) := by
  have hp : p.Prime := Fact.out
  rw [padicValRat.pow _, padicValRat.self hp.one_lt, mul_one]

theorem tmul_one_mem_localBox_of_padicValRat_nrd_eq_zero {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) (u : HeightOneSpectrum (𝓞 ℚ)) (hu : ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal)
    {γ : ℍ[ℚ, a, b]} (hγ0 : QuaternionAlgebra.nrd γ ≠ 0) (hγ : padicValRat q' (QuaternionAlgebra.nrd γ) = 0) :
    γ ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) ∈ Submodule.localBox Λ u := by
  classical
  have hq' : q'.Prime := Fact.out
  have hq'0 : (q' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero
  obtain ⟨D, hD, hDγ⟩ := exists_natCast_smul_mem hΛ.isOrder γ
  obtain ⟨e, D', hD', hDD'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hD q' hq'.ne_one
  have hD'0 : D' ≠ 0 := by rintro rfl; exact hD (by rw [hDD', mul_zero])
  have hD'q : (D' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD'0
  have hDq : (D : ℚ) = (q' : ℚ) ^ e * (D' : ℚ) := by rw [hDD']; push_cast; ring

  set h : ℍ[ℚ, a, b] := (D : ℚ) • γ with hh
  have hhΛ : h ∈ Λ := by rw [hh, ← Int.cast_natCast, Int.cast_smul_eq_zsmul]; exact hDγ
  have hDn0 : (D : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hD)
  have hn0 : QuaternionAlgebra.nrd h ≠ 0 := by rw [hh, nrd_smul]; exact mul_ne_zero hDn0 hγ0
  have hv : padicValRat q' (QuaternionAlgebra.nrd h) = 2 * (e : ℤ) := by
    rw [hh, nrd_smul, padicValRat.mul hDn0 hγ0, hγ, add_zero, hDq, mul_pow,
      padicValRat.mul (pow_ne_zero 2 (pow_ne_zero e hq'0)) (pow_ne_zero 2 hD'q), ← pow_mul,
      padicValRat_pow_self, padicValRat.pow _, padicValRat_natCast_of_not_dvd hD', mul_zero, add_zero]
    push_cast; ring
  obtain ⟨h', hh', he, -⟩ := exists_eq_pow_smul_of_padicValRat_nrd_eq hdef hΛ e hhΛ hn0 hv

  have hγeq : γ = ((D' : ℚ)⁻¹) • h' := by
    have e1 : (D : ℚ) • γ = ((q' : ℚ) ^ e) • h' := by rw [← hh]; exact he
    rw [hDq, ← smul_smul] at e1
    have e2 : (D' : ℚ) • γ = h' := smul_right_injective ℍ[ℚ, a, b] (pow_ne_zero e hq'0) e1
    rw [← e2, smul_smul, inv_mul_cancel₀ hD'q, one_smul]
  have hD'u : algebraMap ℚ (u.adicCompletion ℚ) ((D' : ℚ)⁻¹) ∈ u.adicCompletionIntegers ℚ := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]
    have hne : ((D' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal := by
      intro hmem
      apply hD'

      have hmax : (Ideal.span {((q' : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
        have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
        have hpZ : _root_.Prime (q' : ℤ) := Nat.prime_iff_prime_int.mp hq'
        have hpO : _root_.Prime ((q' : ℕ) : 𝓞 ℚ) := by
          have : ((q' : ℕ) : 𝓞 ℚ) = e.symm (q' : ℤ) := by rw [map_natCast]
          rw [this]; exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
        refine ((Ideal.span_singleton_prime hpO.ne_zero).mpr hpO).isMaximal ?_
        rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq'.ne_zero
      have h1 : u.asIdeal = Ideal.span {((q' : ℕ) : 𝓞 ℚ)} :=
        (hmax.eq_of_le u.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hu)).symm
      rw [h1, Ideal.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
      have h2 : (D' : ℤ) = (q' : ℤ) * e c := by
        have := congrArg e hc
        rwa [map_natCast, map_mul, map_natCast] at this
      exact Int.natCast_dvd_natCast.mp ⟨e c, h2⟩
    rw [show Valued.v (algebraMap ℚ (u.adicCompletion ℚ) (D' : ℚ)) = u.valuation ℚ (D' : ℚ) from
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _]
    have : ((D' : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((D' : ℕ) : 𝓞 ℚ) := by simp
    rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    have hle := u.intValuation_le_one ((D' : ℕ) : 𝓞 ℚ)
    have hnlt : ¬ u.intValuation ((D' : ℕ) : 𝓞 ℚ) < 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]; exact hne
    rw [le_antisymm hle (not_lt.mp hnlt), inv_one]
  rw [hγeq]
  simp only [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
  rw [Algebra.smul_def, mul_one]
  unfold Submodule.localBox
  exact AddSubgroup.subset_closure ⟨h', hh', _, hD'u, rfl⟩

theorem toLoc_mem_localBoxUnits_of_padicValRat_nrd_eq_zero {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) (u : HeightOneSpectrum (𝓞 ℚ)) (hu : ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal)
    (γ : (ℍ[ℚ, a, b])ˣ) (hγ : padicValRat q' (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b])) = 0) :
    toLoc u γ ∈ Submodule.localBoxUnits Λ u := by
  have h0 := nrd_units_ne_zero γ
  have h0i := nrd_units_ne_zero γ⁻¹
  have hinv : QuaternionAlgebra.nrd ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]))⁻¹ := by
    have hm := nrd_mul' (γ : ℍ[ℚ, a, b]) ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, QuaternionAlgebra.nrd_one] at hm
    exact eq_inv_of_mul_eq_one_right hm.symm
  have hγi : padicValRat q' (QuaternionAlgebra.nrd ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 0 := by
    rw [hinv, padicValRat.inv, hγ, neg_zero]
  refine ⟨?_, ?_⟩
  · rw [val_toLoc]; exact tmul_one_mem_localBox_of_padicValRat_nrd_eq_zero hdef hΛ u hu h0 hγ
  · rw [← map_inv, val_toLoc]; exact tmul_one_mem_localBox_of_padicValRat_nrd_eq_zero hdef hΛ u hu h0i hγi

end ALRel21

namespace ALRel21

variable {a b : ℚ}

local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open CerednikDrinfeld.CosetGraph

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

def localUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup (Loc a b w)ˣ where
  carrier := Submodule.localBoxUnits Λ w
  one_mem' := by
    have h1 : ((1 : (Loc a b w)ˣ) : Loc a b w) ∈ (Submodule.localBox Λ w : Set (Loc a b w)) := by
      rw [Units.val_one]
      exact AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩
    exact ⟨h1, by rw [inv_one]; exact h1⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact localBox_mul_mem hΛ w hx.1 hy.1
    · rw [mul_inv_rev, Units.val_mul]; exact localBox_mul_mem hΛ w hy.2 hx.2
  inv_mem' := by
    intro x hx
    exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem mem_awayUnits_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (v : HeightOneSpectrum (𝓞 ℚ))
    (γ : (ℍ[ℚ, a, b])ˣ) :
    γ ∈ awayUnits R v ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → toLoc w γ ∈ Submodule.localBoxUnits R w := by
  have hcl : ∀ w, Subgroup.closure (Submodule.localBoxUnits R w) = localUnits hR w := fun w => (localUnits hR w).closure_eq
  simp only [awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap, hcl]
  rfl

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (w : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ w ≤ Submodule.localBox Λ' w := by
  unfold Submodule.localBox
  exact AddSubgroup.closure_mono fun x ⟨z, hz, c, hc, e⟩ => ⟨z, h hz, c, hc, e⟩

theorem localBoxUnits_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (w : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBoxUnits Λ w ⊆ Submodule.localBoxUnits Λ' w :=
  fun _ hx => ⟨localBox_mono h w hx.1, localBox_mono h w hx.2⟩

theorem awayUnits_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (hΛ' : QuaternionAlgebra.IsOrder Λ')
    (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) : awayUnits Λ v ≤ awayUnits Λ' v := by
  intro γ hγ
  rw [mem_awayUnits_iff hΛ']
  rw [mem_awayUnits_iff hΛ] at hγ
  exact fun w hw => localBoxUnits_mono h w (hγ w hw)

theorem toLoc_conj_mem_localBoxUnits {R X : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (sf : (𝔸ℍ)ˣ) (s : (ℍ[ℚ, a, b])ˣ) (hX : X ≤ Submodule.conjByFiniteIdele R sf) (u : HeightOneSpectrum (𝓞 ℚ))
    (hsu : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (sf : 𝔸ℍ) = (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ))
    {w : (ℍ[ℚ, a, b])ˣ} (hw : toLoc u w ∈ Submodule.localBoxUnits X u) :
    toLoc u (s⁻¹ * w * s) ∈ Submodule.localBoxUnits R u := by
  have hsfu : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u).toRingHom.toMonoidHom sf = toLoc u s := Units.ext hsu
  have hsui : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u ((sf⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = ((toLoc u s)⁻¹ : (Loc a b u)ˣ) := by
    rw [← hsfu, ← map_inv]; rfl
  have key : ∀ x : Loc a b u, x ∈ Submodule.localBox X u →
      (((toLoc u s)⁻¹ : (Loc a b u)ˣ) : Loc a b u) * x * (toLoc u s : (Loc a b u)ˣ) ∈ Submodule.localBox R u := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (Submodule.mem_localBox_conjByFiniteIdele_iff R hR.fg hR.spanTop sf u x).mp (localBox_mono hX u hx)
    rw [hxy, hsu, hsui, ← val_toLoc, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    exact hy
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
    exact key _ hw.1
  · rw [map_mul, map_mul, map_inv, mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, ← mul_assoc]
    exact key _ hw.2

theorem mem_inf_map_conj {Γ : Subgroup (ℍ[ℚ, a, b])ˣ} {s x : (ℍ[ℚ, a, b])ˣ} (hx : x ∈ Γ) (hsx : s⁻¹ * x * s ∈ Γ) :
    x ∈ Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom := by
  refine ⟨hx, Subgroup.mem_map.mpr ⟨s⁻¹ * x * s, hsx, ?_⟩⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end ALRel21

namespace ALRel21

variable {a b : ℚ}

local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open CerednikDrinfeld.CosetGraph

theorem nrd_units_inv (γ : (ℍ[ℚ, a, b])ˣ) :
    QuaternionAlgebra.nrd ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]))⁻¹ := by
  have hm := nrd_mul' (γ : ℍ[ℚ, a, b]) ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, QuaternionAlgebra.nrd_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

theorem toLoc_mem_localBoxUnits_eichler_of_padicValRat_nrd_eq_zero {q' : ℕ} [Fact q'.Prime]
    (hdef : IsDefiniteRamifiedExactlyAt a b q') {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    (u : HeightOneSpectrum (𝓞 ℚ)) (hu : ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal)
    (γ : (ℍ[ℚ, a, b])ˣ) (hγ : padicValRat q' (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b])) = 0) :
    toLoc u γ ∈ Submodule.localBoxUnits R u := by
  obtain ⟨Λa, Λb, hΛa, hΛb, hRab, -⟩ := hR
  have ha := toLoc_mem_localBoxUnits_of_padicValRat_nrd_eq_zero hdef hΛa u hu γ hγ
  have hb := toLoc_mem_localBoxUnits_of_padicValRat_nrd_eq_zero hdef hΛb u hu γ hγ
  have hloc : Submodule.localBox R u = Submodule.localBox Λa u ⊓ Submodule.localBox Λb u := by
    rw [hRab]
    exact Submodule.localBox_inf Λa Λb hΛa.isOrder.fg hΛa.isOrder.spanTop hΛb.isOrder.fg hΛb.isOrder.spanTop u
  refine ⟨?_, ?_⟩
  · rw [hloc]; exact ⟨ha.1, hb.1⟩
  · rw [hloc]; exact ⟨ha.2, hb.2⟩

theorem block
    {a₁ b₁ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')

    (r rbar : ℕ) [Fact r.Prime] [Fact rbar.Prime] (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hrrbar : rbar ≠ r)
    (hdef₁ : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((r : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)
    (s₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₂ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₂ ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₂ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γ₂ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ₂0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ₂ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat r (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (hΓ₂ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₂ (some ℓ) = Γ₂ none ⊓ (Γ₂ none).map (MulAut.conj (s₂ ℓ)).toMonoidHom)
    (w₂ wbar₂ : HeckeTower.Obj q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (hw₂ : (w₂ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ nrd (w₂ none : ℍ[ℚ, a₁, b₁]) = (r : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂ ∧ nrd (w₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (r : ℚ))
    (hwbar₂ :
      (nrd (wbar₂ none : ℍ[ℚ, a₁, b₁]) = (rbar : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((rbar : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₂ none) ∈ Submodule.localBoxUnits R₁ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox R₁ u ↔
            x ∈ Submodule.localBox R₁ u) ∧
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
            x ∈ Submodule.localBox Λ₁ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (rbar : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((rbar : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₂ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₁ (sf₂ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
              x ∈ Submodule.localBox Λ₁ u))))
    :
    ∀ ℓ : HeckeTower.AwayPrime q q',
      w₂ (some ℓ) * (w₂ none)⁻¹ ∈ Γ₂ none ∧
      (s₂ ℓ)⁻¹ * w₂ (some ℓ) * (s₂ ℓ) * (w₂ none)⁻¹ ∈ Γ₂ none ∧
      wbar₂ (some ℓ) * (wbar₂ none)⁻¹ ∈ Γ₂ none ∧
      (s₂ ℓ)⁻¹ * wbar₂ (some ℓ) * (s₂ ℓ) * (wbar₂ none)⁻¹ ∈ Γ₂ none := by
  classical
  intro ℓ
  have hrP : r.Prime := Fact.out
  have hrbarP : rbar.Prime := Fact.out
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hrP.ne_zero
  have hrbar0 : (rbar : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hrbarP.ne_zero
  have hℓ0 : ((ℓ.1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero
  have hR₁o : QuaternionAlgebra.IsOrder R₁ := hR₁.isOrder
  set Rl := meetOrder R₁ (sf₂ ℓ) with hRl
  have hRlo : QuaternionAlgebra.IsOrder Rl := hR₁o.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele R₁ hR₁o (sf₂ ℓ))
  have hRl_le : Rl ≤ R₁ := inf_le_left
  have hRl_conj : Rl ≤ Submodule.conjByFiniteIdele R₁ (sf₂ ℓ) := inf_le_right

  have hru : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal := by
    intro u hu hmem
    apply hu

    have hmax : (Ideal.span {((r : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
      have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
      have hpZ : _root_.Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hrP
      have hpO : _root_.Prime ((r : ℕ) : 𝓞 ℚ) := by
        have : ((r : ℕ) : 𝓞 ℚ) = e.symm (r : ℤ) := by rw [map_natCast]
        rw [this]; exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
      refine ((Ideal.span_singleton_prime hpO.ne_zero).mpr hpO).isMaximal ?_
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hrP.ne_zero
    have h1 : u.asIdeal = Ideal.span {((r : ℕ) : 𝓞 ℚ)} :=
      (hmax.eq_of_le u.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
    have h2 : v₂.asIdeal = Ideal.span {((r : ℕ) : 𝓞 ℚ)} :=
      (hmax.eq_of_le v₂.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv₂)).symm
    exact HeightOneSpectrum.ext (h1.trans h2.symm)
  have hsu : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        (s₂ ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) := fun u hu => (hs₂ ℓ).1 u (hru u hu)

  obtain ⟨⟨hw0U, hw0n⟩, hwℓ⟩ := hw₂
  obtain ⟨hwℓU, hwℓn⟩ := hwℓ ℓ
  obtain ⟨⟨hwb0n, hwb0U, -⟩, hwbℓ⟩ := hwbar₂
  obtain ⟨hwbℓn, hwbℓU, -⟩ := hwbℓ ℓ
  have hsn : QuaternionAlgebra.nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ) := (hs₂ ℓ).2.2.2

  have memΓ : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ awayUnits R₁ v₂ → QuaternionAlgebra.nrd (x : ℍ[ℚ, a₁, b₁]) = 1 → x ∈ Γ₂ none := by
    intro x hx hn
    rw [hΓ₂0]
    refine ⟨hx, ?_⟩
    rw [hn, padicValRat.one]
    exact ⟨0, (add_zero (0 : ℤ)).symm⟩

  have hconj_w : (s₂ ℓ)⁻¹ * w₂ (some ℓ) * s₂ ℓ ∈ awayUnits R₁ v₂ := by
    rw [mem_awayUnits_iff hR₁o]
    intro u hu
    exact toLoc_conj_mem_localBoxUnits hR₁o (sf₂ ℓ) (s₂ ℓ) hRl_conj u (hsu u hu) (((mem_awayUnits_iff hRlo v₂ _).mp hwℓU) u hu)
  have hwℓ' : w₂ (some ℓ) ∈ awayUnits R₁ v₂ := awayUnits_mono hRlo hR₁o hRl_le v₂ hwℓU

  have hz : wbar₂ (some ℓ) * (wbar₂ none)⁻¹ ∈ awayUnits R₁ v₂ := by
    rw [mem_awayUnits_iff hR₁o]
    intro u hu
    by_cases hrb : ((rbar : ℕ) : 𝓞 ℚ) ∈ u.asIdeal
    · refine toLoc_mem_localBoxUnits_eichler_of_padicValRat_nrd_eq_zero hdef₁ hR₁ u hrb _ ?_
      rw [Units.val_mul, nrd_mul', nrd_units_inv, hwbℓn, hwb0n, mul_inv_cancel₀ hrbar0, padicValRat.one]
    · have h1 : toLoc u (wbar₂ (some ℓ)) ∈ localUnits hR₁o u := localBoxUnits_mono hRl_le u (hwbℓU u hu hrb)
      have h2 : toLoc u (wbar₂ none) ∈ localUnits hR₁o u := hwb0U u hu hrb
      have := (localUnits hR₁o u).mul_mem h1 ((localUnits hR₁o u).inv_mem h2)
      rw [← map_inv, ← map_mul] at this
      exact this
  have ht : (s₂ ℓ)⁻¹ * wbar₂ (some ℓ) * s₂ ℓ * (wbar₂ none)⁻¹ ∈ awayUnits R₁ v₂ := by
    rw [mem_awayUnits_iff hR₁o]
    intro u hu
    by_cases hrb : ((rbar : ℕ) : 𝓞 ℚ) ∈ u.asIdeal
    · refine toLoc_mem_localBoxUnits_eichler_of_padicValRat_nrd_eq_zero hdef₁ hR₁ u hrb _ ?_
      rw [Units.val_mul, Units.val_mul, Units.val_mul, nrd_mul', nrd_mul', nrd_mul', nrd_units_inv, nrd_units_inv, hwbℓn, hwb0n, hsn]
      rw [show (((ℓ.1 : ℕ) : ℚ))⁻¹ * (rbar : ℚ) * ((ℓ.1 : ℕ) : ℚ) * (rbar : ℚ)⁻¹ = 1 by field_simp, padicValRat.one]
    · have h1 : toLoc u ((s₂ ℓ)⁻¹ * wbar₂ (some ℓ) * s₂ ℓ) ∈ localUnits hR₁o u :=
        toLoc_conj_mem_localBoxUnits hR₁o (sf₂ ℓ) (s₂ ℓ) hRl_conj u (hsu u hu) (hwbℓU u hu hrb)
      have h2 : toLoc u (wbar₂ none) ∈ localUnits hR₁o u := hwb0U u hu hrb
      have := (localUnits hR₁o u).mul_mem h1 ((localUnits hR₁o u).inv_mem h2)
      rw [← map_inv, ← map_mul] at this
      exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine memΓ _ ((awayUnits R₁ v₂).mul_mem hwℓ' ((awayUnits R₁ v₂).inv_mem hw0U)) ?_
    rw [Units.val_mul, nrd_mul', nrd_units_inv, hwℓn, hw0n, mul_inv_cancel₀ hr0]
  · refine memΓ _ ((awayUnits R₁ v₂).mul_mem hconj_w ((awayUnits R₁ v₂).inv_mem hw0U)) ?_
    rw [Units.val_mul, Units.val_mul, Units.val_mul, nrd_mul', nrd_mul', nrd_mul', nrd_units_inv, nrd_units_inv, hwℓn, hw0n, hsn]
    field_simp
  · refine memΓ _ hz ?_
    rw [Units.val_mul, nrd_mul', nrd_units_inv, hwbℓn, hwb0n, mul_inv_cancel₀ hrbar0]
  · refine memΓ _ ht ?_
    rw [Units.val_mul, Units.val_mul, Units.val_mul, nrd_mul', nrd_mul', nrd_mul', nrd_units_inv, nrd_units_inv, hwbℓn, hwb0n, hsn]
    field_simp

end ALRel21

namespace ALREL48

open CerednikDrinfeld CerednikDrinfeld.CosetGraph QuaternionAlgebra

section Generic

variable {M : Type*} [Group M]

theorem conj_mem_closure_of {S : Set M} {g : M} (hS : ∀ u ∈ S, g * u * g⁻¹ ∈ S) {x : M}
    (hx : x ∈ Subgroup.closure S) : g * x * g⁻¹ ∈ Subgroup.closure S := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure (hS y hy)
  | one => simpa using (Subgroup.closure S).one_mem
  | mul y z _ _ hy hz =>
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]; exact mul_mem hy hz
  | inv y _ hy =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hy

theorem map_conj_eq_self_of {H : Subgroup M} {g : M} (h₁ : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h₂ : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using h₁ y hy
  · intro hx
    exact ⟨g⁻¹ * x * g, h₂ x hx, by simp [MulAut.conj_apply, mul_assoc]⟩

end Generic

section Parity

variable {a b : ℚ} {p : ℕ} [hp : Fact p.Prime]

theorem nrd_units_mul (x y : (ℍ[ℚ, a, b])ˣ) :
    nrd ((x * y : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = nrd (x : ℍ[ℚ, a, b]) * nrd (y : ℍ[ℚ, a, b]) := by
  rw [Units.val_mul, QuaternionAlgebra.nrd_mul]

theorem nrd_units_ne_zero (x : (ℍ[ℚ, a, b])ˣ) : nrd (x : ℍ[ℚ, a, b]) ≠ 0 := by
  intro h
  have := nrd_units_mul x x⁻¹
  rw [mul_inv_cancel, Units.val_one, nrd_one, h, zero_mul] at this
  exact one_ne_zero this

theorem nrd_units_inv (x : (ℍ[ℚ, a, b])ˣ) :
    nrd ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (nrd (x : ℍ[ℚ, a, b]))⁻¹ := by
  have h := nrd_units_mul x x⁻¹
  rw [mul_inv_cancel, Units.val_one, nrd_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem padicValRat_nrd_mul (x y : (ℍ[ℚ, a, b])ˣ) :
    padicValRat p (nrd ((x * y : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) =
      padicValRat p (nrd (x : ℍ[ℚ, a, b])) + padicValRat p (nrd (y : ℍ[ℚ, a, b])) := by
  rw [nrd_units_mul, padicValRat.mul (nrd_units_ne_zero x) (nrd_units_ne_zero y)]

theorem padicValRat_nrd_inv (x : (ℍ[ℚ, a, b])ˣ) :
    padicValRat p (nrd ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = - padicValRat p (nrd (x : ℍ[ℚ, a, b])) := by
  rw [nrd_units_inv, padicValRat.inv]

theorem even_padicValRat_nrd_conj (g x : (ℍ[ℚ, a, b])ˣ)
    (hx : Even (padicValRat p (nrd (x : ℍ[ℚ, a, b])))) :
    Even (padicValRat p (nrd ((g * x * g⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]))) := by
  rw [padicValRat_nrd_mul, padicValRat_nrd_mul, padicValRat_nrd_inv]
  have e : padicValRat p (nrd (g : ℍ[ℚ, a, b])) + padicValRat p (nrd (x : ℍ[ℚ, a, b])) +
      -padicValRat p (nrd (g : ℍ[ℚ, a, b])) = padicValRat p (nrd (x : ℍ[ℚ, a, b])) := by ring
  rw [e]; exact hx

theorem even_padicValRat_nrd_mul_self (x : (ℍ[ℚ, a, b])ˣ) :
    Even (padicValRat p (nrd ((x * x : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]))) := by
  rw [padicValRat_nrd_mul]; exact ⟨_, rfl⟩

theorem even_padicValRat_nrd_comm (x y : (ℍ[ℚ, a, b])ˣ) :
    Even (padicValRat p (nrd ((x * y * x⁻¹ * y⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]))) := by
  rw [padicValRat_nrd_mul, padicValRat_nrd_mul, padicValRat_nrd_mul, padicValRat_nrd_inv, padicValRat_nrd_inv]
  exact ⟨0, by ring⟩

theorem even_padicValRat_nrd_one :
    Even (padicValRat p (nrd ((1 : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]))) := by
  rw [Units.val_one, nrd_one, padicValRat.one]; exact ⟨0, rfl⟩

end Parity

section LevelFree

variable {a b : ℚ}

theorem mem_awayUnits_iff (S : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b])ˣ) :
    x ∈ awayUnits S v ↔ ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v →
      toLoc u x ∈ Subgroup.closure (Submodule.localBoxUnits S u) := by
  simp only [awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem conj_mem_localBoxUnits {S : Submodule ℤ ℍ[ℚ, a, b]} {u : HeightOneSpectrum (𝓞 ℚ)} {g : (Loc a b u)ˣ}
    (hg : ∀ x : Loc a b u,
      ((g⁻¹ : (Loc a b u)ˣ) : Loc a b u) * x * (g : Loc a b u) ∈ Submodule.localBox S u ↔ x ∈ Submodule.localBox S u)
    (U : (Loc a b u)ˣ) (hU : U ∈ Submodule.localBoxUnits S u) :
    g * U * g⁻¹ ∈ Submodule.localBoxUnits S u ∧ g⁻¹ * U * g ∈ Submodule.localBoxUnits S u := by
  rw [Submodule.mem_localBoxUnits_iff] at hU ⊢
  rw [Submodule.mem_localBoxUnits_iff]
  obtain ⟨hU1, hU2⟩ := hU
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply (hg _).1
    have e : ((g⁻¹ : (Loc a b u)ˣ) : Loc a b u) * ((g * U * g⁻¹ : (Loc a b u)ˣ) : Loc a b u) * (g : Loc a b u) = U := by
      rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
    rw [e]; exact hU1
  · apply (hg _).1
    have e : ((g⁻¹ : (Loc a b u)ˣ) : Loc a b u) * (((g * U * g⁻¹)⁻¹ : (Loc a b u)ˣ) : Loc a b u) * (g : Loc a b u) =
        ((U⁻¹ : (Loc a b u)ˣ) : Loc a b u) := by
      rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
    rw [e]; exact hU2
  · have e : ((g⁻¹ * U * g : (Loc a b u)ˣ) : Loc a b u) = ((g⁻¹ : (Loc a b u)ˣ) : Loc a b u) * (U : Loc a b u) * (g : Loc a b u) := by
      rw [Units.val_mul, Units.val_mul]
    rw [e]; exact (hg _).2 hU1
  · have e : (((g⁻¹ * U * g)⁻¹ : (Loc a b u)ˣ) : Loc a b u) =
        ((g⁻¹ : (Loc a b u)ˣ) : Loc a b u) * ((U⁻¹ : (Loc a b u)ˣ) : Loc a b u) * (g : Loc a b u) := by
      rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
    rw [e]; exact (hg _).2 hU2

theorem conj_mem_awayUnits_of_normalizes {S : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {n : (ℍ[ℚ, a, b])ˣ}
    (hn : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ∀ x : Loc a b u,
      (((toLoc u n)⁻¹ : (Loc a b u)ˣ) : Loc a b u) * x * (toLoc u n : Loc a b u) ∈ Submodule.localBox S u ↔
        x ∈ Submodule.localBox S u)
    {x : (ℍ[ℚ, a, b])ˣ} (hx : x ∈ awayUnits S v) :
    n * x * n⁻¹ ∈ awayUnits S v ∧ n⁻¹ * x * n ∈ awayUnits S v := by
  rw [mem_awayUnits_iff] at hx ⊢
  rw [mem_awayUnits_iff]
  constructor
  · intro u hu
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_closure_of (fun U hU => (conj_mem_localBoxUnits (hn u hu) U hU).1) (hx u hu)
  · intro u hu
    rw [map_mul, map_mul, map_inv]
    have := conj_mem_closure_of (g := (toLoc u n)⁻¹) (S := Submodule.localBoxUnits S u)
      (fun U hU => by simpa using (conj_mem_localBoxUnits (hn u hu) U hU).2) (hx u hu)
    simpa using this

theorem core {S : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {p : ℕ} [Fact p.Prime] {Γ : Subgroup (ℍ[ℚ, a, b])ˣ}
    (hΓ : ∀ x : (ℍ[ℚ, a, b])ˣ, x ∈ Γ ↔ x ∈ awayUnits S v ∧ Even (padicValRat p (nrd (x : ℍ[ℚ, a, b]))))
    {w n : (ℍ[ℚ, a, b])ˣ} (hw : w ∈ awayUnits S v)
    (hn : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ∀ x : Loc a b u,
      (((toLoc u n)⁻¹ : (Loc a b u)ˣ) : Loc a b u) * x * (toLoc u n : Loc a b u) ∈ Submodule.localBox S u ↔
        x ∈ Submodule.localBox S u) :
    Γ.map (MulAut.conj w).toMonoidHom = Γ ∧ Γ.map (MulAut.conj n).toMonoidHom = Γ ∧
      w * w ∈ Γ ∧ w * n * w⁻¹ * n⁻¹ ∈ Γ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine map_conj_eq_self_of (fun x hx => ?_) (fun x hx => ?_)
    · rw [hΓ] at hx ⊢
      exact ⟨mul_mem (mul_mem hw hx.1) (inv_mem hw), even_padicValRat_nrd_conj (p := p) w x hx.2⟩
    · rw [hΓ] at hx ⊢
      refine ⟨mul_mem (mul_mem (inv_mem hw) hx.1) hw, ?_⟩
      simpa using even_padicValRat_nrd_conj (p := p) w⁻¹ x hx.2
  · refine map_conj_eq_self_of (fun x hx => ?_) (fun x hx => ?_)
    · rw [hΓ] at hx ⊢
      exact ⟨(conj_mem_awayUnits_of_normalizes hn hx.1).1, even_padicValRat_nrd_conj (p := p) n x hx.2⟩
    · rw [hΓ] at hx ⊢
      refine ⟨(conj_mem_awayUnits_of_normalizes hn hx.1).2, ?_⟩
      simpa using even_padicValRat_nrd_conj (p := p) n⁻¹ x hx.2
  · rw [hΓ]; exact ⟨mul_mem hw hw, even_padicValRat_nrd_mul_self (p := p) w⟩
  · rw [hΓ]
    refine ⟨?_, even_padicValRat_nrd_comm (p := p) w n⟩
    have h1 : n * w⁻¹ * n⁻¹ ∈ awayUnits S v := (conj_mem_awayUnits_of_normalizes hn (inv_mem hw)).1
    have e : w * n * w⁻¹ * n⁻¹ = w * (n * w⁻¹ * n⁻¹) := by group
    rw [e]; exact mul_mem hw h1

end LevelFree

section LocalUnits

variable {a b : ℚ}

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem coe_toLoc (u : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b])ˣ) :
    ((toLoc u x : (Loc a b u)ˣ) : Loc a b u) = (x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) := rfl

theorem coe_toLoc_inv (u : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b])ˣ) :
    (((toLoc u x)⁻¹ : (Loc a b u)ˣ) : Loc a b u) = ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) := by
  rw [← map_inv]; rfl

theorem tmul_mem_localBox {S : Submodule ℤ ℍ[ℚ, a, b]} {u : HeightOneSpectrum (𝓞 ℚ)} {z : ℍ[ℚ, a, b]} (hz : z ∈ S)
    {c : u.adicCompletion ℚ} (hc : c ∈ u.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox S u :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem valued_natCast (u : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v ((n : ℕ) : u.adicCompletion ℚ) = u.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ)) := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) u (n : 𝓞 ℚ)
  change Valued.v (algebraMap (𝓞 ℚ) (u.adicCompletion ℚ) n) = _ at h
  rwa [map_natCast] at h

theorem natCast_mem_integers (u : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : u.adicCompletion ℚ) ∈ u.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_natCast]; exact HeightOneSpectrum.valuation_le_one u _

theorem natCast_inv_mem_integers (u : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ((n : ℕ) : 𝓞 ℚ) ∉ u.asIdeal) :
    ((n : ℕ) : u.adicCompletion ℚ)⁻¹ ∈ u.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast,
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := u)).mpr hn, inv_one]

theorem toLoc_natCast_mem_localBoxUnits {S : Submodule ℤ ℍ[ℚ, a, b]} (hS : (1 : ℍ[ℚ, a, b]) ∈ S) (u : HeightOneSpectrum (𝓞 ℚ))
    {n : ℕ} (hn0 : (n : ℚ) ≠ 0) (hn : ((n : ℕ) : 𝓞 ℚ) ∉ u.asIdeal) :
    toLoc u (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (n : ℚ) hn0)) ∈ Submodule.localBoxUnits S u := by
  rw [Submodule.mem_localBoxUnits_iff, coe_toLoc_inv, coe_toLoc]
  have e1 : ((Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (n : ℚ) hn0) : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ]
      (1 : u.adicCompletion ℚ) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((n : ℕ) : u.adicCompletion ℚ) := by
    change algebraMap ℚ ℍ[ℚ, a, b] (n : ℚ) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) = _
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, map_natCast]
  have e2 : (((Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (n : ℚ) hn0))⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ]
      (1 : u.adicCompletion ℚ) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((n : ℕ) : u.adicCompletion ℚ)⁻¹ := by
    rw [← map_inv]
    change algebraMap ℚ ℍ[ℚ, a, b] (((Units.mk0 (n : ℚ) hn0)⁻¹ : ℚˣ) : ℚ) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) = _
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, Algebra.TensorProduct.tmul_one_eq_one_tmul, map_inv₀, map_natCast]
  rw [e1, e2]
  exact ⟨tmul_mem_localBox hS (natCast_mem_integers u n), tmul_mem_localBox hS (natCast_inv_mem_integers u hn)⟩

end LocalUnits

section DivisionPlace

variable {a b : ℚ}

open IsDedekindDomain

theorem nrd_mk_algebraMap (S : Type*) [CommRing S] [Algebra ℚ S] (z : ℍ[ℚ, a, b]) :
    nrd (⟨algebraMap ℚ S z.re, algebraMap ℚ S z.imI, algebraMap ℚ S z.imJ, algebraMap ℚ S z.imK⟩ :
        ℍ[S, algebraMap ℚ S a, algebraMap ℚ S b]) = algebraMap ℚ S (nrd z) := by
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [nrd_mk, map_sub, map_add, map_mul, map_pow, map_zero]

theorem tmul_one_mem_localBox_of_isMaximalOrder_of_forall_isUnit {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (u : HeightOneSpectrum (𝓞 ℚ)) (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    {z : ℍ[ℚ, a, b]} (hz : algebraMap ℚ (u.adicCompletion ℚ) (nrd z) ∈ u.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) ∈ Submodule.localBox Λ u := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := u.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (u.adicCompletion ℚ) a) (d₂ := (0 : u.adicCompletion ℚ)) (d₃ := algebraMap ℚ (u.adicCompletion ℚ) b)
    rfl (map_zero _) rfl AlgEquiv.refl
  have hφ' : ∀ (x : ℍ[ℚ, a, b]) (r : u.adicCompletion ℚ), φ (x ⊗ₜ[ℚ] r) =
      r • (⟨algebraMap ℚ (u.adicCompletion ℚ) x.re, algebraMap ℚ (u.adicCompletion ℚ) x.imI,
        algebraMap ℚ (u.adicCompletion ℚ) x.imJ, algebraMap ℚ (u.adicCompletion ℚ) x.imK⟩ :
          ℍ[u.adicCompletion ℚ, algebraMap ℚ (u.adicCompletion ℚ) a, algebraMap ℚ (u.adicCompletion ℚ) b]) := by
    intro x r; rw [hφ]; rfl
  rw [QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ u hdiv φ hφ',
    hφ', one_smul, nrd_mk_algebraMap]
  exact hz

theorem localBox_eq_of_isEichlerOrder_of_mem {q' : ℕ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (u : HeightOneSpectrum (𝓞 ℚ)) (hu : ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal) :
    Submodule.localBox R u = Submodule.localBox Λ u := by
  have hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ, x ≠ 0 → IsUnit x := (hdef.2.2 u).mpr hu
  obtain ⟨Λa, Λb, ha, hb, rfl, -⟩ := hR
  rw [Submodule.localBox_inf Λa Λb ha.isOrder.fg ha.isOrder.spanTop hb.isOrder.fg hb.isOrder.spanTop u,
    QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit u hdiv ha hΛ,
    QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit u hdiv hb hΛ, inf_idem]

theorem toLoc_mem_localBoxUnits_of_forall_isUnit {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (u : HeightOneSpectrum (𝓞 ℚ)) (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (y : (ℍ[ℚ, a, b])ˣ) (hy : nrd (y : ℍ[ℚ, a, b]) = 1) :
    toLoc u y ∈ Submodule.localBoxUnits Λ u := by
  rw [Submodule.mem_localBoxUnits_iff, coe_toLoc, coe_toLoc_inv]
  refine ⟨tmul_one_mem_localBox_of_isMaximalOrder_of_forall_isUnit hΛ u hdiv ?_,
    tmul_one_mem_localBox_of_isMaximalOrder_of_forall_isUnit hΛ u hdiv ?_⟩
  · rw [hy, map_one]; exact one_mem _
  · rw [nrd_units_inv, hy, inv_one, map_one]; exact one_mem _

end DivisionPlace

section Clause5

variable {a b : ℚ}

theorem nrd_algebraMap (r : ℚ) : nrd (algebraMap ℚ ℍ[ℚ, a, b] r) = r ^ 2 := by
  rw [show algebraMap ℚ ℍ[ℚ, a, b] r = ((r : ℚ) : ℍ[ℚ, a, b]) from rfl, nrd_coe]

theorem clause5 {S : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {p : ℕ} [Fact p.Prime] {Γ : Subgroup (ℍ[ℚ, a, b])ˣ}
    (hΓ : ∀ x : (ℍ[ℚ, a, b])ˣ, x ∈ Γ ↔ x ∈ awayUnits S v ∧ Even (padicValRat p (nrd (x : ℍ[ℚ, a, b]))))
    (hS : (1 : ℍ[ℚ, a, b]) ∈ S) {q' : ℕ} (hq'0 : (q' : ℚ) ≠ 0) {n : (ℍ[ℚ, a, b])ˣ}
    (hn1 : nrd (n : ℍ[ℚ, a, b]) = (q' : ℚ))
    (hn2 : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal → toLoc u n ∈ Submodule.localBoxUnits S u)
    (hram : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
      toLoc u ((Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) hq'0))⁻¹ * (n * n)) ∈ Submodule.localBoxUnits S u) :
    (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) hq'0))⁻¹ * (n * n) ∈ Γ := by
  rw [hΓ]
  constructor
  · rw [mem_awayUnits_iff]
    intro u hu
    by_cases hq'u : ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal
    · exact Subgroup.subset_closure (hram u hq'u)
    · rw [map_mul, map_mul, map_inv]
      exact mul_mem (inv_mem (Subgroup.subset_closure (toLoc_natCast_mem_localBoxUnits hS u hq'0 hq'u)))
        (mul_mem (Subgroup.subset_closure (hn2 u hu hq'u)) (Subgroup.subset_closure (hn2 u hu hq'u)))
  · rw [padicValRat_nrd_mul, padicValRat_nrd_inv, padicValRat_nrd_mul]
    have hc : padicValRat p (nrd ((Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) hq'0) : (ℍ[ℚ, a, b])ˣ) :
        ℍ[ℚ, a, b])) = 2 * padicValRat p (q' : ℚ) := by
      rw [show ((Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) hq'0) : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) =
        algebraMap ℚ ℍ[ℚ, a, b] (q' : ℚ) from rfl, nrd_algebraMap, padicValRat.pow _]; push_cast; ring
    rw [hc]
    exact ⟨-padicValRat p (q' : ℚ) + padicValRat p (nrd (n : ℍ[ℚ, a, b])), by ring⟩

theorem nrd_clause5_eq_one {q' : ℕ} (hq'0 : (q' : ℚ) ≠ 0) {n : (ℍ[ℚ, a, b])ˣ} (hn1 : nrd (n : ℍ[ℚ, a, b]) = (q' : ℚ)) :
    nrd (((Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) hq'0))⁻¹ * (n * n) : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
  rw [nrd_units_mul, nrd_units_inv, nrd_units_mul, hn1,
    show ((Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) hq'0) : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) =
      algebraMap ℚ ℍ[ℚ, a, b] (q' : ℚ) from rfl, nrd_algebraMap]
  field_simp

end Clause5

section LevelEll

variable {a b : ℚ}

open IsDedekindDomain

theorem mem_iff_of_inf_map_conj {p : ℕ} [Fact p.Prime] {A Aℓ Γ Γℓ : Subgroup (ℍ[ℚ, a, b])ˣ} {s : (ℍ[ℚ, a, b])ˣ}
    (hΓ : ∀ x : (ℍ[ℚ, a, b])ˣ, x ∈ Γ ↔ x ∈ A ∧ Even (padicValRat p (nrd (x : ℍ[ℚ, a, b]))))
    (hΓℓ : Γℓ = Γ ⊓ Γ.map (MulAut.conj s).toMonoidHom)
    (hAℓ : Aℓ = A ⊓ A.map (MulAut.conj s).toMonoidHom) :
    ∀ x : (ℍ[ℚ, a, b])ˣ, x ∈ Γℓ ↔ x ∈ Aℓ ∧ Even (padicValRat p (nrd (x : ℍ[ℚ, a, b]))) := by
  intro x
  rw [hΓℓ, hAℓ, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_map, hΓ]
  constructor
  · rintro ⟨⟨hxA, hxe⟩, y, hy, hyx⟩
    rw [hΓ] at hy
    exact ⟨⟨hxA, y, hy.1, hyx⟩, hxe⟩
  · rintro ⟨⟨hxA, y, hyA, hyx⟩, hxe⟩
    refine ⟨⟨hxA, hxe⟩, y, ?_, hyx⟩
    rw [hΓ]
    refine ⟨hyA, ?_⟩
    have hyx' : s * y * s⁻¹ = x := by simpa [MulAut.conj_apply] using hyx
    have hy' : s⁻¹ * x * s⁻¹⁻¹ = y := by rw [← hyx']; group
    rw [← hy']
    exact even_padicValRat_nrd_conj (p := p) s⁻¹ x hxe

theorem natCast_not_mem_asIdeal_of_ne {p p' : ℕ} [hp : Fact p.Prime] [hp' : Fact p'.Prime] (h : p' ≠ p)
    (u : HeightOneSpectrum (𝓞 ℚ)) (hu : ((p' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal) : ((p : ℕ) : 𝓞 ℚ) ∉ u.asIdeal := by
  intro hpu
  have hcop : IsCoprime ((p' : ℤ) : 𝓞 ℚ) ((p : ℤ) : 𝓞 ℚ) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp'.out hp.out).mpr h)).map (Int.castRingHom (𝓞 ℚ))
  obtain ⟨x, y, hxy⟩ := hcop
  rw [Int.cast_natCast, Int.cast_natCast] at hxy
  have h1 : (1 : 𝓞 ℚ) ∈ u.asIdeal := by
    rw [← hxy]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hu) (Ideal.mul_mem_left _ _ hpu)
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem tmul_one_mem_localBox_meetOrder_of_forall_isUnit {R Λ : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    (hΛ : IsMaximalOrder Λ) (u : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (hRΛ : Submodule.localBox R u = Submodule.localBox Λ u)
    (s : (ℍ[ℚ, a, b])ˣ) (sf : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hsf : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ))
    (z : (ℍ[ℚ, a, b])ˣ) (hz : nrd (z : ℍ[ℚ, a, b]) = 1) :
    (z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) ∈ Submodule.localBox (meetOrder R sf) u := by
  have hC : IsOrder (Submodule.conjByFiniteIdele R sf) := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR sf
  have hmemΛ : ∀ y : (ℍ[ℚ, a, b])ˣ, nrd (y : ℍ[ℚ, a, b]) = 1 →
      (y : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) ∈ Submodule.localBox R u := by
    intro y hy
    rw [hRΛ]
    exact tmul_one_mem_localBox_of_isMaximalOrder_of_forall_isUnit hΛ u hdiv (by rw [hy, map_one]; exact one_mem _)

  set E : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ :=
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) with hE
  set E' : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ :=
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u ((sf⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) with hE'
  have hEE' : E * E' = 1 := by rw [hE, hE', ← map_mul, Units.mul_inv, map_one]
  have hE'E : E' * E = 1 := by rw [hE, hE', ← map_mul, Units.inv_mul, map_one]
  have hE's : E' = ((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) := by
    have h1 : ((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) * E = 1 := by
      rw [hsf, Algebra.TensorProduct.tmul_mul_tmul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      rfl
    calc E' = 1 * E' := (one_mul _).symm
      _ = ((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) * E * E' := by rw [h1]
      _ = ((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) := by rw [mul_assoc, hEE', mul_one]
  unfold meetOrder
  rw [Submodule.localBox_inf R (Submodule.conjByFiniteIdele R sf) hR.fg hR.spanTop hC.fg hC.spanTop u]
  refine AddSubgroup.mem_inf.mpr ⟨hmemΛ z hz, ?_⟩
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff R hR.fg hR.spanTop sf u]
  refine ⟨E' * ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) * E, ?_, ?_⟩
  · rw [hE's, hsf, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one,
      ← Units.val_mul, ← Units.val_mul]
    exact hmemΛ (s⁻¹ * z * s) (by rw [nrd_units_mul, nrd_units_mul, nrd_units_inv, hz]; field_simp [nrd_units_ne_zero s])
  · change _ = E * (E' * ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) * E) * E'
    have e : E * (E' * ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) * E) * E' =
        (E * E') * ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) * (E * E') := by simp only [mul_assoc]
    rw [e, hEE', one_mul, mul_one]

theorem toLoc_mem_localBoxUnits_meetOrder_of_forall_isUnit {R Λ : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    (hΛ : IsMaximalOrder Λ) (u : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (hRΛ : Submodule.localBox R u = Submodule.localBox Λ u)
    (s : (ℍ[ℚ, a, b])ˣ) (sf : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hsf : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ))
    (y : (ℍ[ℚ, a, b])ˣ) (hy : nrd (y : ℍ[ℚ, a, b]) = 1) :
    toLoc u y ∈ Submodule.localBoxUnits (meetOrder R sf) u := by
  rw [Submodule.mem_localBoxUnits_iff, coe_toLoc, coe_toLoc_inv]
  exact ⟨tmul_one_mem_localBox_meetOrder_of_forall_isUnit hR hΛ u hdiv hRΛ s sf hsf y hy,
    tmul_one_mem_localBox_meetOrder_of_forall_isUnit hR hΛ u hdiv hRΛ s sf hsf y⁻¹ (by rw [nrd_units_inv, hy, inv_one])⟩

end LevelEll

section Main

theorem main
    {a₁ b₁ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')

    (r rbar : ℕ) [Fact r.Prime] [Fact rbar.Prime] (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hrrbar : rbar ≠ r)
    (hdef₁ : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((r : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)
    (s₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₂ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₂ ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₂ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γ₂ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ₂0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ₂ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat r (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (hΓ₂ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₂ (some ℓ) = Γ₂ none ⊓ (Γ₂ none).map (MulAut.conj (s₂ ℓ)).toMonoidHom)
    (w₂ wbar₂ : HeckeTower.Obj q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (hw₂ : (w₂ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ nrd (w₂ none : ℍ[ℚ, a₁, b₁]) = (r : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂ ∧ nrd (w₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (r : ℚ))
    (hwbar₂ :
      (nrd (wbar₂ none : ℍ[ℚ, a₁, b₁]) = (rbar : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((rbar : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₂ none) ∈ Submodule.localBoxUnits R₁ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox R₁ u ↔
            x ∈ Submodule.localBox R₁ u) ∧
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
            x ∈ Submodule.localBox Λ₁ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (rbar : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((rbar : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₂ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₁ (sf₂ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
              x ∈ Submodule.localBox Λ₁ u))))
    :
    ∀ j : HeckeTower.Obj q q',
      (Γ₂ j).map (MulAut.conj (w₂ j)).toMonoidHom = Γ₂ j ∧
      (Γ₂ j).map (MulAut.conj (wbar₂ j)).toMonoidHom = Γ₂ j ∧
      w₂ j * w₂ j ∈ Γ₂ j ∧
      w₂ j * wbar₂ j * (w₂ j)⁻¹ * (wbar₂ j)⁻¹ ∈ Γ₂ j ∧
      (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom (Units.mk0 (rbar : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : rbar.Prime).ne_zero)))⁻¹ *
          (wbar₂ j * wbar₂ j) ∈ Γ₂ j ∧

      (∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) * (w₂ none)⁻¹ ∈ Γ₂ none ∧
        (s₂ ℓ)⁻¹ * w₂ (some ℓ) * (s₂ ℓ) * (w₂ none)⁻¹ ∈ Γ₂ none ∧
        wbar₂ (some ℓ) * (wbar₂ none)⁻¹ ∈ Γ₂ none ∧
        (s₂ ℓ)⁻¹ * wbar₂ (some ℓ) * (s₂ ℓ) * (wbar₂ none)⁻¹ ∈ Γ₂ none) := by
  have hq'0 : (rbar : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : rbar.Prime).ne_zero

  have hcross : ∀ ℓ : HeckeTower.AwayPrime q q',
      w₂ (some ℓ) * (w₂ none)⁻¹ ∈ Γ₂ none ∧
      (s₂ ℓ)⁻¹ * w₂ (some ℓ) * (s₂ ℓ) * (w₂ none)⁻¹ ∈ Γ₂ none ∧
      wbar₂ (some ℓ) * (wbar₂ none)⁻¹ ∈ Γ₂ none ∧
      (s₂ ℓ)⁻¹ * wbar₂ (some ℓ) * (s₂ ℓ) * (wbar₂ none)⁻¹ ∈ Γ₂ none :=
    ALRel21.block hN hqN hq'N hqq' hq5 hq'5 r rbar hrN hrbarN hrrbar hdef₁ Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ v₂ hv₂ s₂ sf₂ hs₂ Γ₂ hΓ₂0 hΓ₂ℓ
      w₂ wbar₂ hw₂ hwbar₂
  intro j
  cases j with
  | none =>
    obtain ⟨c1, c2, c3, c4⟩ := core (p := r) hΓ₂0 hw₂.1.1 (fun u hu x => (hwbar₂.1.2.2 u hu x).1)
    refine ⟨c1, c2, c3, c4, ?_, hcross⟩
    exact clause5 (p := r) hΓ₂0 hR₁.isOrder.one_mem hq'0 hwbar₂.1.1 hwbar₂.1.2.1
      (fun u hu => by
        rw [Submodule.mem_localBoxUnits_iff, localBox_eq_of_isEichlerOrder_of_mem hdef₁ hR₁ hΛ₁ u hu, ← Submodule.mem_localBoxUnits_iff]
        exact toLoc_mem_localBoxUnits_of_forall_isUnit hΛ₁ u ((hdef₁.2.2 u).mpr hu) _ (nrd_clause5_eq_one hq'0 hwbar₂.1.1))
  | some ℓ =>
    have hAℓ := CerednikDrinfeld.CosetGraph.awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq
      R₁ hR₁.isOrder r v₂ hv₂ (s₂ ℓ) (sf₂ ℓ) (hs₂ ℓ).1
    have hΓℓ' := mem_iff_of_inf_map_conj (p := r) hΓ₂0 (hΓ₂ℓ ℓ) hAℓ
    have hS1 : (1 : ℍ[ℚ, a₁, b₁]) ∈ meetOrder R₁ (sf₂ ℓ) :=
      Submodule.mem_inf.mpr ⟨hR₁.isOrder.one_mem, (QuaternionAlgebra.IsOrder.conjByFiniteIdele R₁ hR₁.isOrder (sf₂ ℓ)).one_mem⟩
    obtain ⟨c1, c2, c3, c4⟩ := core (p := r) hΓℓ' (hw₂.2 ℓ).1 (fun u hu x => ((hwbar₂.2 ℓ).2.2 u hu x).1)
    refine ⟨c1, c2, c3, c4, ?_, hcross⟩
    exact clause5 (p := r) hΓℓ' hS1 hq'0 (hwbar₂.2 ℓ).1 (hwbar₂.2 ℓ).2.1
      (fun u hu =>
        toLoc_mem_localBoxUnits_meetOrder_of_forall_isUnit hR₁.isOrder hΛ₁ u ((hdef₁.2.2 u).mpr hu)
          (localBox_eq_of_isEichlerOrder_of_mem hdef₁ hR₁ hΛ₁ u hu) (s₂ ℓ) (sf₂ ℓ)
          ((hs₂ ℓ).1 u (natCast_not_mem_asIdeal_of_ne (p := r) (p' := rbar) hrrbar u hu)) _
          (nrd_clause5_eq_one hq'0 (hwbar₂.2 ℓ).1))

end Main

end ALREL48

theorem solution
    {a₁ b₁ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')

    (r rbar : ℕ) [Fact r.Prime] [Fact rbar.Prime] (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hrrbar : rbar ≠ r)
    (hdef₁ : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((r : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)
    (s₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₂ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₂ ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₂ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γ₂ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ₂0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ₂ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat r (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (hΓ₂ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₂ (some ℓ) = Γ₂ none ⊓ (Γ₂ none).map (MulAut.conj (s₂ ℓ)).toMonoidHom)
    (w₂ wbar₂ : HeckeTower.Obj q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (hw₂ : (w₂ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ nrd (w₂ none : ℍ[ℚ, a₁, b₁]) = (r : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂ ∧ nrd (w₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (r : ℚ))
    (hwbar₂ :
      (nrd (wbar₂ none : ℍ[ℚ, a₁, b₁]) = (rbar : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((rbar : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₂ none) ∈ Submodule.localBoxUnits R₁ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox R₁ u ↔
            x ∈ Submodule.localBox R₁ u) ∧
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
            x ∈ Submodule.localBox Λ₁ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (rbar : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((rbar : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₂ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₁ (sf₂ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
              x ∈ Submodule.localBox Λ₁ u))))
    :
    ∀ j : HeckeTower.Obj q q',
      (Γ₂ j).map (MulAut.conj (w₂ j)).toMonoidHom = Γ₂ j ∧
      (Γ₂ j).map (MulAut.conj (wbar₂ j)).toMonoidHom = Γ₂ j ∧
      w₂ j * w₂ j ∈ Γ₂ j ∧
      w₂ j * wbar₂ j * (w₂ j)⁻¹ * (wbar₂ j)⁻¹ ∈ Γ₂ j ∧
      (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom (Units.mk0 (rbar : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : rbar.Prime).ne_zero)))⁻¹ *
          (wbar₂ j * wbar₂ j) ∈ Γ₂ j ∧

      (∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) * (w₂ none)⁻¹ ∈ Γ₂ none ∧
        (s₂ ℓ)⁻¹ * w₂ (some ℓ) * (s₂ ℓ) * (w₂ none)⁻¹ ∈ Γ₂ none ∧
        wbar₂ (some ℓ) * (wbar₂ none)⁻¹ ∈ Γ₂ none ∧
        (s₂ ℓ)⁻¹ * wbar₂ (some ℓ) * (s₂ ℓ) * (wbar₂ none)⁻¹ ∈ Γ₂ none) := by
  exact ALREL48.main hN hqN hq'N hqq' hq5 hq'5 r rbar hrN hrbarN hrrbar hdef₁ Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ v₂ hv₂ s₂ sf₂ hs₂ Γ₂ hΓ₂0 hΓ₂ℓ w₂ wbar₂ hw₂ hwbar₂

end S_CerednikDrinfeld_CosetGraph_atkinLehner_relations_levelGroups_place
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_atkinLehner_relations_levelGroups_place (solution)
