-- Prove2me | solution 1 for CerednikDrinfeld.awayUnits_exists_central_vdet_two_and_exists_vdet_one_and_exists_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b3c3306e-49b2-5089-87ba-2533670ab376

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_awayUnits_exists_central_vdet_two_and_exists_vdet_one_and_exists_even

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField MatrixGroups
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

open scoped Classical

noncomputable section

namespace GroupFeedAbstract

section Places

open Rat.HeightOneSpectrum

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

variable (q : ℕ) (hq : q.Prime)

theorem primesEquiv_place : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) (place q hq) = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place : Rat.HeightOneSpectrum.natGenerator (place q hq) = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem q_notMem_asIdeal_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ place q hq) : (q : 𝓞 ℚ) ∉ w.asIdeal := by
  rw [natCast_mem_asIdeal_iff]
  intro h
  have : Rat.HeightOneSpectrum.natGenerator w = q :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).mp h
  apply hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [primesEquiv_place]
  exact Subtype.ext this

theorem eq_place_of_mem (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : w = place q hq := by
  by_contra h
  exact q_notMem_asIdeal_of_ne q hq w h hw

theorem natCast_notMem_of_ne_of_mem (hq' : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)} (hv : (q : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : w ≠ v) : (q : 𝓞 ℚ) ∉ w.asIdeal := by
  rw [eq_place_of_mem q hq' v hv] at hw
  exact q_notMem_asIdeal_of_ne q hq' w hw

theorem valuation_natCast_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 hn

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem algebraMap_inv_natCast_mem_integers_of_valuation (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ)
    (hc : w.valuation ℚ (c : ℚ) = 1) :
    algebraMap ℚ (w.adicCompletion ℚ) ((c : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, valued_algebraMap, hc, inv_one]

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

end Box

section Scalar

variable {a b : ℚ}

local notation "ℍv[" w "]" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ w

theorem coe_toLoc (u : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b])ˣ) :
    ((CosetGraph.toLoc u x : (ℍv[u])ˣ) : ℍv[u]) = (x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ) := rfl

def scalarUnit (c : ℚ) (hc : c ≠ 0) : (ℍ[ℚ, a, b])ˣ :=
  Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 c hc)

theorem coe_scalarUnit (c : ℚ) (hc : c ≠ 0) : ((scalarUnit (a := a) (b := b) c hc : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) =
    algebraMap ℚ ℍ[ℚ, a, b] c := rfl

theorem coe_inv_scalarUnit (c : ℚ) (hc : c ≠ 0) :
    (((scalarUnit (a := a) (b := b) c hc)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = algebraMap ℚ ℍ[ℚ, a, b] c⁻¹ := by
  rw [scalarUnit, Units.coe_map_inv]; rfl

theorem algebraMap_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    (algebraMap ℚ ℍ[ℚ, a, b] r) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem algebraMap_natCast_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (n : ℕ) :
    algebraMap ℚ ℍ[ℚ, a, b] (n : ℚ) ∈ R := by
  rw [map_natCast]
  have h : ((n : ℤ) : ℍ[ℚ, a, b]) ∈ R := by
    rw [← zsmul_one]
    exact R.smul_mem _ hR.one_mem
  exact_mod_cast h

theorem scalarUnit_mem_awayUnits {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (q : ℕ) [hq : Fact q.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    scalarUnit (a := a) (b := b) (q : ℚ) (Nat.cast_ne_zero.mpr hq.out.ne_zero) ∈ CosetGraph.awayUnits R v := by
  unfold CosetGraph.awayUnits
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
  intro w hw
  have hqw : (q : 𝓞 ℚ) ∉ w.asIdeal := natCast_notMem_of_ne_of_mem q hq.out hv hw
  apply Subgroup.subset_closure
  rw [Submodule.mem_localBoxUnits_iff]
  refine ⟨?_, ?_⟩
  · rw [coe_toLoc, coe_scalarUnit]
    exact tmul_mem_localBox R w (algebraMap_natCast_mem hR q) (one_mem _)
  · rw [← map_inv, coe_toLoc, coe_inv_scalarUnit, algebraMap_tmul_one]
    exact tmul_mem_localBox R w hR.one_mem
      (algebraMap_inv_natCast_mem_integers_of_valuation w q (valuation_natCast_eq_one_of_notMem w q hqw))

end Scalar

section DetNrd

variable {K : Type*} [Field K] {a b : ℚ}

theorem mul_self_eq (x : ℍ[ℚ, a, b]) :
    x * x = ((2 * x.re : ℚ) : ℍ[ℚ, a, b]) * x - ((nrd x : ℚ) : ℍ[ℚ, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [nrd_mk]
  ext <;> simp [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe,
    QuaternionAlgebra.imJ_coe, QuaternionAlgebra.imK_coe, -QuaternionAlgebra.coe_pow, -QuaternionAlgebra.coe_mul,
    -QuaternionAlgebra.coe_sub, -QuaternionAlgebra.coe_add] <;> ring

theorem matrix_mul_self_eq (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem eq_coe_re_of_comm (ha : a ≠ 0) (x : ℍ[ℚ, a, b])
    (hi : x * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * x) (hj : x * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * x) :
    x = ((x.re : ℚ) : ℍ[ℚ, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk.injEq] at hi hj
  have h2 : x₂ = 0 := by
    obtain ⟨-, -, -, h⟩ := hi
    linarith
  have h3 : x₃ = 0 := by
    obtain ⟨-, -, h, -⟩ := hi
    have : a * x₃ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left ha
  have h1 : x₁ = 0 := by
    obtain ⟨-, -, -, h⟩ := hj
    linarith
  subst h1 h2 h3
  ext <;> simp

variable [CharZero K]

theorem map_coe_eq_smul_one (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K) (r : ℚ) :
    ι ((r : ℚ) : ℍ[ℚ, a, b]) = algebraMap ℚ K r • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [← QuaternionAlgebra.coe_algebraMap, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, algebraMap_smul]

theorem det_map_eq_algebraMap_nrd (ha : a ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K) (hι : Function.Injective ι) (x : ℍ[ℚ, a, b]) :
    (ι x).det = algebraMap ℚ K (nrd x) := by
  set M := ι x with hM
  have h1 : M * M = algebraMap ℚ K (2 * x.re) • M - algebraMap ℚ K (nrd x) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h := congrArg ι (mul_self_eq x)
    rw [map_mul, map_sub, map_mul, map_coe_eq_smul_one, map_coe_eq_smul_one, smul_mul_assoc, one_mul] at h
    exact h
  have h2 := matrix_mul_self_eq M
  have h3 : (M.trace - algebraMap ℚ K (2 * x.re)) • M = (M.det - algebraMap ℚ K (nrd x)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [sub_smul, sub_smul]
    have := h1.symm.trans h2
    rw [sub_eq_sub_iff_sub_eq_sub] at this
    rw [← neg_sub, ← neg_sub (M.det • (1 : Matrix (Fin 2) (Fin 2) K)), neg_inj] at this
    exact this
  by_cases htr : M.trace = algebraMap ℚ K (2 * x.re)
  · rw [htr, sub_self, zero_smul] at h3
    have h4 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) h3
    simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
    exact (sub_eq_zero.mp h4.symm)
  · have hne : M.trace - algebraMap ℚ K (2 * x.re) ≠ 0 := sub_ne_zero.mpr htr
    have hMs : M = ((M.trace - algebraMap ℚ K (2 * x.re))⁻¹ * (M.det - algebraMap ℚ K (nrd x))) •
        (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hcomm : ∀ y : ℍ[ℚ, a, b], x * y = y * x := by
      intro y
      apply hι
      rw [map_mul, map_mul, ← hM, hMs, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    have hx : x = ((x.re : ℚ) : ℍ[ℚ, a, b]) := eq_coe_re_of_comm ha x (hcomm _) (hcomm _)
    rw [hM, hx, map_coe_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, nrd_coe, map_pow]

theorem coe_det_unitsMap (ha : a ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K) (hι : Function.Injective ι) (x : (ℍ[ℚ, a, b])ˣ) :
    ((Matrix.GeneralLinearGroup.det (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) K) x) : Kˣ) : K) =
      algebraMap ℚ K (nrd (x : ℍ[ℚ, a, b])) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  exact det_map_eq_algebraMap_nrd ha ι hι x

end DetNrd

section EvenPart

def evenPart {G : Type*} [Group G] (φ : G →* Multiplicative ℤ) : Subgroup G where
  carrier := {x | Even (Multiplicative.toAdd (φ x))}
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, toAdd_one, Even.zero]
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, map_mul, toAdd_mul] at hx hy ⊢
    exact hx.add hy
  inv_mem' {x} hx := by
    simp only [Set.mem_setOf_eq, map_inv, toAdd_inv] at hx ⊢
    exact hx.neg

theorem mem_evenPart {G : Type*} [Group G] (φ : G →* Multiplicative ℤ) (x : G) :
    x ∈ evenPart φ ↔ Even (Multiplicative.toAdd (φ x)) := Iff.rfl

end EvenPart

end GroupFeedAbstract

end

open GroupFeedAbstract in
theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {rbar N : ℕ} [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsEichlerOrder R₁ N)
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (wodd : (ℍ[ℚ, a₁, b₁])ˣ) (hwodd : wodd ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v) (hwodd_nrd : nrd (wodd : ℍ[ℚ, a₁, b₁]) = (r : ℚ)) :
    (∃ z ∈ Γt, ∃ c : K₀, (((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z) = Multiplicative.ofAdd (2 : ℤ)) ∧
    (∃ w ∈ Γt, vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) w) = Multiplicative.ofAdd (1 : ℤ)) ∧
    (∃ Γt' : Subgroup (ℍ[ℚ, a₁, b₁])ˣ, ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt' ↔ x ∈ Γt ∧ Even (Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) x)))) := by
  have hrP : r.Prime := Fact.out
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hrP.ne_zero
  have hR₁o : QuaternionAlgebra.IsOrder R₁ := hR₁.isOrder
  have ha₁ : a₁ ≠ 0 := ne_of_lt hdef.1

  obtain ⟨u, hu⟩ : ∃ u : 𝒪ˣ, ((r : ℕ) : 𝒪) = (u : 𝒪) * π := by
    obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp hunr).symm
    exact ⟨u, by rw [← hu, mul_comm]⟩
  have hrK : ((r : ℕ) : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * algebraMap 𝒪 K₀ π := by
    rw [← map_natCast (algebraMap 𝒪 K₀), hu, map_mul]

  set z : (ℍ[ℚ, a₁, b₁])ˣ := scalarUnit (a := a₁) (b := b₁) (r : ℚ) hr0 with hz
  have hzΓ : z ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v := scalarUnit_mem_awayUnits hR₁o r v hv
  have hzmat : (((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z :
      Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = ((r : ℕ) : K₀) • (1 : Matrix (Fin 2) (Fin 2) K₀) := by
    rw [Units.coe_map, MonoidHom.coe_coe, coe_scalarUnit, AlgHom.commutes, map_natCast, Nat.cast_smul_eq_nsmul,
      Nat.smul_one_eq_cast]
  have hzdet : ((Matrix.GeneralLinearGroup.det ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z) : K₀ˣ) : K₀) =
      algebraMap 𝒪 K₀ ((u ^ 2 : 𝒪ˣ) : 𝒪) * (algebraMap 𝒪 K₀ π) ^ (2 : ℤ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hzmat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
      hrK, Units.val_pow_eq_pow_val, map_pow, zpow_two]
    ring
  have hzv : vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z) = Multiplicative.ofAdd (2 : ℤ) :=
    (hvdet _ 2).mpr ⟨u ^ 2, hzdet⟩

  have hwdet : ((Matrix.GeneralLinearGroup.det ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) wodd) : K₀ˣ) : K₀) =
      algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ (1 : ℤ) := by
    rw [coe_det_unitsMap ha₁ ι₀ hι₀ wodd, hwodd_nrd, map_natCast, hrK, zpow_one]
  have hwv : vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) wodd) = Multiplicative.ofAdd (1 : ℤ) :=
    (hvdet _ 1).mpr ⟨u, hwdet⟩
  refine ⟨⟨z, (hΓt z).mpr hzΓ, ((r : ℕ) : K₀), hzmat, hzv⟩, ⟨wodd, (hΓt wodd).mpr hwodd, hwv⟩, ?_⟩

  refine ⟨Γt ⊓ evenPart (vdet.comp (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀))), fun x => ?_⟩
  rw [Subgroup.mem_inf, mem_evenPart, MonoidHom.comp_apply]

end S_CerednikDrinfeld_awayUnits_exists_central_vdet_two_and_exists_vdet_one_and_exists_even
end P2MW
export P2MW.S_CerednikDrinfeld_awayUnits_exists_central_vdet_two_and_exists_vdet_one_and_exists_even (solution)
