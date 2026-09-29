-- Prove2me | solution 1 for CerednikDrinfeld.exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d00daaa4-13c8-56ac-92f3-47b84df799f2

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_det_ringEquiv_tmul_one_eq_algebraMap_nrd
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "CosetGraph.exists_units_nrd_eq_prime_forall_mem_localBox meetOrder"
namespace CosetGraph
p2m_export "CerednikDrinfeld.CosetGraph" "Loc toLoc level awayUnits exists_units_nrd_eq_prime_forall_mem_localBox"
namespace SExist
p2m_open "CerednikDrinfeld.CosetGraph CerednikDrinfeld"

variable {a b : ℚ}

local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem isMaximal_span_natCast_of_prime {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpO : _root_.Prime (p : 𝓞 ℚ) := by
    have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
    rw [this]
    exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
  have hprime : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsPrime := (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  refine hprime.isMaximal ?_
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

theorem eq_of_natCast_prime_mem {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hv' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have hmax := isMaximal_span_natCast_of_prime hp
  have h1 : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  have h2 : v'.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v'.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv')).symm
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

theorem natCast_not_mem_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : (q : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hqv
  have hcop : IsCoprime (p : 𝓞 ℚ) (q : 𝓞 ℚ) := by
    have := (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq) : IsCoprime (p : ℤ) (q : ℤ))
    simpa using this.map (Int.castRingHom (𝓞 ℚ))
  obtain ⟨x, y, hxy⟩ := hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hxy]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hqv)

theorem v_algebraMap_natCast_eq_one {r : ℕ} {w : HeightOneSpectrum (𝓞 ℚ)} (hw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (r : ℚ)) = 1 := by
  rw [show Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (r : ℚ)) = w.valuation ℚ (r : ℚ) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
  have : (r : ℚ) = algebraMap (𝓞 ℚ) ℚ (r : 𝓞 ℚ) := by simp
  rw [this, HeightOneSpectrum.valuation_of_algebraMap]
  have hle := w.intValuation_le_one (r : 𝓞 ℚ)
  have hnlt : ¬ w.intValuation (r : 𝓞 ℚ) < 1 := by
    rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hw
  exact le_antisymm hle (not_lt.mp hnlt)

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

theorem unitsMap_finiteAdeleEvalAt_diagonal (w : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ) =
      toLoc w γ := by
  apply Units.ext
  rw [Units.coe_map]
  show (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w) ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ : (𝔸ℍ)ˣ) : 𝔸ℍ) =
    Algebra.TensorProduct.includeLeft (γ : ℍ[ℚ, a, b])
  rw [Submodule.val_finiteIdeleDiagonal_apply, Submodule.finiteAdeleEvalAt_tmul, Algebra.TensorProduct.includeLeft_apply]
  rfl

theorem evU_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℍ)ˣ) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom (x * y) =
      Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom x *
        Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom y :=
  MonoidHom.map_mul _ x y

theorem evU_inv (w : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℍ)ˣ) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom x⁻¹ =
      (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom x)⁻¹ :=
  MonoidHom.map_inv _ x

theorem diag_mul (x y : (ℍ[ℚ, a, b])ˣ) :
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (x * y) =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] x * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] y :=
  MonoidHom.map_mul _ x y

theorem diag_inv (x : (ℍ[ℚ, a, b])ˣ) :
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] x⁻¹ = (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] x)⁻¹ :=
  MonoidHom.map_inv _ x

theorem nrd_mul {K : Type*} [CommRing K] {a' b' : K} (x y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

def unitOfNrd (x : ℍ[ℚ, a, b]) (hx : QuaternionAlgebra.nrd x ≠ 0) : (ℍ[ℚ, a, b])ˣ where
  val := x
  inv := (QuaternionAlgebra.nrd x)⁻¹ • star x
  val_inv := by
    rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd]
    ext <;> simp [hx]
  inv_val := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd]
    ext <;> simp [hx]

@[scoped simp] theorem val_unitOfNrd (x : ℍ[ℚ, a, b]) (hx : QuaternionAlgebra.nrd x ≠ 0) :
    ((unitOfNrd x hx : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = x := rfl

theorem nrd_val_inv (B : (ℍ[ℚ, a, b])ˣ) :
    QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]))⁻¹ := by
  have h : QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]) * QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
    rw [← nrd_mul, Units.mul_inv, QuaternionAlgebra.nrd_one]
  exact (eq_inv_of_mul_eq_one_right h)

theorem nrd_coords {w : HeightOneSpectrum (𝓞 ℚ)} (z : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd ((⟨algebraMap ℚ (w.adicCompletion ℚ) z.re, algebraMap ℚ (w.adicCompletion ℚ) z.imI,
        algebraMap ℚ (w.adicCompletion ℚ) z.imJ, algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])) =
      algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd z) := by
  rw [QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd]
  simp only [map_sub, map_add, map_mul, map_pow]

theorem coord_evalAt_tmul_one {w : HeightOneSpectrum (𝓞 ℚ)}
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (hφ : ∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
        algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
        algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]))
    (z : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)))) =
      algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd z) := by
  rw [Submodule.finiteAdeleEvalAt_tmul, show ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) w) = 1 from rfl, hφ, one_smul, nrd_coords]

theorem mat_smul_mul {v : HeightOneSpectrum (𝓞 ℚ)} (c : v.adicCompletion ℚ)
    (M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : (c • M) * N = c • (M * N) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cayley_hamilton_two {v : HeightOneSpectrum (𝓞 ℚ)} (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    X * X = X.trace • X - X.det • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem mul_self_eq' {K : Type*} [CommRing K] {a' b' : K} (x : ℍ[K, a', b']) :
    x * x = (QuaternionAlgebra.trd x) • x - (QuaternionAlgebra.nrd x) • (1 : ℍ[K, a', b']) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd, QuaternionAlgebra.trd] <;> ring

section LocalDetNrd

variable {v : HeightOneSpectrum (𝓞 ℚ)}
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (hφ : ∀ t : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
  (ψ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hψ : ∀ (z : ℍ[ℚ, a, b]) (t : v.adicCompletion ℚ),
      ψ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re,
        algebraMap ℚ (v.adicCompletion ℚ) z.imI, algebraMap ℚ (v.adicCompletion ℚ) z.imJ,
        algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))

include hψ in
theorem psi_one_tmul (t : v.adicCompletion ℚ) :
    ψ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) =
      ((t : v.adicCompletion ℚ) : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) := by
  rw [hψ]
  ext <;> simp

include hψ in

theorem symm_smul (t : v.adicCompletion ℚ)
    (ξ : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) :
    ψ.symm (t • ξ) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) * ψ.symm ξ := by
  apply ψ.injective
  rw [ψ.apply_symm_apply, ψ.map_mul, psi_one_tmul ψ hψ, ψ.apply_symm_apply, QuaternionAlgebra.coe_mul_eq_smul]

include hφ hψ in

theorem det_eq_nrd (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    (φ x).det = QuaternionAlgebra.nrd (ψ x) := by
  set ξ := ψ x with hξ
  have hx : x = ψ.symm ξ := by rw [hξ, ψ.symm_apply_apply]

  have hrel : φ x * φ x = QuaternionAlgebra.trd ξ • φ x - QuaternionAlgebra.nrd ξ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    have h0 : x * x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] QuaternionAlgebra.trd ξ) * x - ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] QuaternionAlgebra.nrd ξ) := by
      have := congrArg ψ.symm (mul_self_eq' ξ)
      rw [ψ.symm.map_mul, ψ.symm.map_sub, symm_smul ψ hψ, symm_smul ψ hψ, ψ.symm.map_one, mul_one, ← hx] at this
      exact this
    rw [← φ.map_mul, h0, φ.map_sub, φ.map_mul, hφ, hφ, mat_smul_mul, one_mul]
  have hCH := cayley_hamilton_two (φ x)
  have hdiff : (QuaternionAlgebra.trd ξ - (φ x).trace) • φ x =
      (QuaternionAlgebra.nrd ξ - (φ x).det) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_sub_eq_sub, ← hrel, ← hCH]
  by_cases hs : QuaternionAlgebra.trd ξ - (φ x).trace = 0
  · rw [hs, zero_smul] at hdiff
    have h00 := congrFun (congrFun hdiff 0) 0
    simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    exact (sub_eq_zero.mp h00.symm).symm
  ·
    have hXs : φ x = ((QuaternionAlgebra.trd ξ - (φ x).trace)⁻¹ * (QuaternionAlgebra.nrd ξ - (φ x).det)) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) => (QuaternionAlgebra.trd ξ - (φ x).trace)⁻¹ • M) hdiff
      simp only [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
      exact this
    obtain ⟨c, hc⟩ : ∃ c : v.adicCompletion ℚ, φ x = c • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := ⟨_, hXs⟩
    have hx1 : x = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c := by
      apply φ.injective; rw [hc, hφ]
    have hξc : ξ = ((c : v.adicCompletion ℚ) : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a,
        algebraMap ℚ (v.adicCompletion ℚ) b]) := by rw [hξ, hx1, psi_one_tmul ψ hψ]
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hξc, QuaternionAlgebra.nrd_coe]

end LocalDetNrd

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  unfold Submodule.localBox
  rw [Algebra.TensorProduct.one_def]
  exact AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

theorem dvd_of_natCast_mem {p : ℕ} (hp : p.Prime) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    {N : ℕ} (hN : (N : 𝓞 ℚ) ∈ v.asIdeal) : p ∣ N := by
  have h1 : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    ((isMaximal_span_natCast_of_prime hp).eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  rw [h1, Ideal.mem_span_singleton] at hN
  obtain ⟨c, hc⟩ := hN
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have h : (N : ℤ) = (p : ℤ) * e c := by
    have := congrArg e hc
    rwa [map_natCast, map_mul, map_natCast] at this
  exact Int.natCast_dvd_natCast.mp ⟨e c, h⟩

def placeOver (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {(p : 𝓞 ℚ)}
  isPrime := (isMaximal_span_natCast_of_prime hp).isPrime
  ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero

theorem natCast_mem_placeOver (p : ℕ) (hp : p.Prime) : ((p : ℕ) : 𝓞 ℚ) ∈ (placeOver p hp).asIdeal :=
  Ideal.mem_span_singleton_self _

theorem tmul_one_mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem ratSmul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ)) {c : ℚ}
    (hc : algebraMap ℚ (w.adicCompletion ℚ) c ∈ w.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ w) : c • x ∈ Submodule.localBox Λ w := by
  have e : c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) * x := by
    have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) = c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rw [e1, smul_mul_assoc, one_mul]
  rw [e]
  exact tmul_one_mul_mem_localBox w hc hx

theorem ev_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : 𝔸ℍ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x * y) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w y :=
  map_mul _ x y

theorem ev_ratSmul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : 𝔸ℍ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (c • x) = c • Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x :=
  map_smul (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w) c x

theorem algebraMap_natCast_mem {p : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) :
    algebraMap ℚ (w.adicCompletion ℚ) (p : ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [map_natCast]; exact natCast_mem _ _

theorem algebraMap_inv_natCast_not_mem {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ)⁻¹) ∉ v.adicCompletionIntegers ℚ := by
  intro h
  have hlt : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) < 1 := by
    rw [show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) = v.valuation ℚ (p : ℚ) from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _]
    have : (p : ℚ) = algebraMap (𝓞 ℚ) ℚ (p : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hv
  have hp0 : algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap ℚ (v.adicCompletion ℚ)).injective]
    exact_mod_cast hp.ne_zero
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀] at h
  have hv0 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hp0
  have h1 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) * (Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)))⁻¹ = 1 :=
    mul_inv_cancel₀ hv0
  have : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) :=
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
      _ ≤ Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) * 1 := mul_le_mul_right h _
      _ = _ := mul_one _
  exact not_lt.mpr this hlt

def pU (p : ℕ) [Fact p.Prime] : (ℍ[ℚ, a, b])ˣ :=
  Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

theorem val_diag_pU (p : ℕ) [Fact p.Prime] :
    ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p) : (𝔸ℍ)ˣ) : 𝔸ℍ) = (p : ℚ) • (1 : 𝔸ℍ) := by
  rw [Submodule.val_finiteIdeleDiagonal_apply]
  show ((algebraMap ℚ ℍ[ℚ, a, b] (p : ℚ)) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) = _
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', ← Algebra.TensorProduct.one_def]

theorem val_diag_pU_inv (p : ℕ) [Fact p.Prime] :
    (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p))⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = (p : ℚ)⁻¹ • (1 : 𝔸ℍ) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h : (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p) : 𝔸ℍ) * ((p : ℚ)⁻¹ • (1 : 𝔸ℍ)) = 1 := by
    rw [val_diag_pU, smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hp0, one_smul]
  exact Units.inv_eq_of_mul_eq_one_right h

section Mat

variable {w : HeightOneSpectrum (𝓞 ℚ)}

theorem det_mem (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) (hM : ∀ i j, M i j ∈ w.adicCompletionIntegers ℚ) :
    M.det ∈ w.adicCompletionIntegers ℚ := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

theorem adjugate_mem (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) (hM : ∀ i j, M i j ∈ w.adicCompletionIntegers ℚ) :
    ∀ i j, M.adjugate i j ∈ w.adicCompletionIntegers ℚ := by
  intro i j
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact hM 1 1
  · exact neg_mem (hM 0 1)
  · exact neg_mem (hM 1 0)
  · exact hM 0 0

theorem smul_inv_eq_adjugate (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) {d : w.adicCompletion ℚ} (hd : M.det = d)
    (hd0 : d ≠ 0) : d • M⁻¹ = M.adjugate := by
  rw [Matrix.inv_def, hd, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hd0, one_smul]

theorem smul_det (c : w.adicCompletion ℚ) (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) : (c • M).det = c ^ 2 * M.det := by
  rw [Matrix.det_smul, Fintype.card_fin]

end Mat

theorem map_ratSmul {w : HeightOneSpectrum (𝓞 ℚ)}
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
    (hφ : ∀ t : w.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)))
    (r : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : φ (r • x) = (algebraMap ℚ (w.adicCompletion ℚ) r) • φ x := by
  have e : r • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) r) * x := by
    have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) r) = r • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rw [e1, smul_mul_assoc, one_mul]
  rw [e, φ.map_mul, hφ, mat_smul_mul, one_mul]

theorem main {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hq'5 : 5 ≤ q') (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (n : (𝔸ℍ)ˣ) (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (hS : QuaternionAlgebra.IsEichlerOrder (meetOrder R n) (N * q))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N * q * q') :
    ∃ (s : (ℍ[ℚ, a, b])ˣ) (sf : (𝔸ℍ)ˣ),
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : 𝔸ℍ) = (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : 𝔸ℍ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) ℓ) * sf⁻¹ ∈
        QuaternionAlgebra.primeHeckeSet (meetOrder R n) ℓ ∧
      QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = (ℓ : ℚ) := by
  classical
  have hqp : q.Prime := Fact.out
  have hq'p : q'.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
  have hq'2 : q' ≠ 2 := by omega
  have hℓNq : ¬ ℓ ∣ N * q := fun h => hℓ (Dvd.dvd.mul_right h q')
  have hℓq : ℓ ≠ q := by rintro rfl; exact hℓNq (Dvd.intro_left N rfl)
  have hℓq' : ℓ ≠ q' := by rintro rfl; exact hℓ (Dvd.intro_left (N * q) rfl)
  set S := meetOrder R n with hSdef
  have hSo : QuaternionAlgebra.IsOrder S := hS.isOrder
  have boxS := fun z => Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox S hSo.fg hSo.spanTop z

  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := ⟨placeOver q hqp, natCast_mem_placeOver q hqp⟩
  have hwv : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → w ≠ v := fun w hw h => hw (h ▸ hv)
  obtain ⟨vl, hvl⟩ : ∃ vl : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∈ vl.asIdeal := ⟨placeOver ℓ hℓp, natCast_mem_placeOver ℓ hℓp⟩
  have hvlv : vl ≠ v := fun h => natCast_not_mem_of_ne hℓp hqp hℓq hvl (h ▸ hv)

  have hq'vl : (q' : 𝓞 ℚ) ∉ vl.asIdeal := natCast_not_mem_of_ne hℓp hq'p hℓq' hvl
  have hNqvl : ((N * q : ℕ) : 𝓞 ℚ) ∉ vl.asIdeal := fun h => hℓNq (dvd_of_natCast_mem hℓp hvl h)
  obtain ⟨φ, hφ, hφS⟩ := QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef hS vl hq'vl hNqvl

  obtain ⟨s, hsint, hsunit, hsnrd⟩ :=
    CerednikDrinfeld.CosetGraph.exists_units_nrd_eq_prime_forall_mem_localBox hq'2 hdef hS hqq'.symm v hv hℓq' hℓNq

  have hy : (((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) * ((s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.inv_mul, ← Algebra.TensorProduct.one_def]
  have hy' : ((s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) * (((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.mul_inv, ← Algebra.TensorProduct.one_def]
  obtain ⟨c, hcv, -, hcw⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq_of_forall_ne S hSo.fg hSo.spanTop v _ _ hy hy' 1
    (fun w _ => ⟨by rw [Units.val_one, map_one]; exact one_mem_localBox hSo w,
      by rw [inv_one, Units.val_one, map_one]; exact one_mem_localBox hSo w⟩)
  have hcU : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom c = 1 := by
    intro w hw; apply Units.ext; have h1 := (hcw w hw).1; rwa [Units.val_one, map_one] at h1
  set sf : (𝔸ℍ)ˣ := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] s * c with hsf

  have hsfU : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom sf = toLoc w s := by
    intro w hw
    rw [hsf, evU_mul, unitsMap_finiteAdeleEvalAt_diagonal, hcU w hw, mul_one]
  have hsf_w : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : 𝔸ℍ) = (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
    intro w hw
    exact congrArg Units.val (hsfU w hw)
  have hsfi_w : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((sf⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = ((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
    intro w hw
    have := congrArg Units.val ((evU_inv w sf).trans (congrArg Inv.inv (hsfU w hw)))
    rw [← map_inv] at this
    exact this
  have hsf_v : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (sf : 𝔸ℍ) = 1 := by
    have hU : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom sf =
        toLoc v s * Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom c := by
      rw [hsf, evU_mul, unitsMap_finiteAdeleEvalAt_diagonal]
    have h := congrArg Units.val hU
    rw [Units.val_mul] at h
    rw [show Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (sf : 𝔸ℍ) =
      ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom sf : (Loc a b v)ˣ) : Loc a b v) from rfl, h]
    show ((s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (c : 𝔸ℍ) = 1
    rw [hcv]; exact hy'
  have hsfi_v : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((sf⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = 1 := by
    have h1 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((sf⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (sf : 𝔸ℍ) = 1 := by
      rw [← ev_mul, Units.inv_mul, map_one]
    rwa [hsf_v, mul_one] at h1

  set M : Matrix (Fin 2) (Fin 2) (vl.adicCompletion ℚ) := φ ((s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : vl.adicCompletion ℚ)) with hM
  have hMint : ∀ i j, M i j ∈ vl.adicCompletionIntegers ℚ := (hφS _).mp (hsint vl hvlv)
  have hMdet : M.det = algebraMap ℚ (vl.adicCompletion ℚ) (ℓ : ℚ) := by
    rw [hM, QuaternionAlgebra.det_ringEquiv_tmul_one_eq_algebraMap_nrd vl φ hφ, hsnrd]
  have hℓK0 : algebraMap ℚ (vl.adicCompletion ℚ) (ℓ : ℚ) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap ℚ (vl.adicCompletion ℚ)).injective]; exact hℓ0
  have hMinv : φ (((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : vl.adicCompletion ℚ)) = M⁻¹ := by
    have h1 : φ (((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : vl.adicCompletion ℚ)) * M = 1 := by
      rw [hM, ← φ.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.inv_mul, ← Algebra.TensorProduct.one_def, φ.map_one]
    exact (Matrix.inv_eq_left_inv h1).symm

  have hval : ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) ℓ) * sf⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = (ℓ : ℚ) • ((sf⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) := by
    rw [Units.val_mul, val_diag_pU, smul_mul_assoc, one_mul]
  have hvali : (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) ℓ) * sf⁻¹)⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = (ℓ : ℚ)⁻¹ • (sf : 𝔸ℍ) := by
    rw [mul_inv_rev, inv_inv, Units.val_mul, val_diag_pU_inv, mul_smul_comm, mul_one]

  have hsf_box : (sf : 𝔸ℍ) ∈ Submodule.finiteAdeleBox S := by
    rw [boxS]
    intro w
    by_cases hw : w = v
    · subst hw; rw [hsf_v]; exact one_mem_localBox hSo _
    · rw [hsf_w w hw]; exact hsint w hw
  refine ⟨s, sf, fun w hw => hsf_w w (hwv w hw), fun w hw => ?_, ⟨?_, ?_, ?_, ?_⟩, hsnrd⟩
  · have : w = v := eq_of_natCast_prime_mem hqp hw hv
    subst this; exact hsf_v
  ·
    rw [hval, boxS]
    intro w
    rw [ev_ratSmul]
    by_cases hw : w = v
    · subst hw; rw [hsfi_v]; exact ratSmul_mem_localBox _ (algebraMap_natCast_mem _) (one_mem_localBox hSo _)
    · rw [hsfi_w w hw]
      by_cases hwl : w = vl
      · subst hwl
        rw [hφS]
        intro i j
        rw [map_ratSmul φ hφ, hMinv, smul_inv_eq_adjugate M hMdet hℓK0]
        exact adjugate_mem M hMint i j
      · have hu := hsunit w hw (fun h => hwl (eq_of_natCast_prime_mem hℓp h hvl))
        have : (((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = (((toLoc w s)⁻¹ : (Loc a b w)ˣ) : Loc a b w) := by
          rw [← map_inv]; rfl
        rw [this]
        exact ratSmul_mem_localBox _ (algebraMap_natCast_mem _) hu.2
  ·
    rw [hvali, smul_smul, mul_inv_cancel₀ hℓ0, one_smul]; exact hsf_box
  ·
    rw [hvali, boxS]
    intro h
    have h1 := h vl
    rw [ev_ratSmul, hsf_w vl hvlv, hφS] at h1
    have hdet := det_mem _ h1
    rw [map_ratSmul φ hφ, ← hM, smul_det, hMdet, ← map_pow, ← map_mul,
      show ((ℓ : ℚ)⁻¹) ^ 2 * (ℓ : ℚ) = (ℓ : ℚ)⁻¹ by field_simp] at hdet
    exact algebraMap_inv_natCast_not_mem hℓp vl hvl hdet
  ·
    rw [hval, smul_smul, inv_mul_cancel₀ hℓ0, one_smul, boxS]
    intro h
    have h1 := h vl
    rw [hsfi_w vl hvlv, hφS] at h1
    have hdet := det_mem _ h1
    rw [hMinv, Matrix.det_nonsing_inv, hMdet, Ring.inverse_eq_inv', ← map_inv₀] at hdet
    exact algebraMap_inv_natCast_not_mem hℓp vl hvl hdet

end CerednikDrinfeld.CosetGraph.SExist
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld.CosetGraph P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld.CosetGraph.SExist"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld.CosetGraph"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld.CosetGraph P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld.CosetGraph.SExist"

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.CerednikDrinfeld QuaternionAlgebra in
theorem solution
    {a b : ℚ} {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hq'5 : 5 ≤ q') (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N * q * q') :
    ∃ (s : (ℍ[ℚ, a, b])ˣ) (sf : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ),
      (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), ((q : ℕ) : NumberField.RingOfIntegers ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) =
          (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∧
      (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), ((q : ℕ) : NumberField.RingOfIntegers ℚ) ∈ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * sf⁻¹ ∈
        primeHeckeSet (meetOrder R n) ℓ ∧
      QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = (ℓ : ℚ) :=
  CerednikDrinfeld.CosetGraph.SExist.main hqq' hq'5 hdef R hR n hn hS ℓ hℓ

end S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd (solution)
