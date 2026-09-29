-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.exists_units_nrd_eq_prime_forall_mem_localBox
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2701afbe-a679-51fa-944f-cfbac2c032cf

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_nrd_eq_of_pos
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
namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "CosetGraph.Loc CosetGraph.toLoc"
namespace CosetGraph
p2m_export "CerednikDrinfeld.CosetGraph" "Loc toLoc awayUnits"
namespace NormL
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

open Classical in

theorem ynorm {ℓ : ℕ} (hℓ0 : (ℓ : ℚ) ≠ 0) (B₀ : (ℍ[ℚ, a, b])ˣ) (hB₀ : QuaternionAlgebra.nrd (B₀ : ℍ[ℚ, a, b]) = (ℓ : ℚ))
    (vl : HeightOneSpectrum (𝓞 ℚ)) (x m : (𝔸ℍ)ˣ)
    (hxnrd : ∀ w : HeightOneSpectrum (𝓞 ℚ), w = vl → ∀ ψ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
          ψ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (ψ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ))) = algebraMap ℚ (w.adicCompletion ℚ) (ℓ : ℚ))
    (hxw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ vl → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ) = 1)
    (hm : ∀ w : HeightOneSpectrum (𝓞 ℚ), ∀ ψ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
          ψ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (ψ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (m : 𝔸ℍ))) =
          algebraMap ℚ (w.adicCompletion ℚ) (if w = vl then (1 : ℚ) else (ℓ : ℚ)))
    (w : HeightOneSpectrum (𝓞 ℚ)) : ∀ ψ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
          ψ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (ψ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
          (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀)⁻¹ * x * m : (𝔸ℍ)ˣ) : 𝔸ℍ))) = 1 := by
  classical
  intro ψ hψ
  have hev : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀)⁻¹ * x * m : (𝔸ℍ)ˣ) : 𝔸ℍ) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (((B₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) *
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (m : 𝔸ℍ) := by
    rw [Units.val_mul, Units.val_mul, ← diag_inv, Submodule.val_finiteIdeleDiagonal_apply, map_mul, map_mul]
  rw [hev, ψ.map_mul, ψ.map_mul, nrd_mul, nrd_mul, coord_evalAt_tmul_one ψ hψ, hm w ψ hψ, nrd_val_inv, hB₀]
  by_cases hw : w = vl
  · rw [hxnrd w hw ψ hψ, if_pos hw, map_one, mul_one, ← map_mul, inv_mul_cancel₀ hℓ0, map_one]
  · rw [if_neg hw, hxw w hw, ψ.map_one, QuaternionAlgebra.nrd_one, mul_one, ← map_mul, inv_mul_cancel₀ hℓ0, map_one]

theorem assembly {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R) {ℓ : ℕ}
    (v vl : HeightOneSpectrum (𝓞 ℚ)) (hvl : ((ℓ : ℕ) : 𝓞 ℚ) ∈ vl.asIdeal) (hℓ : ℓ.Prime)
    (S : (ℍ[ℚ, a, b])ˣ) (x m u g : (𝔸ℍ)ˣ)
    (key : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] S = x * m * u⁻¹ * g⁻¹)
    (hxint : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] vl (x : 𝔸ℍ) ∈ Submodule.localBox R vl)
    (hxw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ vl → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ) = 1)
    (hmS : m ∈ Submodule.finiteIdeleStabilizer R) (huS : u ∈ Submodule.finiteIdeleStabilizer R)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : 𝔸ℍ) = 1) :
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((toLoc w S : (Loc a b w)ˣ) : Loc a b w) ∈ Submodule.localBox R w) ∧
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → toLoc w S ∈ Submodule.localBoxUnits R w) := by
  have hmw := fun w => ((QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      R hRo m).mp hmS) w
  have huw := fun w => ((QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      R hRo u).mp huS) w
  have hgw : ∀ w, w ≠ v → Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom g = 1 :=
    fun w hw => Units.ext (hg w hw)
  have hcomp : ∀ w, w ≠ v → toLoc w S =
      Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom x *
        (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom m *
          (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom u)⁻¹) := by
    intro w hw
    rw [← unitsMap_finiteAdeleEvalAt_diagonal, key, evU_mul, evU_mul, evU_mul, evU_inv, evU_inv, hgw w hw, inv_one, mul_one,
      mul_assoc]
  have hmu : ∀ w, Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom m *
      (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom u)⁻¹ ∈ localUnits hRo w :=
    fun w => (localUnits hRo w).mul_mem (hmw w) ((localUnits hRo w).inv_mem (huw w))
  have hx1 : ∀ w, w ≠ vl → Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom x = 1 :=
    fun w hw => Units.ext (hxw w hw)
  refine ⟨fun w hw => ?_, fun w hw hwl => ?_⟩
  · rw [hcomp w hw, Units.val_mul]
    by_cases hwl' : w = vl
    · subst hwl'
      exact localBox_mul_mem hRo _ hxint (hmu _).1
    · rw [hx1 w hwl', Units.val_one, one_mul]
      exact (hmu w).1
  · have hwl' : w ≠ vl := fun h => hwl (h ▸ hvl)
    rw [hcomp w hw, hx1 w hwl', one_mul]
    exact hmu w

theorem main {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓN : ¬ ℓ ∣ N) :
    ∃ s : (ℍ[ℚ, a, b])ˣ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((toLoc w s : (Loc a b w)ˣ) : Loc a b w) ∈ Submodule.localBox R w) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → toLoc w s ∈ Submodule.localBoxUnits R w) ∧
      QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = (ℓ : ℚ) := by
  classical
  have hr : r.Prime := Fact.out
  have hqp : q.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder

  obtain ⟨vl, hvl_mem⟩ : ∃ vl : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∈ vl.asIdeal :=
    ⟨placeOver ℓ hℓ, natCast_mem_placeOver ℓ hℓ⟩
  have hqvl : (q : 𝓞 ℚ) ∉ vl.asIdeal := natCast_not_mem_of_ne hℓ hqp hℓq hvl_mem
  have hNvl : (N : 𝓞 ℚ) ∉ vl.asIdeal := fun hN => hℓN (dvd_of_natCast_mem hℓ hvl_mem hN)
  obtain ⟨φ, hφ, hφR⟩ := QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef hR vl hqvl hNvl

  obtain ⟨β₀, hβ₀⟩ := QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_nrd_eq_of_pos hq hdef (ℓ : ℚ)
    (by exact_mod_cast hℓ.pos)
  have hβ₀0 : QuaternionAlgebra.nrd β₀ ≠ 0 := by rw [hβ₀]; exact hℓ0
  set B₀ : (ℍ[ℚ, a, b])ˣ := unitOfNrd β₀ hβ₀0 with hB₀
  have hB₀n : QuaternionAlgebra.nrd (B₀ : ℍ[ℚ, a, b]) = (ℓ : ℚ) := hβ₀

  have hll : algebraMap ℚ (vl.adicCompletion ℚ) (ℓ : ℚ) * algebraMap ℚ (vl.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hℓ0, map_one]
  have hll' : algebraMap ℚ (vl.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) * algebraMap ℚ (vl.adicCompletion ℚ) (ℓ : ℚ) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hℓ0, map_one]
  set Dl : Matrix (Fin 2) (Fin 2) (vl.adicCompletion ℚ) := Matrix.diagonal ![1, algebraMap ℚ (vl.adicCompletion ℚ) (ℓ : ℚ)] with hDl
  set Dli : Matrix (Fin 2) (Fin 2) (vl.adicCompletion ℚ) := Matrix.diagonal ![1, algebraMap ℚ (vl.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)] with hDli
  have hDD : Dl * Dli = 1 := by
    rw [hDl, hDli, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i
    · show (1 : vl.adicCompletion ℚ) * 1 = 1; rw [mul_one]
    · show algebraMap ℚ (vl.adicCompletion ℚ) (ℓ : ℚ) * algebraMap ℚ (vl.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) = 1; exact hll
  have hDD' : Dli * Dl = 1 := by
    rw [hDl, hDli, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i
    · show (1 : vl.adicCompletion ℚ) * 1 = 1; rw [mul_one]
    · show algebraMap ℚ (vl.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) * algebraMap ℚ (vl.adicCompletion ℚ) (ℓ : ℚ) = 1; exact hll'
  have hxx : φ.symm Dl * φ.symm Dli = 1 := by
    apply φ.injective; rw [φ.map_mul, φ.apply_symm_apply, φ.apply_symm_apply, hDD, φ.map_one]
  have hxx' : φ.symm Dli * φ.symm Dl = 1 := by
    apply φ.injective; rw [φ.map_mul, φ.apply_symm_apply, φ.apply_symm_apply, hDD', φ.map_one]
  obtain ⟨x, hxv, -, hxw⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq_of_forall_ne R hRo.fg hRo.spanTop vl _ _ hxx hxx' 1
    (fun w _ => ⟨by rw [Units.val_one, map_one]; exact one_mem_localBox hRo w,
      by rw [inv_one, Units.val_one, map_one]; exact one_mem_localBox hRo w⟩)
  have hxw' : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ vl → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ) = 1 := by
    intro w hw
    have h1 := (hxw w hw).1
    rwa [Units.val_one, map_one] at h1
  have hxint : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] vl (x : 𝔸ℍ) ∈ Submodule.localBox R vl := by
    rw [hxv, hφR, φ.apply_symm_apply, hDl]
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      fin_cases i
      · exact one_mem _
      · show algebraMap ℚ (vl.adicCompletion ℚ) (ℓ : ℚ) ∈ _
        rw [map_natCast]; exact natCast_mem _ _
    · rw [Matrix.diagonal_apply_ne _ hij]; exact zero_mem _
  have hxnrd : ∀ w : HeightOneSpectrum (𝓞 ℚ), w = vl → ∀ ψ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
          ψ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])) →
      QuaternionAlgebra.nrd (ψ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ))) = algebraMap ℚ (w.adicCompletion ℚ) (ℓ : ℚ) := by
    intro w hw ψ hψ
    subst hw
    rw [← det_eq_nrd φ hφ ψ hψ, hxv, φ.apply_symm_apply, hDl, Matrix.det_diagonal, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]

  have hεv : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (if w = vl then (1 : ℚ) else (ℓ : ℚ))) = 1 := by
    intro w
    by_cases hw : w = vl
    · rw [if_pos hw, map_one, map_one]
    · rw [if_neg hw]
      exact v_algebraMap_natCast_eq_one (fun hmem => hw (eq_of_natCast_prime_mem hℓ hmem hvl_mem))
  obtain ⟨m, hmS, hm⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq hq hdef hR
      (fun w => algebraMap ℚ (w.adicCompletion ℚ) (if w = vl then (1 : ℚ) else (ℓ : ℚ))) hεv

  have hsplit : ∃ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ≠ 0 ∧ ¬ IsUnit z := by
    by_contra hcon
    push_neg at hcon
    exact natCast_not_mem_of_ne hr hqp hrq hv ((hdef.2.2 v).mp hcon)

  obtain ⟨β, g, u, hβ1, huS, hg, hyeq⟩ :=
    QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
      hdef.1 hdef.2.1 hRo v hsplit ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀)⁻¹ * x * m)
      (fun w _ => ynorm hℓ0 B₀ hB₀n vl x m hxnrd hxw' hm w)

  have key : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (B₀ * β) = x * m * u⁻¹ * g⁻¹ := by
    rw [diag_mul]
    calc Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β
        = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β * g * u) * u⁻¹ * g⁻¹ := by group
      _ = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀ * ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀)⁻¹ * x * m) * u⁻¹ * g⁻¹ := by
          rw [hyeq]
      _ = x * m * u⁻¹ * g⁻¹ := by group
  obtain ⟨h1, h2⟩ := assembly hRo v vl hvl_mem hℓ (B₀ * β) x m u g key hxint hxw' hmS huS hg
  refine ⟨B₀ * β, h1, h2, ?_⟩
  rw [Units.val_mul, nrd_mul, hβ1, mul_one, hB₀n]

end CerednikDrinfeld.CosetGraph.NormL
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld.CosetGraph P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld.CosetGraph.NormL"
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld.CosetGraph"
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld.CosetGraph P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld.CosetGraph.NormL"

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.CerednikDrinfeld QuaternionAlgebra in
theorem solution
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : ((r : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓN : ¬ ℓ ∣ N) :
    ∃ s : (ℍ[ℚ, a, b])ˣ,
      (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), w ≠ v →
        ((CosetGraph.toLoc w s : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox R w) ∧
      (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), w ≠ v →
        ((ℓ : ℕ) : NumberField.RingOfIntegers ℚ) ∉ w.asIdeal →
        CosetGraph.toLoc w s ∈ Submodule.localBoxUnits R w) ∧
      QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = (ℓ : ℚ) :=
  CerednikDrinfeld.CosetGraph.NormL.main hq hdef hR hrq v hv hℓq hℓN

end S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox (solution)
