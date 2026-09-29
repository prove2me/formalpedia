-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_nrd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fa8848c5-9a1c-5349-b215-3c33230d09bc

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "CosetGraph.awayUnits"
namespace CosetGraph
p2m_export "CerednikDrinfeld.CosetGraph" "Loc toLoc awayUnits"
namespace NormR
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

theorem main {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ γ : (ℍ[ℚ, a, b])ˣ, γ ∈ awayUnits R v ∧ QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) = (r : ℚ) := by
  classical
  have hr : r.Prime := Fact.out
  have hqp : q.Prime := Fact.out
  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder

  obtain ⟨β₀, hβ₀⟩ := QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_nrd_eq_of_pos hq hdef (r : ℚ)
    (by exact_mod_cast hr.pos)
  have hβ₀0 : QuaternionAlgebra.nrd β₀ ≠ 0 := by rw [hβ₀]; exact_mod_cast hr.ne_zero
  set B₀ : (ℍ[ℚ, a, b])ˣ := unitOfNrd β₀ hβ₀0 with hB₀

  have hεv : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (if w = v then (1 : ℚ) else (r : ℚ))) = 1 := by
    intro w
    by_cases hw : w = v
    · rw [if_pos hw, map_one, map_one]
    · rw [if_neg hw]
      exact v_algebraMap_natCast_eq_one (fun hmem => hw (eq_of_natCast_prime_mem hr hmem hv))
  obtain ⟨m, hmS, hm⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq hq hdef hR
      (fun w => algebraMap ℚ (w.adicCompletion ℚ) (if w = v then (1 : ℚ) else (r : ℚ))) hεv

  have hsplit : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x := by
    by_contra hcon
    push_neg at hcon
    exact natCast_not_mem_of_ne hr hqp hrq hv ((hdef.2.2 v).mp hcon)

  set y : (𝔸ℍ)ˣ := (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀)⁻¹ * m with hy
  have hynorm : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : 𝔸ℍ))) = 1 := by
    intro w hw φ hφ
    have hev : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : 𝔸ℍ) =
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (((B₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) *
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (m : 𝔸ℍ) := by
      rw [hy, Units.val_mul, ← diag_inv, Submodule.val_finiteIdeleDiagonal_apply, map_mul]
    rw [hev, φ.map_mul, nrd_mul, coord_evalAt_tmul_one φ hφ, hm w φ hφ, nrd_val_inv, val_unitOfNrd, hβ₀]
    show algebraMap ℚ (w.adicCompletion ℚ) (r : ℚ)⁻¹ * algebraMap ℚ (w.adicCompletion ℚ) (if w = v then (1 : ℚ) else (r : ℚ)) = 1
    rw [if_neg hw, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hr.ne_zero : (r : ℚ) ≠ 0), map_one]

  obtain ⟨β, g, u, hβ1, huS, hg, hyeq⟩ :=
    QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
      hdef.1 hdef.2.1 hRo v hsplit y hynorm

  refine ⟨B₀ * β, ?_, ?_⟩
  ·
    have key : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (B₀ * β) = m * u⁻¹ * g⁻¹ := by
      have e1 : m = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β * g * u) := by
        rw [← hyeq, hy, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [diag_mul, e1]
      group
    rw [mem_awayUnits_iff hRo]
    intro w hw
    have hmw := ((QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      R hRo m).mp hmS) w
    have huw := ((QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      R hRo u).mp huS) w
    have hgw : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom g = 1 :=
      Units.ext (hg w hw)
    rw [← unitsMap_finiteAdeleEvalAt_diagonal, key, evU_mul, evU_mul, evU_inv, evU_inv, hgw, inv_one, mul_one]
    exact (localUnits hRo w).mul_mem hmw ((localUnits hRo w).inv_mem huw)
  ·
    rw [Units.val_mul, nrd_mul, hβ1, mul_one, hB₀, val_unitOfNrd, hβ₀]

end CerednikDrinfeld.CosetGraph.NormR
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld.CosetGraph P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld.CosetGraph.NormR"
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld.CosetGraph"
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld.CosetGraph P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld.CosetGraph.NormR"

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.CerednikDrinfeld QuaternionAlgebra in
theorem solution
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (hv : ((r : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal) :
    ∃ γ : (ℍ[ℚ, a, b])ˣ, γ ∈ CosetGraph.awayUnits R v ∧ QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) = (r : ℚ) :=
  CerednikDrinfeld.CosetGraph.NormR.main hq hdef hR hrq v hv

end S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq (solution)
