-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/311dd08e-018b-56e5-940e-99a2df2d68b1

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_BaseChange
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_nrd_eq_of_pos
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_localBox_inf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes
p2m_attr_erase "simp" "LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "CosetGraph.Loc CosetGraph.toLoc"
namespace CosetGraph
p2m_export "CerednikDrinfeld.CosetGraph" "Loc toLoc awayUnits"
namespace WBar
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

def coord (w : HeightOneSpectrum (𝓞 ℚ)) :
    ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b] :=
  (QuaternionAlgebra.baseChangeRight (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    rfl (map_zero _) rfl).toRingEquiv

theorem coord_formula (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ) :
    coord w (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) := by
  show QuaternionAlgebra.baseChangeRight _ _ _ (z ⊗ₜ[ℚ] r) = _
  rw [QuaternionAlgebra.baseChangeRight_tmul]
  ext <;> simp [smul_eq_mul]

def locNrd (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : w.adicCompletion ℚ :=
  QuaternionAlgebra.nrd (coord w x)

theorem nrd_mul' {K : Type*} [CommRing K] {a' b' : K} (x y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem locNrd_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    locNrd w (x * y) = locNrd w x * locNrd w y := by
  unfold locNrd
  rw [(coord w).map_mul, nrd_mul']

theorem locNrd_one (w : HeightOneSpectrum (𝓞 ℚ)) : locNrd w (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 1 := by
  unfold locNrd
  have h1 : coord w (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 1 := map_one (coord w)
  rw [h1, QuaternionAlgebra.nrd_one]

theorem locNrd_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    locNrd w (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd z) := by
  unfold locNrd
  rw [coord_formula, one_smul, QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd]
  simp only [map_sub, map_add, map_mul, map_pow]

theorem locNrd_one_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (t : w.adicCompletion ℚ) :
    locNrd w ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t ^ 2 := by
  unfold locNrd
  rw [coord_formula, QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk]
  simp only [show (1 : ℍ[ℚ, a, b]).re = 1 from rfl, show (1 : ℍ[ℚ, a, b]).imI = 0 from rfl,
    show (1 : ℍ[ℚ, a, b]).imJ = 0 from rfl, show (1 : ℍ[ℚ, a, b]).imK = 0 from rfl, map_one, map_zero,
    smul_eq_mul, mul_one, mul_zero]
  ring

theorem ratSmul_eq (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) * x := by
  have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) = c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rw [e1, smul_mul_assoc, one_mul]

theorem locNrd_ratSmul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    locNrd w (c • x) = algebraMap ℚ (w.adicCompletion ℚ) c ^ 2 * locNrd w x := by
  rw [ratSmul_eq, locNrd_mul, locNrd_one_tmul]

theorem locNrd_conj (w : HeightOneSpectrum (𝓞 ℚ)) {g gi : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hg : gi * g = 1)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : locNrd w (gi * x * g) = locNrd w x := by
  rw [locNrd_mul, locNrd_mul, mul_comm (locNrd w gi), mul_assoc, ← locNrd_mul, hg, locNrd_one, mul_one]

section Div
variable {p : ℕ} [Fact p.Prime]

theorem mem_localBox_iff_locNrd (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox R v ↔ locNrd v x ∈ v.adicCompletionIntegers ℚ := by
  have hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y := (hdef.2.2 v).mpr hv
  obtain ⟨Λ₁, Λ₂, h₁, h₂, hRdef, -⟩ := hR
  have hbox : Submodule.localBox R v = Submodule.localBox Λ₁ v := by
    rw [hRdef, Submodule.localBox_inf Λ₁ Λ₂ h₁.isOrder.fg h₁.isOrder.spanTop h₂.isOrder.fg h₂.isOrder.spanTop,
      ← QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv h₁ h₂, inf_idem]
  rw [hbox]
  exact QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit h₁ v hdiv
    (coord v) (coord_formula v) x

end Div

section idele

open Classical in

def localData (v : HeightOneSpectrum (𝓞 ℚ)) (wl : (Loc a b v)ˣ) :
    ∀ v' : HeightOneSpectrum (𝓞 ℚ), (Loc a b v')ˣ :=
  fun v' => if h : v' = v then h ▸ wl else 1

theorem exists_idele (v : HeightOneSpectrum (𝓞 ℚ)) (wl : (Loc a b v)ˣ) :
    ∃ n : (𝔸ℍ)ˣ, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : 𝔸ℍ) = wl ∧
      ∀ v' ≠ v, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v' (n : 𝔸ℍ) = 1 := by
  classical
  obtain ⟨β, h1, h2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {v} (localData v wl)
  refine ⟨β, ?_, fun v' hv' => ?_⟩
  · rw [h1 v (Finset.mem_singleton_self v)]; simp [localData]
  · rw [h2 v' (by simpa using hv')]

end idele

def placeOfPrime (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  ⟨Ideal.span {(p : 𝓞 ℚ)}, (isMaximal_span_natCast_of_prime hp).isPrime, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero⟩

theorem natCast_mem_placeOfPrime (p : ℕ) (hp : p.Prime) : ((p : ℕ) : 𝓞 ℚ) ∈ (placeOfPrime p hp).asIdeal :=
  Ideal.subset_span (Set.mem_singleton _)

theorem conj_mem_localBox_iff_of_mem_localBoxUnits {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (w : HeightOneSpectrum (𝓞 ℚ)) {t : (Loc a b w)ˣ} (ht : t ∈ Submodule.localBoxUnits O w) (x : Loc a b w) :
    ((t⁻¹ : (Loc a b w)ˣ) : Loc a b w) * x * (t : Loc a b w) ∈ Submodule.localBox O w ↔ x ∈ Submodule.localBox O w := by
  obtain ⟨h1, h2⟩ := ht
  constructor
  · intro h
    have e : x = (t : Loc a b w) * (((t⁻¹ : (Loc a b w)ˣ) : Loc a b w) * x * (t : Loc a b w)) *
        ((t⁻¹ : (Loc a b w)ˣ) : Loc a b w) := by
      rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact localBox_mul_mem hO w (localBox_mul_mem hO w h1 h) h2
  · intro h
    exact localBox_mul_mem hO w (localBox_mul_mem hO w h2 h) h1

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (w : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ w ≤ Submodule.localBox Λ' w := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem localBoxUnits_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (w : HeightOneSpectrum (𝓞 ℚ))
    {t : (Loc a b w)ˣ} (ht : t ∈ Submodule.localBoxUnits Λ w) : t ∈ Submodule.localBoxUnits Λ' w :=
  ⟨localBox_mono h w ht.1, localBox_mono h w ht.2⟩

theorem main {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ wbar : (ℍ[ℚ, a, b])ˣ,
      QuaternionAlgebra.nrd (wbar : ℍ[ℚ, a, b]) = (q : ℚ) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        toLoc w wbar ∈ Submodule.localBoxUnits R w) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ∀ x : Loc a b w,
        ((((toLoc w wbar)⁻¹ : (Loc a b w)ˣ) : Loc a b w) * x * ((toLoc w wbar : (Loc a b w)ˣ) : Loc a b w) ∈
            Submodule.localBox R w ↔ x ∈ Submodule.localBox R w) ∧
        ((((toLoc w wbar)⁻¹ : (Loc a b w)ˣ) : Loc a b w) * x * ((toLoc w wbar : (Loc a b w)ˣ) : Loc a b w) ∈
            Submodule.localBox Λ w ↔ x ∈ Submodule.localBox Λ w)) := by
  classical
  have hr : r.Prime := Fact.out
  have hqp : q.Prime := Fact.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder

  set vq := placeOfPrime q hqp with hvq_def
  have hvq : ((q : ℕ) : 𝓞 ℚ) ∈ vq.asIdeal := natCast_mem_placeOfPrime q hqp
  have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := natCast_not_mem_of_ne hr hqp hrq hv
  have hvqv : vq ≠ v := fun h => hqv (h ▸ hvq)

  obtain ⟨β₀, hβ₀⟩ := QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_nrd_eq_of_pos hq hdef (q : ℚ)
    (by exact_mod_cast hqp.pos)
  have hβ₀0 : QuaternionAlgebra.nrd β₀ ≠ 0 := by rw [hβ₀]; exact hq0
  set B₀ : (ℍ[ℚ, a, b])ˣ := unitOfNrd β₀ hβ₀0 with hB₀

  set ε : ℚ → HeightOneSpectrum (𝓞 ℚ) → ℚ := fun _ w => if w = v ∨ ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal then 1 else q with hε
  have hεv : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (ε 0 w)) = 1 := by
    intro w
    by_cases hw : w = v ∨ ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    · simp only [hε, if_pos hw, map_one]
    · simp only [hε, if_neg hw]
      exact v_algebraMap_natCast_eq_one (fun hmem => hw (Or.inr hmem))
  obtain ⟨m, hmS, hm⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq hq hdef hR
      (fun w => algebraMap ℚ (w.adicCompletion ℚ) (ε 0 w)) hεv

  obtain ⟨c, hcv, hcw⟩ := exists_idele vq (toLoc vq B₀)

  have hsplit : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x := by
    by_contra hcon
    push_neg at hcon
    exact hqv ((hdef.2.2 v).mp hcon)

  set y : (𝔸ℍ)ˣ := (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀)⁻¹ * m * c with hy
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
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (m : 𝔸ℍ) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (c : 𝔸ℍ) := by
      rw [hy, Units.val_mul, Units.val_mul, ← diag_inv, Submodule.val_finiteIdeleDiagonal_apply, map_mul, map_mul]
    rw [hev, φ.map_mul, φ.map_mul, nrd_mul, nrd_mul, coord_evalAt_tmul_one φ hφ, hm w φ hφ, nrd_val_inv, val_unitOfNrd, hβ₀]
    by_cases hqw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    ·
      have hwq : w = vq := eq_of_natCast_prime_mem hqp hqw hvq
      subst hwq
      have hc : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (placeOfPrime q hqp) (c : 𝔸ℍ) =
          β₀ ⊗ₜ[ℚ] (1 : (placeOfPrime q hqp).adicCompletion ℚ) := by
        rw [hcv]; rfl
      rw [hc, hφ, one_smul, nrd_coords, hβ₀]
      simp only [hε, if_pos (Or.inr hqw), map_one, mul_one]
      rw [← map_mul, inv_mul_cancel₀ hq0, map_one]
    ·
      have hwvq : w ≠ vq := fun h => hqw (h ▸ hvq)
      rw [hcw w hwvq, map_one, QuaternionAlgebra.nrd_one, mul_one]
      have : ¬ (w = v ∨ ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) := fun h => h.elim hw hqw
      simp only [hε, if_neg this]
      rw [← map_mul, inv_mul_cancel₀ hq0, map_one]

  obtain ⟨β, g, u, hβ1, huS, hg, hyeq⟩ :=
    QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
      hdef.1 hdef.2.1 hRo v hsplit y hynorm

  have key : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (B₀ * β) = m * c * u⁻¹ * g⁻¹ := by
    have e1 : m * c = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β * g * u) := by
      rw [← hyeq, hy]; group
    rw [diag_mul]
    have e2 : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β =
        m * c * u⁻¹ * g⁻¹ := by
      rw [e1]; group
    exact e2
  have hunit : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      toLoc w (B₀ * β) ∈ Submodule.localBoxUnits R w := by
    intro w hw hqw
    have hwvq : w ≠ vq := fun h => hqw (h ▸ hvq)
    have hmw := ((QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      R hRo m).mp hmS) w
    have huw := ((QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      R hRo u).mp huS) w
    have hgw : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom g = 1 :=
      Units.ext (hg w hw)
    have hcw' : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom c = 1 :=
      Units.ext (hcw w hwvq)
    rw [← unitsMap_finiteAdeleEvalAt_diagonal, key, evU_mul, evU_mul, evU_mul, evU_inv, evU_inv, hgw, hcw', inv_one,
      mul_one, mul_one]
    exact (localUnits hRo w).mul_mem hmw ((localUnits hRo w).inv_mem huw)
  refine ⟨B₀ * β, ?_, hunit, ?_⟩
  ·
    rw [Units.val_mul, nrd_mul, hβ1, mul_one, hB₀, val_unitOfNrd, hβ₀]
  ·
    intro w hw x
    by_cases hqw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    ·
      have hwq : w = vq := eq_of_natCast_prime_mem hqp hqw hvq
      subst hwq
      have hdiv : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] (placeOfPrime q hqp).adicCompletion ℚ, z ≠ 0 → IsUnit z :=
        (hdef.2.2 _).mpr hqw
      set t := toLoc (placeOfPrime q hqp) (B₀ * β) with ht
      have hinv : ((t⁻¹ : (Loc a b (placeOfPrime q hqp))ˣ) : Loc a b (placeOfPrime q hqp)) * (t : Loc a b _) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      refine ⟨?_, ?_⟩
      · rw [mem_localBox_iff_locNrd hdef hR _ hqw, mem_localBox_iff_locNrd hdef hR _ hqw, locNrd_conj _ hinv]
      · rw [QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ _ hdiv
            (coord _) (coord_formula _),
          QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ _ hdiv
            (coord _) (coord_formula _)]
        show locNrd _ _ ∈ _ ↔ locNrd _ _ ∈ _
        rw [locNrd_conj _ hinv]
    ·
      have ht := hunit w hw hqw
      exact ⟨conj_mem_localBox_iff_of_mem_localBoxUnits hRo w ht x,
        conj_mem_localBox_iff_of_mem_localBoxUnits hΛo w (localBoxUnits_mono hRΛ w ht) x⟩

end CerednikDrinfeld.CosetGraph.WBar
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld.CosetGraph P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld.CosetGraph.WBar"
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld.CosetGraph"
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld.CosetGraph P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld.CosetGraph.WBar"

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes.CerednikDrinfeld QuaternionAlgebra in
theorem solution
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ wbar : (ℍ[ℚ, a, b])ˣ,
      QuaternionAlgebra.nrd (wbar : ℍ[ℚ, a, b]) = (q : ℚ) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        CosetGraph.toLoc w wbar ∈ Submodule.localBoxUnits R w) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ∀ x : CosetGraph.Loc a b w,
        ((((CosetGraph.toLoc w wbar)⁻¹ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) * x *
            ((CosetGraph.toLoc w wbar : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox R w ↔
          x ∈ Submodule.localBox R w) ∧
        ((((CosetGraph.toLoc w wbar)⁻¹ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) * x *
            ((CosetGraph.toLoc w wbar : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox Λ w ↔
          x ∈ Submodule.localBox Λ w)) :=
  CerednikDrinfeld.CosetGraph.WBar.main hq hdef hR Λ hΛ hRΛ hrq v hv

end S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_ramifiedPrime_forall_mem_localBoxUnits_and_normalizes (solution)
