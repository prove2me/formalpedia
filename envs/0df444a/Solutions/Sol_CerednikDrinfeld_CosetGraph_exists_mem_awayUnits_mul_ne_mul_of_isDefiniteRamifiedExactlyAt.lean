-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7ef1240f-11eb-5d43-a0c3-fb0342583433

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
import Theorems.Thm_Submodule_exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace NoncommPair

section Places

abbrev pgen (w : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator w

theorem pgen_prime (w : HeightOneSpectrum (𝓞 ℚ)) : (pgen w).Prime :=
  Rat.HeightOneSpectrum.prime_natGenerator w

def place (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem primesEquiv_place (p : ℕ) (hp : p.Prime) :
    Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) (place p hp) = ⟨p, hp⟩ := by
  simp [place]

theorem pgen_place (p : ℕ) (hp : p.Prime) : pgen (place p hp) = p :=
  congrArg Subtype.val (primesEquiv_place p hp)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ pgen w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem pgen_eq_of_prime_mem {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : pgen v = p :=
  (Nat.prime_dvd_prime_iff_eq (pgen_prime v) hp).1 ((natCast_mem_asIdeal_iff v p).1 hv)

theorem pgen_injective : Function.Injective pgen := by
  intro w w' h
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) c) = w.valuation ℚ c := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w c

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ¬ pgen w ∣ n) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 ?_
  rwa [natCast_mem_asIdeal_iff]

theorem mem_integers_iff (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) :
    x ∈ w.adicCompletionIntegers ℚ ↔ Valued.v x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem zpow_natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ¬ pgen w ∣ n) (i : ℤ) :
    algebraMap ℚ (w.adicCompletion ℚ) ((n : ℚ) ^ i) ∈ w.adicCompletionIntegers ℚ := by
  rw [mem_integers_iff, valued_algebraMap, map_zpow₀, valuation_natCast_eq_one_of_not_dvd w hn, one_zpow]

theorem cst_zpow' (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) (n : ℤ) :
    algebraMap ℚ (w.adicCompletion ℚ) (x ^ n) = algebraMap ℚ (w.adicCompletion ℚ) x ^ n :=
  map_zpow₀ _ x n

theorem intCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (t : ℤ) :
    (t : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := intCast_mem _ t

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) :
    (t : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := natCast_mem _ t

end Places

section Coord

variable {a b : ℚ}

abbrev cst (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) q

theorem cst_zpow (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) (n : ℤ) : cst w (x ^ n) = cst w x ^ n :=
  map_zpow₀ _ x n

theorem cst_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℚ) : cst w (x * y) = cst w x * cst w y :=
  map_mul _ x y

theorem cst_one (w : HeightOneSpectrum (𝓞 ℚ)) : cst w (1 : ℚ) = 1 := map_one _

theorem cst_sub (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℚ) : cst w (x - y) = cst w x - cst w y :=
  map_sub _ x y

def hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : ℍ[w.adicCompletion ℚ, cst w a, cst w b] :=
  ⟨cst w x.re, cst w x.imI, cst w x.imJ, cst w x.imK⟩

theorem hatQ_star (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : hatQ w (star x) = star (hatQ w x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [hatQ, map_neg]

theorem hatQ_one (w : HeightOneSpectrum (𝓞 ℚ)) : hatQ w (1 : ℍ[ℚ, a, b]) = 1 := by
  ext <;> simp [hatQ]

theorem nrd_hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (hatQ w x) = cst w (QuaternionAlgebra.nrd x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [hatQ, QuaternionAlgebra.nrd, map_add, map_sub, map_mul, map_pow]

theorem nrd_mul' {K : Type*} [CommRing K] {c₁ c₃ : K} (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_smul' {K : Type*} [CommRing K] {c₁ c₃ : K} (c : K) (x : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (c • x) = c ^ 2 * QuaternionAlgebra.nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk, smul_eq_mul]
  ring

theorem nrd_nonneg (ha : a < 0) (hb : b < 0) (x : ℍ[ℚ, a, b]) : 0 ≤ QuaternionAlgebra.nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  rw [QuaternionAlgebra.nrd_mk]
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃, mul_pos_of_neg_of_neg ha hb]

def IsCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) : Prop :=
  ∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
    φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])

variable {w : HeightOneSpectrum (𝓞 ℚ)}
  {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}

theorem IsCoord.tmul (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ) :
    φ (z ⊗ₜ[ℚ] r) = r • hatQ w z := by
  rw [hφ]; rfl

theorem IsCoord.tmul_one (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) :
    φ (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = hatQ w z := by
  rw [hφ.tmul, one_smul]

theorem IsCoord.one_tmul (hφ : IsCoord a b w φ) (c : w.adicCompletion ℚ) :
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = (c : ℍ[w.adicCompletion ℚ, cst w a, cst w b]) := by
  rw [hφ.tmul, hatQ_one]
  ext <;> simp

theorem nrd_φ_tmul_one (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (φ (z ⊗ₜ[ℚ] 1)) = cst w (QuaternionAlgebra.nrd z) := by
  rw [hφ.tmul_one, nrd_hatQ]

end Coord

section Boxes

variable {a b : ℚ} {O : Submodule ℤ ℍ[ℚ, a, b]}

theorem tmul_mem_localBox {z : ℍ[ℚ, a, b]} (hz : z ∈ O) (w : HeightOneSpectrum (𝓞 ℚ))
    {c : w.adicCompletion ℚ} (hc : c ∈ w.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox O w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem mul_mem_localBox (hO : QuaternionAlgebra.IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox O w) (hy : y ∈ Submodule.localBox O w) :
    x * y ∈ Submodule.localBox O w := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z', hz', c', hc', rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z, hz, c, hc, rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox (hO.mul_mem hz hz') w (Subring.mul_mem _ hc hc')
    | zero => rw [zero_mul]; exact AddSubgroup.zero_mem _
    | add u u' _ _ hu hu' => rw [add_mul]; exact AddSubgroup.add_mem _ hu hu'
    | neg u _ hu => rw [show -u * z' ⊗ₜ[ℚ] c' = -(u * z' ⊗ₜ[ℚ] c') from neg_mul u _]; exact AddSubgroup.neg_mem _ hu
  | zero => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | add u u' _ _ hu hu' => rw [mul_add]; exact AddSubgroup.add_mem _ hu hu'
  | neg u _ hu => rw [show x * -u = -(x * u) from mul_neg x u]; exact AddSubgroup.neg_mem _ hu

theorem localBox_mono {O' : Submodule ℤ ℍ[ℚ, a, b]} (h : O' ≤ O) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox O' w ≤ Submodule.localBox O w := by
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

open QuaternionAlgebra CerednikDrinfeld

def boxUnits (hO : IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (CosetGraph.Loc a b w)ˣ where
  carrier := Submodule.localBoxUnits O w
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one, Algebra.TensorProduct.one_def]
      exact tmul_mem_localBox hO.one_mem w (one_mem _)
    · rw [inv_one, Units.val_one, Algebra.TensorProduct.one_def]
      exact tmul_mem_localBox hO.one_mem w (one_mem _)
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact mul_mem_localBox hO w hx.1 hy.1
    · rw [mul_inv_rev, Units.val_mul]; exact mul_mem_localBox hO w hy.2 hx.2
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem closure_localBoxUnits (hO : IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup.closure (Submodule.localBoxUnits O w) = boxUnits hO w :=
  (boxUnits hO w).closure_eq

theorem mem_awayUnits_iff (hO : IsOrder O) (v : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) :
    γ ∈ CosetGraph.awayUnits O v ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      (γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox O w ∧
      ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox O w := by
  simp only [CosetGraph.awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap, closure_localBoxUnits hO]
  refine forall_congr' fun w => forall_congr' fun hw => ?_
  rw [show (CosetGraph.toLoc w γ ∈ boxUnits hO w) ↔ _ from Iff.rfl]
  change (_ ∈ Submodule.localBoxUnits O w) ↔ _
  rw [Submodule.mem_localBoxUnits_iff, ← map_inv]
  rfl

end Boxes

section LocalGlobal

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

def extendScalar (w : HeightOneSpectrum (𝓞 ℚ)) (f : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ) :
    ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ →ₗ[ℚ] w.adicCompletion ℚ :=
  (TensorProduct.lid ℚ (w.adicCompletion ℚ)).toLinearMap ∘ₗ f.rTensor (w.adicCompletion ℚ)

theorem extendScalar_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (f : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ) (x : ℍ[ℚ, a, b])
    (y : w.adicCompletion ℚ) : extendScalar w f (x ⊗ₜ[ℚ] y) = f x • y := by
  simp [extendScalar]

theorem extendScalar_coord_mem_integers {R : Submodule ℤ ℍ[ℚ, a, b]}
    (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (hBR : Submodule.span ℤ (Set.range B) = R)
    (w : HeightOneSpectrum (𝓞 ℚ)) (i : Fin 4) {t : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ}
    (ht : t ∈ Submodule.localBox R w) :
    extendScalar w (B.coord i) t ∈ w.adicCompletionIntegers ℚ := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    rw [extendScalar_tmul, Module.Basis.coord_apply]
    rw [← hBR] at hz
    obtain ⟨m, hm⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ B z).1 hz i
    rw [← hm, algebraMap_smul]
    exact zsmul_mem hc m
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end LocalGlobal

section AuxOrder

variable {a b : ℚ}

open QuaternionAlgebra

def auxOrder (R : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) : Submodule ℤ ℍ[ℚ, a, b] :=
  Submodule.span ℤ {(1 : ℍ[ℚ, a, b])} ⊔ R.map ((ℓ : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b]))

theorem mem_auxOrder_iff (R : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ auxOrder R ℓ ↔ ∃ (k : ℤ) (ρ : ℍ[ℚ, a, b]), ρ ∈ R ∧ x = k • (1 : ℍ[ℚ, a, b]) + (ℓ : ℤ) • ρ := by
  rw [auxOrder, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨ρ, hρ, rfl⟩ := Submodule.mem_map.1 hz
    exact ⟨k, ρ, hρ, by simp⟩
  · rintro ⟨k, ρ, hρ, rfl⟩
    exact ⟨k • 1, Submodule.mem_span_singleton.2 ⟨k, rfl⟩, (ℓ : ℤ) • ρ,
      Submodule.mem_map.2 ⟨ρ, hρ, by simp⟩, rfl⟩

theorem smul_mem_auxOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (ℓ : ℕ) {ρ : ℍ[ℚ, a, b]} (hρ : ρ ∈ R) :
    (ℓ : ℤ) • ρ ∈ auxOrder R ℓ :=
  (mem_auxOrder_iff R ℓ _).2 ⟨0, ρ, hρ, by simp⟩

theorem one_mem_auxOrder (R : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) : (1 : ℍ[ℚ, a, b]) ∈ auxOrder R ℓ :=
  (mem_auxOrder_iff R ℓ _).2 ⟨1, 0, R.zero_mem, by simp⟩

theorem auxOrder_le {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (ℓ : ℕ) : auxOrder R ℓ ≤ R := by
  intro x hx
  obtain ⟨k, ρ, hρ, rfl⟩ := (mem_auxOrder_iff R ℓ x).1 hx
  exact R.add_mem (R.smul_mem k hR.one_mem) (R.smul_mem _ hρ)

theorem isOrder_auxOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    IsOrder (auxOrder R ℓ) where
  one_mem := one_mem_auxOrder R ℓ
  mul_mem := by
    intro x y hx hy
    obtain ⟨k, ρ, hρ, rfl⟩ := (mem_auxOrder_iff R ℓ x).1 hx
    have hyR : y ∈ R := auxOrder_le hR ℓ hy
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
    exact (auxOrder R ℓ).add_mem ((auxOrder R ℓ).smul_mem k hy) (smul_mem_auxOrder ℓ (hR.mul_mem hρ hyR))
  spanTop := by
    refine top_unique ?_
    rw [← hR.spanTop]
    refine Submodule.span_le.mpr fun ρ hρ => ?_
    have e : ρ = ((ℓ : ℚ)⁻¹) • (((ℓ : ℤ) • ρ : ℍ[ℚ, a, b])) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hℓ), one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (smul_mem_auxOrder ℓ hρ))
  fg := Submodule.FG.sup (Submodule.fg_span_singleton _) (Submodule.FG.map _ hR.fg)

theorem exists_eq_of_mem_localBox_auxOrder (R : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) (w : HeightOneSpectrum (𝓞 ℚ))
    {X : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hX : X ∈ Submodule.localBox (auxOrder R ℓ) w) :
    ∃ c ∈ w.adicCompletionIntegers ℚ, ∃ z ∈ Submodule.localBox R w,
      X = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c + (ℓ : ℚ) • z := by
  induction hX using AddSubgroup.closure_induction with
  | mem X' hX' =>
    obtain ⟨o, ho, d, hd, rfl⟩ := hX'
    obtain ⟨k, ρ, hρ, rfl⟩ := (mem_auxOrder_iff R ℓ o).1 ho
    refine ⟨k • d, zsmul_mem hd k, ρ ⊗ₜ[ℚ] d, tmul_mem_localBox hρ w hd, ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul ℚ (ℓ : ℤ) ρ,
      Int.cast_natCast, TensorProduct.smul_tmul']
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add u u' _ _ hu hu' =>
    obtain ⟨c, hc, z, hz, rfl⟩ := hu
    obtain ⟨c', hc', z', hz', rfl⟩ := hu'
    refine ⟨c + c', add_mem hc hc', z + z', add_mem hz hz', ?_⟩
    rw [TensorProduct.tmul_add, smul_add]; abel
  | neg u _ hu =>
    obtain ⟨c, hc, z, hz, rfl⟩ := hu
    refine ⟨-c, neg_mem hc, -z, neg_mem hz, ?_⟩
    rw [TensorProduct.tmul_neg, smul_neg, neg_add]

end AuxOrder

section Main

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld Classical

abbrev evU (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ →* (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom

theorem coe_evU (w : HeightOneSpectrum (𝓞 ℚ)) (y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((evU a b w y : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  rfl

theorem evalAt_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]
  rfl

theorem coe_evU_diagonal (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b])ˣ) :
    ((evU a b w (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] x) : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = (x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [coe_evU, Submodule.val_finiteIdeleDiagonal_apply, evalAt_tmul_one]

theorem valuation_eq_one_of_lt (w : HeightOneSpectrum (𝓞 ℚ)) {x : ℚ} (hx : x ≠ 0)
    (hnum : x.num.natAbs < pgen w) (hden : x.den < pgen w) : w.valuation ℚ x = 1 := by
  have h1 : w.valuation ℚ ((x.num.natAbs : ℕ) : ℚ) = 1 :=
    valuation_natCast_eq_one_of_not_dvd w (fun h => by
      have := Nat.le_of_dvd (Int.natAbs_pos.2 (Rat.num_ne_zero.2 hx)) h; omega)
  have h2 : w.valuation ℚ ((x.den : ℕ) : ℚ) = 1 :=
    valuation_natCast_eq_one_of_not_dvd w (fun h => by
      have := Nat.le_of_dvd x.den_pos h; omega)
  have hnumv : w.valuation ℚ ((x.num : ℤ) : ℚ) = 1 := by
    rcases Int.natAbs_eq x.num with h | h
    · rw [h, Int.cast_natCast]; exact h1
    · rw [h, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact h1
  rw [← Rat.num_div_den x, map_div₀, hnumv, h2, div_one]

theorem eq_one_of_mul_eq_one_of_le {x y : WithZero (Multiplicative ℤ)} (hx : x ≤ 1) (hy : y ≤ 1) (h : x * y = 1) :
    x = 1 := by
  refine le_antisymm hx ?_
  calc (1 : WithZero (Multiplicative ℤ)) = x * y := h.symm
    _ ≤ x * 1 := mul_le_mul_right hy x
    _ = x := mul_one x

def locK (w : HeightOneSpectrum (𝓞 ℚ)) (s : ℍ[ℚ, a, b]) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
  (s * s) ⊗ₜ[ℚ] (cst w (QuaternionAlgebra.nrd s))⁻¹

def locK' (w : HeightOneSpectrum (𝓞 ℚ)) (s : ℍ[ℚ, a, b]) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
  (star s * star s) ⊗ₜ[ℚ] (cst w (QuaternionAlgebra.nrd s))⁻¹

theorem coe_eq_smul_one (x : ℚ) : ((x : ℚ) : ℍ[ℚ, a, b]) = x • (1 : ℍ[ℚ, a, b]) := by
  ext <;> simp

theorem mul_star_mul_star (s : ℍ[ℚ, a, b]) :
    s * s * (star s * star s) = (QuaternionAlgebra.nrd s * QuaternionAlgebra.nrd s) • (1 : ℍ[ℚ, a, b]) := by
  rw [mul_assoc, ← mul_assoc s (star s), QuaternionAlgebra.mul_star_eq_coe_nrd, QuaternionAlgebra.coe_mul_eq_smul,
    mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd, coe_eq_smul_one, smul_smul]

theorem star_mul_star_mul (s : ℍ[ℚ, a, b]) :
    star s * star s * (s * s) = (QuaternionAlgebra.nrd s * QuaternionAlgebra.nrd s) • (1 : ℍ[ℚ, a, b]) := by
  rw [mul_assoc, ← mul_assoc (star s) s, QuaternionAlgebra.star_mul_eq_coe_nrd, QuaternionAlgebra.coe_mul_eq_smul,
    mul_smul_comm, QuaternionAlgebra.star_mul_eq_coe_nrd, coe_eq_smul_one, smul_smul]

theorem smul_one_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) (c : w.adicCompletion ℚ) :
    (x • (1 : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] c = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (cst w x * c) := by
  rw [TensorProduct.smul_tmul, Algebra.smul_def]

theorem locK_mul_locK' (w : HeightOneSpectrum (𝓞 ℚ)) {s : ℍ[ℚ, a, b]} (hs : QuaternionAlgebra.nrd s ≠ 0) :
    locK w s * locK' w s = 1 := by
  have hc : cst w (QuaternionAlgebra.nrd s) ≠ 0 := (map_ne_zero _).2 hs
  rw [locK, locK', Algebra.TensorProduct.tmul_mul_tmul, mul_star_mul_star, smul_one_tmul, cst_mul,
    Algebra.TensorProduct.one_def]
  congr 1
  field_simp

theorem locK'_mul_locK (w : HeightOneSpectrum (𝓞 ℚ)) {s : ℍ[ℚ, a, b]} (hs : QuaternionAlgebra.nrd s ≠ 0) :
    locK' w s * locK w s = 1 := by
  have hc : cst w (QuaternionAlgebra.nrd s) ≠ 0 := (map_ne_zero _).2 hs
  rw [locK, locK', Algebra.TensorProduct.tmul_mul_tmul, star_mul_star_mul, smul_one_tmul, cst_mul,
    Algebra.TensorProduct.one_def]
  congr 1
  field_simp

def locKU (w : HeightOneSpectrum (𝓞 ℚ)) (s : ℍ[ℚ, a, b]) (hs : QuaternionAlgebra.nrd s ≠ 0) :
    (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  ⟨locK w s, locK' w s, locK_mul_locK' w hs, locK'_mul_locK w hs⟩

theorem inv_cst_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) {x : ℚ} (hx : w.valuation ℚ x = 1) :
    (cst w x)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [mem_integers_iff, map_inv₀, valued_algebraMap, hx, inv_one]

theorem locK_mem {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ)) {s : ℍ[ℚ, a, b]}
    (hs : s ∈ O) (hv : w.valuation ℚ (QuaternionAlgebra.nrd s) = 1) : locK w s ∈ Submodule.localBox O w :=
  tmul_mem_localBox (hO.mul_mem hs hs) w (inv_cst_mem_integers w hv)

theorem locK'_mem {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ)) {s : ℍ[ℚ, a, b]}
    (hs' : star s ∈ O) (hv : w.valuation ℚ (QuaternionAlgebra.nrd s) = 1) : locK' w s ∈ Submodule.localBox O w :=
  tmul_mem_localBox (hO.mul_mem hs' hs') w (inv_cst_mem_integers w hv)

theorem nrd_locK {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) {s : ℍ[ℚ, a, b]} (hs : QuaternionAlgebra.nrd s ≠ 0) :
    QuaternionAlgebra.nrd (φ (locK w s)) = 1 := by
  have hc : cst w (QuaternionAlgebra.nrd s) ≠ 0 := (map_ne_zero _).2 hs
  rw [locK, hφ.tmul, nrd_smul', nrd_hatQ, nrd_mul', cst_mul]
  field_simp

theorem mem_localBox_iff_of_mem_boxUnits {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ))
    {g : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hg : g ∈ boxUnits hO w) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    x ∈ Submodule.localBox O w ↔ ∃ y ∈ Submodule.localBox O w,
      x = (g : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * y * ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
  constructor
  · intro hx
    refine ⟨((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * x * g,
      mul_mem_localBox hO w (mul_mem_localBox hO w hg.2 hx) hg.1, ?_⟩
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem_localBox hO w (mul_mem_localBox hO w hg.1 hy) hg.2

theorem exists_awayUnit_congr (ha : a < 0) (hb : b < 0) {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hsplit : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x)
    (wl : HeightOneSpectrum (𝓞 ℚ)) (hwl : wl ≠ v) (hℓ0 : pgen wl ≠ 0)
    {s : ℍ[ℚ, a, b]} (hs : s ∈ R) (hs' : star s ∈ R) (hns : wl.valuation ℚ (QuaternionAlgebra.nrd s) = 1) :
    ∃ β : (ℍ[ℚ, a, b])ˣ, β ∈ CosetGraph.awayUnits R v ∧
      ∃ c ∈ wl.adicCompletionIntegers ℚ, ∃ c' ∈ wl.adicCompletionIntegers ℚ,
      ∃ z ∈ Submodule.localBox R wl, ∃ z' ∈ Submodule.localBox R wl,
        (β : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : wl.adicCompletion ℚ) =
          locK wl s * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c + ((pgen wl : ℕ) : ℚ) • z) ∧
        ((β⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : wl.adicCompletion ℚ) =
          ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c' + ((pgen wl : ℕ) : ℚ) • z') * locK' wl s := by
  have hns0 : QuaternionAlgebra.nrd s ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hns; exact zero_ne_one hns

  set KU : (ℍ[ℚ, a, b] ⊗[ℚ] wl.adicCompletion ℚ)ˣ := locKU wl s hns0 with hKU
  have hKUmem : KU ∈ boxUnits hRo wl := ⟨locK_mem hRo wl hs hns, locK'_mem hRo wl hs' hns⟩
  set gfam : (w : HeightOneSpectrum (𝓞 ℚ)) → (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
    Function.update (fun w => 1) wl KU with hgfam
  have hgfam_wl : gfam wl = KU := by rw [hgfam, Function.update_self]
  have hgfam_ne : ∀ w, w ≠ wl → gfam w = 1 := fun w hw => by rw [hgfam, Function.update_of_ne hw]
  have hgmem : ∀ w, gfam w ∈ boxUnits hRo w := by
    intro w
    by_cases hw : w = wl
    · subst hw; rw [hgfam_wl]; exact hKUmem
    · rw [hgfam_ne w hw]; exact (boxUnits hRo w).one_mem

  obtain ⟨y, hy, hy', -⟩ := Submodule.exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq R R
    hRo.fg hRo.spanTop hRo.fg hRo.spanTop gfam (Filter.Eventually.of_forall fun w => hgmem w)
    (fun w x => mem_localBox_iff_of_mem_boxUnits hRo w (hgmem w) x)
  have hyU : ∀ w, evU a b w y = gfam w := fun w => Units.ext (by rw [coe_evU]; exact hy w)

  set O : Submodule ℤ ℍ[ℚ, a, b] := auxOrder R (pgen wl) with hOdef
  have hO : IsOrder O := isOrder_auxOrder hRo hℓ0
  have hOR : O ≤ R := auxOrder_le hRo (pgen wl)
  have hynorm : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ →
        QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
          (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) = 1 := by
    intro w hw φ hφ
    rw [hy w]
    by_cases hwl' : w = wl
    · subst hwl'
      rw [hgfam_wl]
      exact nrd_locK hφ hns0
    · rw [hgfam_ne w hwl', Units.val_one, map_one, QuaternionAlgebra.nrd_one]
  obtain ⟨β, g, u, hu, hg, hyeq⟩ :=
    QuaternionAlgebra.IsOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one ha hb hO v hsplit y hynorm

  set Dg := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] with hD
  have hDβ : Dg β = y * u⁻¹ * g⁻¹ := by
    rw [hyeq]; group
  have hev : ∀ w, w ≠ v → evU a b w (Dg β) = gfam w * (evU a b w u)⁻¹ := by
    intro w hw
    have hg1 : evU a b w g = 1 := Units.ext (by rw [coe_evU, Units.val_one]; exact hg w hw)
    rw [hDβ, map_mul, map_mul, map_inv, map_inv, hg1, inv_one, mul_one, hyU]
  have huloc := (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
    O hO u).1 hu
  have huR : ∀ w, evU a b w u ∈ boxUnits hRo w := by
    intro w
    have h := huloc w
    rw [Submodule.mem_localBoxUnits_iff] at h
    exact ⟨localBox_mono hOR w h.1, localBox_mono hOR w h.2⟩
  have hβmem : ∀ w, w ≠ v → evU a b w (Dg β) ∈ boxUnits hRo w := by
    intro w hw
    rw [hev w hw]
    exact (boxUnits hRo w).mul_mem (hgmem w) ((boxUnits hRo w).inv_mem (huR w))
  refine ⟨β, ?_, ?_⟩
  · rw [mem_awayUnits_iff hRo]
    intro w hw
    have h := hβmem w hw
    refine ⟨?_, ?_⟩
    · rw [← coe_evU_diagonal w β]; exact h.1
    · rw [← coe_evU_diagonal w β⁻¹, ← hD, map_inv]; exact h.2

  have hu1 := (huloc wl)
  rw [Submodule.mem_localBoxUnits_iff] at hu1
  obtain ⟨c, hc, z, hz, hcz⟩ := exists_eq_of_mem_localBox_auxOrder R (pgen wl) wl hu1.2
  obtain ⟨c', hc', z', hz', hcz'⟩ := exists_eq_of_mem_localBox_auxOrder R (pgen wl) wl hu1.1
  refine ⟨c, hc, c', hc', z, hz, z', hz', ?_, ?_⟩
  · rw [← coe_evU_diagonal wl β, ← hD, hev wl hwl, Units.val_mul, hgfam_wl, hcz]
    rfl
  · rw [← coe_evU_diagonal wl β⁻¹, ← hD, map_inv, map_inv, hev wl hwl, mul_inv_rev, inv_inv, Units.val_mul, hgfam_wl,
      hcz']
    rfl

theorem valuation_coord_lt_one {R : Submodule ℤ ℍ[ℚ, a, b]}
    (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (hBR : Submodule.span ℤ (Set.range B) = R)
    (wl : HeightOneSpectrum (𝓞 ℚ)) {x : ℍ[ℚ, a, b]} {d : wl.adicCompletion ℚ}
    {m : ℍ[ℚ, a, b] ⊗[ℚ] wl.adicCompletion ℚ} (hm : m ∈ Submodule.localBox R wl)
    (h : x ⊗ₜ[ℚ] d = ((pgen wl : ℕ) : ℚ) • m) (t : Fin 4) :
    Valued.v (cst wl (B.coord t x) * d) < 1 := by
  have h1 := congrArg (extendScalar wl (B.coord t)) h
  rw [extendScalar_tmul, map_smul, Algebra.smul_def, Algebra.smul_def] at h1
  rw [h1, map_mul, valued_algebraMap]
  have hint : Valued.v (extendScalar wl (B.coord t) m) ≤ 1 :=
    (mem_integers_iff wl _).1 (extendScalar_coord_mem_integers B hBR wl t hm)
  have hℓ : wl.valuation ℚ ((pgen wl : ℕ) : ℚ) < 1 := by
    rw [show ((pgen wl : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (pgen wl : ℕ) from (map_natCast _ _).symm,
      HeightOneSpectrum.valuation_lt_one_iff_mem, natCast_mem_asIdeal_iff]
  calc wl.valuation ℚ ((pgen wl : ℕ) : ℚ) * Valued.v (extendScalar wl (B.coord t) m)
      ≤ wl.valuation ℚ ((pgen wl : ℕ) : ℚ) * 1 := mul_le_mul_right hint _
    _ < 1 := by rw [mul_one]; exact hℓ

def ModL (R : Submodule ℤ ℍ[ℚ, a, b]) (w : HeightOneSpectrum (𝓞 ℚ))
    (x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : Prop :=
  ∃ m ∈ Submodule.localBox R w, x - y = ((pgen w : ℕ) : ℚ) • m

theorem ModL.symm {R : Submodule ℤ ℍ[ℚ, a, b]} {w : HeightOneSpectrum (𝓞 ℚ)}
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (h : ModL R w x y) : ModL R w y x := by
  obtain ⟨m, hm, e⟩ := h
  refine ⟨-m, neg_mem hm, ?_⟩
  rw [smul_neg, ← e, neg_sub]

theorem ModL.trans {R : Submodule ℤ ℍ[ℚ, a, b]} {w : HeightOneSpectrum (𝓞 ℚ)}
    {x y z : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (h : ModL R w x y) (h' : ModL R w y z) : ModL R w x z := by
  obtain ⟨m, hm, e⟩ := h
  obtain ⟨m', hm', e'⟩ := h'
  refine ⟨m + m', add_mem hm hm', ?_⟩
  rw [smul_add, ← e, ← e', sub_add_sub_cancel]

theorem ModL.mul {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) {w : HeightOneSpectrum (𝓞 ℚ)}
    {x x' y y' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (h : ModL R w x x') (h' : ModL R w y y')
    (hx' : x' ∈ Submodule.localBox R w) (hy : y ∈ Submodule.localBox R w) : ModL R w (x * y) (x' * y') := by
  obtain ⟨m, hm, e⟩ := h
  obtain ⟨m', hm', e'⟩ := h'
  refine ⟨m * y + x' * m', add_mem (mul_mem_localBox hRo w hm hy) (mul_mem_localBox hRo w hx' hm'), ?_⟩
  have : x * y - x' * y' = (x - x') * y + x' * (y - y') := by
    rw [sub_mul, mul_sub]; abel
  rw [this, e, e', smul_mul_assoc, mul_smul_comm, smul_add]

theorem modL_of_eq_mul_add {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) {w : HeightOneSpectrum (𝓞 ℚ)}
    {x K z : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} {c : w.adicCompletion ℚ}
    (hK : K ∈ Submodule.localBox R w) (hz : z ∈ Submodule.localBox R w)
    (h : x = K * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c + ((pgen w : ℕ) : ℚ) • z)) :
    ModL R w x (K * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)) := by
  refine ⟨K * z, mul_mem_localBox hRo w hK hz, ?_⟩
  rw [h, mul_add, add_sub_cancel_left, mul_smul_comm]

theorem modL_of_eq_add_mul {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) {w : HeightOneSpectrum (𝓞 ℚ)}
    {x K z : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} {c : w.adicCompletion ℚ}
    (hK : K ∈ Submodule.localBox R w) (hz : z ∈ Submodule.localBox R w)
    (h : x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c + ((pgen w : ℕ) : ℚ) • z) * K) :
    ModL R w x (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * K) := by
  refine ⟨z * K, mul_mem_localBox hRo w hz hK, ?_⟩
  rw [h, add_mul, add_sub_cancel_left, smul_mul_assoc]

theorem v_eq_one_of_v_one_sub_mul_lt {w : HeightOneSpectrum (𝓞 ℚ)} {c c' : w.adicCompletion ℚ}
    (hc : Valued.v c ≤ 1) (hc' : Valued.v c' ≤ 1) (h : Valued.v (1 - c * c') < 1) : Valued.v c = 1 := by
  by_contra hne
  have hlt : Valued.v c < 1 := lt_of_le_of_ne hc hne
  have hcc : Valued.v (c * c') < 1 := by
    rw [map_mul]
    calc Valued.v c * Valued.v c' ≤ Valued.v c * 1 := mul_le_mul_right hc' _
      _ < 1 := by rwa [mul_one]
  have h1 := Valuation.map_add_lt Valued.v h hcc
  rw [sub_add_cancel, map_one] at h1
  exact lt_irrefl _ h1

def qi : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩
def qj : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩
def qk : ℍ[ℚ, a, b] := ⟨0, 0, 0, 1⟩

theorem qk_ne_zero : (qk : ℍ[ℚ, a, b]) ≠ 0 := by
  intro h
  have := congrArg QuaternionAlgebra.imK h
  simp [qk] at this

theorem sq_comm_sq (D : ℚ) :
    (1 + D • qi) * (1 + D • qi) * ((1 + D • qj) * (1 + D • qj)) -
      (1 + D • qj) * (1 + D • qj) * ((1 + D • qi) * (1 + D • qi)) = (8 * D ^ 2) • (qk : ℍ[ℚ, a, b]) := by
  ext <;> simp [qi, qj, qk] <;> ring

theorem star_one_add_smul_qi (D : ℚ) : star (1 + D • (qi : ℍ[ℚ, a, b])) = 1 - D • qi := by
  ext <;> simp [qi]

theorem star_one_add_smul_qj (D : ℚ) : star (1 + D • (qj : ℍ[ℚ, a, b])) = 1 - D • qj := by
  ext <;> simp [qj]

theorem main {q : ℕ} (hqp : q.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R)
    {r : ℕ} (hr : r.Prime) (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ x ∈ CosetGraph.awayUnits R v, ∃ y ∈ CosetGraph.awayUnits R v,
      (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ≠ (y : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) := by
  classical
  have ha : a < 0 := hdef.1
  have hb : b < 0 := hdef.2.1
  have hgen : pgen v = r := pgen_eq_of_prime_mem hr v hv

  have hsplit : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x := by
    have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
      rw [natCast_mem_asIdeal_iff, hgen]
      intro h
      exact hrq ((Nat.prime_dvd_prime_iff_eq hr hqp).1 h)
    have h := (hdef.2.2 v).not.2 hqv
    push Not at h
    exact h

  obtain ⟨B, -, hBR⟩ := hRo.exists_basis_span_eq
  obtain ⟨D₁, hD₁, hD₁i⟩ := QuaternionAlgebra.exists_natCast_smul_mem_of_mem_span (Λ := R) (y := qi)
    (by rw [hRo.spanTop]; trivial)
  obtain ⟨D₂, hD₂, hD₂j⟩ := QuaternionAlgebra.exists_natCast_smul_mem_of_mem_span (Λ := R) (y := qj)
    (by rw [hRo.spanTop]; trivial)
  set D : ℕ := D₁ * D₂ with hDdef
  have hD0 : D ≠ 0 := mul_ne_zero hD₁ hD₂
  have hDi : (D : ℚ) • (qi : ℍ[ℚ, a, b]) ∈ R := by
    have : (D : ℚ) • (qi : ℍ[ℚ, a, b]) = ((D₂ : ℕ) : ℤ) • ((((D₁ : ℕ) : ℤ)) • qi) := by
      rw [smul_smul, ← Int.cast_smul_eq_zsmul ℚ, hDdef]; push_cast; ring_nf
    rw [this]; exact R.smul_mem _ hD₁i
  have hDj : (D : ℚ) • (qj : ℍ[ℚ, a, b]) ∈ R := by
    have : (D : ℚ) • (qj : ℍ[ℚ, a, b]) = ((D₁ : ℕ) : ℤ) • ((((D₂ : ℕ) : ℤ)) • qj) := by
      rw [smul_smul, ← Int.cast_smul_eq_zsmul ℚ, hDdef]; push_cast; ring_nf
    rw [this]; exact R.smul_mem _ hD₂j
  set sI : ℍ[ℚ, a, b] := 1 + (D : ℚ) • qi with hsI
  set sJ : ℍ[ℚ, a, b] := 1 + (D : ℚ) • qj with hsJ
  have hsIR : sI ∈ R := R.add_mem hRo.one_mem hDi
  have hsJR : sJ ∈ R := R.add_mem hRo.one_mem hDj
  have hsI'R : star sI ∈ R := by rw [hsI, star_one_add_smul_qi]; exact R.sub_mem hRo.one_mem hDi
  have hsJ'R : star sJ ∈ R := by rw [hsJ, star_one_add_smul_qj]; exact R.sub_mem hRo.one_mem hDj
  set nI : ℚ := QuaternionAlgebra.nrd sI with hnI
  set nJ : ℚ := QuaternionAlgebra.nrd sJ with hnJ
  have hnIpos : 0 < nI := by
    rw [hnI, hsI]; simp only [qi, QuaternionAlgebra.nrd]; simp; nlinarith [sq_nonneg (D : ℚ)]
  have hnJpos : 0 < nJ := by
    rw [hnJ, hsJ]; simp only [qj, QuaternionAlgebra.nrd]; simp; nlinarith [sq_nonneg (D : ℚ)]

  obtain ⟨t₀, ht₀⟩ : ∃ t : Fin 4, B.coord t (qk : ℍ[ℚ, a, b]) ≠ 0 := by
    by_contra h
    push Not at h
    apply qk_ne_zero (a := a) (b := b)
    rw [← B.sum_repr qk]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [show B.repr qk t = B.coord t qk from rfl, h t, zero_smul]
  obtain ⟨t₁, ht₁⟩ : ∃ t : Fin 4, B.coord t (1 : ℍ[ℚ, a, b]) ≠ 0 := by
    by_contra h
    push Not at h
    apply (one_ne_zero : (1 : ℍ[ℚ, a, b]) ≠ 0)
    rw [← B.sum_repr 1]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [show B.repr 1 t = B.coord t 1 from rfl, h t, zero_smul]

  set ck : ℚ := B.coord t₀ (qk : ℍ[ℚ, a, b]) with hck
  set c1 : ℚ := B.coord t₁ (1 : ℍ[ℚ, a, b]) with hc1
  set bound : ℕ := 3 + r + D + nI.num.natAbs + nI.den + nJ.num.natAbs + nJ.den +
    ck.num.natAbs + ck.den + c1.num.natAbs + c1.den with hbound
  obtain ⟨ℓ, hℓb, hℓp⟩ := Nat.exists_infinite_primes bound
  set wl := place ℓ hℓp with hwl
  have hpg : pgen wl = ℓ := pgen_place ℓ hℓp
  have hℓ0 : pgen wl ≠ 0 := by rw [hpg]; exact hℓp.ne_zero
  have hwlv : wl ≠ v := by
    intro h; have := congrArg pgen h; rw [hpg, hgen] at this; omega
  have hℓ2 : ¬ ℓ ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
  have hℓD : ¬ ℓ ∣ D := fun h => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) h; omega
  have hvnI : wl.valuation ℚ nI = 1 := valuation_eq_one_of_lt wl hnIpos.ne' (by rw [hpg]; omega) (by rw [hpg]; omega)
  have hvnJ : wl.valuation ℚ nJ = 1 := valuation_eq_one_of_lt wl hnJpos.ne' (by rw [hpg]; omega) (by rw [hpg]; omega)
  have hvck : wl.valuation ℚ ck = 1 := valuation_eq_one_of_lt wl ht₀ (by rw [hpg]; omega) (by rw [hpg]; omega)
  have hvc1 : wl.valuation ℚ c1 = 1 := valuation_eq_one_of_lt wl ht₁ (by rw [hpg]; omega) (by rw [hpg]; omega)
  have hv8D : wl.valuation ℚ (8 * (D : ℚ) ^ 2) = 1 := by
    have h8 : wl.valuation ℚ ((8 : ℕ) : ℚ) = 1 := by
      refine valuation_natCast_eq_one_of_not_dvd wl ?_
      rw [hpg]; intro h
      exact hℓ2 ((Nat.Prime.dvd_mul hℓp).1 (show ℓ ∣ 2 * 4 from h) |>.elim id
        (fun h4 => (Nat.Prime.dvd_mul hℓp).1 (show ℓ ∣ 2 * 2 from h4) |>.elim id id))
    have hDv : wl.valuation ℚ ((D : ℕ) : ℚ) = 1 := valuation_natCast_eq_one_of_not_dvd wl (by rw [hpg]; exact hℓD)
    rw [map_mul, map_pow, hDv, one_pow, mul_one]
    exact_mod_cast h8

  obtain ⟨βI, hβI, cI, hcI, cI', hcI', zI, hzI, zI', hzI', eI, eI'⟩ :=
    exists_awayUnit_congr ha hb hRo v hsplit wl hwlv hℓ0 hsIR hsI'R hvnI
  obtain ⟨βJ, hβJ, cJ, hcJ, cJ', hcJ', zJ, hzJ, zJ', hzJ', eJ, eJ'⟩ :=
    exists_awayUnit_congr ha hb hRo v hsplit wl hwlv hℓ0 hsJR hsJ'R hvnJ
  refine ⟨βI, hβI, βJ, hβJ, fun hcomm => ?_⟩

  have hnI0 : nI ≠ 0 := hnIpos.ne'
  have hnJ0 : nJ ≠ 0 := hnJpos.ne'
  have hcnI : cst wl nI ≠ 0 := (map_ne_zero _).2 hnI0
  have hcnJ : cst wl nJ ≠ 0 := (map_ne_zero _).2 hnJ0
  have hinI : (cst wl nI)⁻¹ ∈ wl.adicCompletionIntegers ℚ := inv_cst_mem_integers wl hvnI
  have hinJ : (cst wl nJ)⁻¹ ∈ wl.adicCompletionIntegers ℚ := inv_cst_mem_integers wl hvnJ

  have hβImem := (mem_awayUnits_iff hRo v βI).1 hβI wl hwlv
  have hβJmem := (mem_awayUnits_iff hRo v βJ).1 hβJ wl hwlv
  have hKI : locK wl sI ∈ Submodule.localBox R wl := locK_mem hRo wl hsIR hvnI
  have hKJ : locK wl sJ ∈ Submodule.localBox R wl := locK_mem hRo wl hsJR hvnJ
  have hKI' : locK' wl sI ∈ Submodule.localBox R wl := locK'_mem hRo wl hsI'R hvnI
  have hKJ' : locK' wl sJ ∈ Submodule.localBox R wl := locK'_mem hRo wl hsJ'R hvnJ

  set dI : wl.adicCompletion ℚ := (cst wl nI)⁻¹ * cI with hdI
  set dJ : wl.adicCompletion ℚ := (cst wl nJ)⁻¹ * cJ with hdJ
  have hdImem : dI ∈ wl.adicCompletionIntegers ℚ := mul_mem hinI hcI
  have hdJmem : dJ ∈ wl.adicCompletionIntegers ℚ := mul_mem hinJ hcJ
  have eXI : locK wl sI * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] cI) = (sI * sI) ⊗ₜ[ℚ] dI := by
    rw [locK, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have eXJ : locK wl sJ * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] cJ) = (sJ * sJ) ⊗ₜ[ℚ] dJ := by
    rw [locK, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hXImem : (sI * sI) ⊗ₜ[ℚ] dI ∈ Submodule.localBox R wl := tmul_mem_localBox (hRo.mul_mem hsIR hsIR) wl hdImem
  have hXJmem : (sJ * sJ) ⊗ₜ[ℚ] dJ ∈ Submodule.localBox R wl := tmul_mem_localBox (hRo.mul_mem hsJR hsJR) wl hdJmem
  have mI : ModL R wl ((βI : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : wl.adicCompletion ℚ)) ((sI * sI) ⊗ₜ[ℚ] dI) := by
    rw [← eXI]; exact modL_of_eq_mul_add hRo hKI hzI eI
  have mJ : ModL R wl ((βJ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : wl.adicCompletion ℚ)) ((sJ * sJ) ⊗ₜ[ℚ] dJ) := by
    rw [← eXJ]; exact modL_of_eq_mul_add hRo hKJ hzJ eJ

  have unit_test : ∀ {β : (ℍ[ℚ, a, b])ˣ} {s : ℍ[ℚ, a, b]} {n : ℚ} {c c' : wl.adicCompletion ℚ}
      {z' : ℍ[ℚ, a, b] ⊗[ℚ] wl.adicCompletion ℚ},
      QuaternionAlgebra.nrd s = n → cst wl n ≠ 0 → star s ∈ R →
      wl.valuation ℚ n = 1 →
      c ∈ wl.adicCompletionIntegers ℚ → c' ∈ wl.adicCompletionIntegers ℚ →
      z' ∈ Submodule.localBox R wl →
      ((β⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : wl.adicCompletion ℚ) ∈ Submodule.localBox R wl →
      (s * s) ⊗ₜ[ℚ] ((cst wl n)⁻¹ * c) ∈ Submodule.localBox R wl →
      ModL R wl ((β : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : wl.adicCompletion ℚ)) ((s * s) ⊗ₜ[ℚ] ((cst wl n)⁻¹ * c)) →
      ((β⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : wl.adicCompletion ℚ) =
          ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c' + ((pgen wl : ℕ) : ℚ) • z') * locK' wl s →
      Valued.v c = 1 := by
    intro β s n c c' z' hn hcn hs' hvn hc hc' hz' hβ'mem hXmem m e'
    have hK' : locK' wl s ∈ Submodule.localBox R wl := locK'_mem hRo wl hs' (hn ▸ hvn)
    have m' : ModL R wl (((β⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : wl.adicCompletion ℚ))
        ((star s * star s) ⊗ₜ[ℚ] (c' * (cst wl n)⁻¹)) := by
      have := modL_of_eq_add_mul hRo hK' hz' e'
      rwa [locK', hn, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
    have mm := ModL.mul hRo m m' hXmem hβ'mem
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.mul_inv,
      mul_star_mul_star, hn, smul_one_tmul] at mm
    obtain ⟨m₀, hm₀, e₀⟩ := mm
    have e₁ : (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 - c * c') = ((pgen wl : ℕ) : ℚ) • m₀ := by
      rw [← e₀, TensorProduct.tmul_sub]
      congr 1
      rw [cst_mul]
      field_simp
    have hlt := valuation_coord_lt_one B hBR wl hm₀ e₁ t₁
    rw [map_mul, valued_algebraMap, ← hc1, hvc1, one_mul] at hlt
    exact v_eq_one_of_v_one_sub_mul_lt ((mem_integers_iff wl c).1 hc) ((mem_integers_iff wl c').1 hc') hlt
  have hvcI : Valued.v cI = 1 :=
    unit_test hnI.symm hcnI hsI'R hvnI hcI hcI' hzI' hβImem.2 hXImem mI eI'
  have hvcJ : Valued.v cJ = 1 :=
    unit_test hnJ.symm hcnJ hsJ'R hvnJ hcJ hcJ' hzJ' hβJmem.2 hXJmem mJ eJ'

  have mIJ := ModL.mul hRo mI mJ hXImem hβJmem.1
  have mJI := ModL.mul hRo mJ mI hXJmem hβImem.1
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at mIJ mJI
  rw [hcomm] at mIJ
  obtain ⟨m₀, hm₀, e₀⟩ := (mIJ.symm).trans mJI
  have e₁ : ((8 * (D : ℚ) ^ 2) • (qk : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (dI * dJ) = ((pgen wl : ℕ) : ℚ) • m₀ := by
    rw [← e₀, mul_comm dJ dI, ← TensorProduct.sub_tmul, ← sq_comm_sq (D : ℚ)]
  have hlt := valuation_coord_lt_one B hBR wl hm₀ e₁ t₀
  rw [map_smul, smul_eq_mul, map_mul, valued_algebraMap, map_mul, ← hck, hv8D, hvck, one_mul, one_mul, hdI, hdJ] at hlt
  simp only [map_mul, map_inv₀, valued_algebraMap, hvnI, hvnJ, hvcI, hvcJ, inv_one, mul_one] at hlt
  exact lt_irrefl _ hlt

end Main

end NoncommPair

end

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra IsDedekindDomain CerednikDrinfeld

theorem solution
    {rbar : ℕ} [Fact rbar.Prime]
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR : IsOrder R)
    (r : ℕ) [Fact r.Prime] (hrr : rbar ≠ r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R v, ∃ y ∈ CerednikDrinfeld.CosetGraph.awayUnits R v,
      (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ≠ (y : ℍ[ℚ, a₁, b₁]) * (x : ℍ[ℚ, a₁, b₁]) :=
  NoncommPair.main Fact.out hdef hR Fact.out hrr.symm v hv

end S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt (solution)
