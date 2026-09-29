-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c7166fd0-da2a-57b9-a8a5-28e4bdb981c6

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
import Theorems.Thm_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isDefiniteRamifiedExactlyAt
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

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

namespace R1AwayNrd

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

section AuxPrime

theorem exists_prime_not_isSquare (r : ℕ) (hr : r.Prime) (n : ℕ) :
    ∃ ℓ : ℕ, n < ℓ ∧ ℓ.Prime ∧ ¬ IsSquare ((r : ZMod ℓ)) := by
  rcases eq_or_ne r 2 with rfl | hr2
  ·
    obtain ⟨ℓ, hℓn, hℓ, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max n 2) (q := 8) (a := 3)
      (by norm_num) (by norm_num)
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓ2 : ℓ ≠ 2 := by
      have := le_max_right n 2; omega
    refine ⟨ℓ, lt_of_le_of_lt (le_max_left n 2) hℓn, hℓ, ?_⟩
    rw [Nat.cast_ofNat, ZMod.exists_sq_eq_two_iff hℓ2]
    have h3 : ℓ % 8 = 3 := hmod
    omega
  ·
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨n₀, hn₀⟩ := FiniteField.exists_nonsquare (F := ZMod r) (by rw [ZMod.ringChar_zmod_n]; exact hr2)
    have h4 : (4 : ZMod r) ≠ 0 := by
      intro h
      have h' : ((4 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have : r ∣ 2 ^ 2 := by simpa using h'
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow this))
    have hn₀0 : n₀ ≠ 0 := by rintro rfl; exact hn₀ ⟨0, by simp⟩
    set t : ℕ := ((n₀ - 1) * (4 : ZMod r)⁻¹).val with ht
    set a₀ : ℕ := 1 + 4 * t with ha₀
    have ha₀r : (a₀ : ZMod r) = n₀ := by
      rw [ha₀, Nat.cast_add, Nat.cast_one, Nat.cast_mul, ht, ZMod.natCast_val, ZMod.cast_id', id,
        Nat.cast_ofNat, mul_comm, mul_assoc, inv_mul_cancel₀ h4, mul_one]
      ring
    have hcop : a₀.Coprime (4 * r) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · rw [ha₀]
        exact (Nat.coprime_add_mul_left_left 1 4 t).2 (Nat.coprime_one_left 4)
      · rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
        intro hdvd
        apply hn₀0
        rw [← ha₀r, (ZMod.natCast_eq_zero_iff a₀ r).2 hdvd]
    obtain ⟨ℓ, hℓn, hℓ, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max n r) (q := 4 * r) (a := a₀)
      (mul_ne_zero four_ne_zero hr.ne_zero) hcop
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓ4 : ℓ % 4 = 1 := by
      have h1 : ℓ ≡ a₀ [MOD 4] := Nat.ModEq.of_mul_right r hmod
      have h2 : a₀ % 4 = 1 := by rw [ha₀]; omega
      have h3 : ℓ ≡ 1 [MOD 4] := h1.trans h2
      exact h3
    have hℓr : (ℓ : ZMod r) = n₀ := by
      rw [← ha₀r]
      exact (ZMod.natCast_eq_natCast_iff ℓ a₀ r).2 (Nat.ModEq.of_mul_left 4 hmod)
    refine ⟨ℓ, lt_of_le_of_lt (le_max_left n r) hℓn, hℓ, ?_⟩
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hℓ4 hr2, hℓr]
    exact hn₀

end AuxPrime

section Coord

variable {a b : ℚ}

abbrev cst (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) q

theorem cst_zpow (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) (n : ℤ) : cst w (x ^ n) = cst w x ^ n :=
  map_zpow₀ _ x n

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

theorem trd_hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.trd (hatQ w x) = cst w (QuaternionAlgebra.trd x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [hatQ, QuaternionAlgebra.trd, map_mul]

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

theorem trd_smul' {K : Type*} [CommRing K] {c₁ c₃ : K} (c : K) (x : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.trd (c • x) = c * QuaternionAlgebra.trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.trd_mk, smul_eq_mul]
  ring

theorem trd_add' {K : Type*} [CommRing K] {c₁ c₃ : K} (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.trd (x + y) = QuaternionAlgebra.trd x + QuaternionAlgebra.trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.trd_mk]
  ring

theorem trd_neg' {K : Type*} [CommRing K] {c₁ c₃ : K} (x : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.trd (-x) = -QuaternionAlgebra.trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [QuaternionAlgebra.trd]

theorem trd_zero' {K : Type*} [CommRing K] {c₁ c₃ : K} :
    QuaternionAlgebra.trd (0 : ℍ[K, c₁, c₃]) = 0 := by
  simp [QuaternionAlgebra.trd]

theorem nrd_add' {K : Type*} [CommRing K] {c₁ c₃ : K} (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (x + y) =
      QuaternionAlgebra.nrd x + QuaternionAlgebra.nrd y + QuaternionAlgebra.trd (x * star y) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.nrd_mk, QuaternionAlgebra.trd,
    QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, zero_mul, add_zero]
  ring

theorem nrd_coe_add_smul {K : Type*} [CommRing K] {c₁ c₃ : K} (c ℓ : K) (Z : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd ((c : ℍ[K, c₁, c₃]) + ℓ • Z) =
      c ^ 2 + ℓ * (c * QuaternionAlgebra.trd Z + ℓ * QuaternionAlgebra.nrd Z) := by
  obtain ⟨Z₀, Z₁, Z₂, Z₃⟩ := Z
  have e : ((c : ℍ[K, c₁, c₃]) + ℓ • (⟨Z₀, Z₁, Z₂, Z₃⟩ : ℍ[K, c₁, c₃])) =
      ⟨c + ℓ * Z₀, ℓ * Z₁, ℓ * Z₂, ℓ * Z₃⟩ := by
    ext <;> simp
  rw [e, QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd_mk, QuaternionAlgebra.trd_mk]
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

theorem exists_isCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      IsCoord a b w φ := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (w.adicCompletion ℚ) a) (d₂ := (0 : w.adicCompletion ℚ))
    (d₃ := algebraMap ℚ (w.adicCompletion ℚ) b) rfl (map_zero _) rfl AlgEquiv.refl
  exact ⟨φ, fun z r => by rw [hφ]; rfl⟩

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

def barT (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
  φ.symm (star (φ x))

theorem φ_barT (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : φ (barT φ x) = star (φ x) := by
  rw [barT, RingEquiv.apply_symm_apply]

theorem barT_add (x x' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : barT φ (x + x') = barT φ x + barT φ x' := by
  apply φ.injective
  rw [RingEquiv.map_add, φ_barT, φ_barT, φ_barT, RingEquiv.map_add, star_add]

theorem barT_neg (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : barT φ (-x) = -barT φ x := by
  apply φ.injective
  rw [RingEquiv.map_neg, φ_barT, φ_barT, RingEquiv.map_neg, star_neg]

theorem barT_zero : barT φ (0 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 0 := by
  apply φ.injective
  rw [φ_barT, RingEquiv.map_zero]
  exact star_zero _

theorem barT_tmul (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) (c : w.adicCompletion ℚ) :
    barT φ (z ⊗ₜ[ℚ] c) = (star z) ⊗ₜ[ℚ] c := by
  apply φ.injective
  rw [φ_barT, hφ.tmul, hφ.tmul, hatQ_star]
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  ext <;> simp [hatQ]

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

theorem star_mem (hO : QuaternionAlgebra.IsOrder O) {z : ℍ[ℚ, a, b]} (hz : z ∈ O) : star z ∈ O := by
  obtain ⟨⟨t, n, ht, hn⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hz
  have e : star z = (t : ℤ) • (1 : ℍ[ℚ, a, b]) - z := by
    have h1 : z + star z = ((QuaternionAlgebra.trd z : ℚ) : ℍ[ℚ, a, b]) := QuaternionAlgebra.add_star_eq_coe_trd z
    rw [ht] at h1
    have : star z = ((t : ℚ) : ℍ[ℚ, a, b]) - z := by rw [← h1]; abel
    rw [this, ← Int.cast_smul_eq_zsmul ℚ]
    congr 1
    ext <;> simp
  rw [e]
  exact O.sub_mem (O.smul_mem _ hO.one_mem) hz

variable {w : HeightOneSpectrum (𝓞 ℚ)}
  {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}

theorem barT_mem_localBox (hO : QuaternionAlgebra.IsOrder O) (hφ : IsCoord a b w φ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox O w) :
    barT φ x ∈ Submodule.localBox O w := by
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    rw [barT_tmul hφ]
    exact tmul_mem_localBox (star_mem hO hz) w hc
  | zero => rw [barT_zero]; exact AddSubgroup.zero_mem _
  | add u u' _ _ hu hu' => rw [barT_add]; exact AddSubgroup.add_mem _ hu hu'
  | neg u _ hu => rw [barT_neg]; exact AddSubgroup.neg_mem _ hu

theorem trd_mem_integers (hO : QuaternionAlgebra.IsOrder O) (hφ : IsCoord a b w φ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox O w) :
    QuaternionAlgebra.trd (φ x) ∈ w.adicCompletionIntegers ℚ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    obtain ⟨⟨t, n, ht, hn⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hz
    rw [hφ.tmul, trd_smul', trd_hatQ, ht, show cst w (t : ℚ) = (t : w.adicCompletion ℚ) from map_intCast _ t]
    exact mul_mem hc (intCast_mem_integers w t)
  | zero => rw [RingEquiv.map_zero, trd_zero']; exact zero_mem _
  | add u u' _ _ hu hu' => rw [RingEquiv.map_add, trd_add']; exact add_mem hu hu'
  | neg u _ hu => rw [RingEquiv.map_neg, trd_neg']; exact neg_mem hu

theorem nrd_mem_integers (hO : QuaternionAlgebra.IsOrder O) (hφ : IsCoord a b w φ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox O w) :
    QuaternionAlgebra.nrd (φ x) ∈ w.adicCompletionIntegers ℚ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    obtain ⟨⟨t, n, ht, hn⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hz
    rw [hφ.tmul, nrd_smul', nrd_hatQ, hn, show cst w (n : ℚ) = (n : w.adicCompletion ℚ) from map_intCast _ n]
    exact mul_mem (pow_mem hc 2) (intCast_mem_integers w n)
  | zero => rw [RingEquiv.map_zero, QuaternionAlgebra.nrd_zero]; exact zero_mem _
  | add u u' hu₀ hu'₀ hu hu' =>
    rw [RingEquiv.map_add, nrd_add', ← φ_barT, ← RingEquiv.map_mul]
    exact add_mem (add_mem hu hu')
      (trd_mem_integers hO hφ (mul_mem_localBox hO w hu₀ (barT_mem_localBox hO hφ hu'₀)))
  | neg u _ hu => rw [RingEquiv.map_neg, QuaternionAlgebra.nrd_neg]; exact hu

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

theorem exists_natCast_smul_mem_of_tmul_one_mem_localBox {R : Submodule ℤ ℍ[ℚ, a, b]}
    (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (hBR : Submodule.span ℤ (Set.range B) = R)
    (w : HeightOneSpectrum (𝓞 ℚ)) {x : ℍ[ℚ, a, b]}
    (hx : x ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w) :
    ∃ n : ℕ, ¬ pgen w ∣ n ∧ (n : ℚ) • x ∈ R := by
  have hden : ∀ i, ¬ pgen w ∣ (B.repr x i).den := by
    intro i hdvd
    have hint := extendScalar_coord_mem_integers B hBR w i hx
    rw [extendScalar_tmul, Module.Basis.coord_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      Algebra.smul_def, mul_one, valued_algebraMap, Rat.valuation_le_one_iff_den] at hint
    exact hint ((natCast_mem_asIdeal_iff w _).2 hdvd)
  refine ⟨∏ i, (B.repr x i).den, ?_, ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (pgen_prime w).prime _).1 h
    exact hden i hi
  · rw [← hBR, Module.Basis.mem_span_iff_repr_mem]
    intro i
    refine ⟨(∏ j ∈ Finset.univ.erase i, ((B.repr x j).den : ℤ)) * (B.repr x i).num, ?_⟩
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
      Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num]
    simp

theorem exists_pow_smul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) {x : ℍ[ℚ, a, b]}
    (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      x ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w) :
    ∃ k : ℕ, ((r ^ k : ℕ) : ℚ) • x ∈ R := by
  obtain ⟨B, -, hBR⟩ := hR.exists_basis_span_eq
  have hgen : pgen v = r := pgen_eq_of_prime_mem hr v hv
  have step : ∀ p : ℕ, p.Prime → p ≠ r → ∃ n : ℕ, ¬ p ∣ n ∧ (n : ℚ) • x ∈ R := by
    intro p hp hpr
    have hw : place p hp ≠ v := by
      intro h; apply hpr; rw [← pgen_place p hp, h, hgen]
    obtain ⟨n, hn, hnx⟩ := exists_natCast_smul_mem_of_tmul_one_mem_localBox B hBR (place p hp) (hx _ hw)
    rw [pgen_place] at hn
    exact ⟨n, hn, hnx⟩
  let I : Ideal ℤ := R.comap (LinearMap.toSpanSingleton ℤ ℍ[ℚ, a, b] x)
  have hI : ∀ n : ℤ, n ∈ I ↔ (n : ℚ) • x ∈ R := by
    intro n
    simp only [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Int.cast_smul_eq_zsmul ℚ]
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = Submodule.IsPrincipal.generator I := ⟨_, rfl⟩
  have hdI : d ∈ I := hd ▸ Submodule.IsPrincipal.generator_mem I
  have hdvd : ∀ n : ℤ, n ∈ I → d ∣ n := fun n hn =>
    hd ▸ (Submodule.IsPrincipal.mem_iff_generator_dvd I).1 hn
  have hprime : ∀ {p : ℕ}, p.Prime → p ∣ d.natAbs → p = r := by
    intro p hp hpd
    by_contra hpr
    obtain ⟨n, hn, hnx⟩ := step p hp hpr
    apply hn
    have h1 : d ∣ (n : ℤ) := hdvd n ((hI n).2 (by exact_mod_cast hnx))
    have h2 : (p : ℤ) ∣ (n : ℤ) := (Int.natCast_dvd.2 hpd).trans h1
    exact Int.natCast_dvd_natCast.1 h2
  have hd0 : d.natAbs ≠ 0 := by
    obtain ⟨p, hp, hpr⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ r := by
      by_cases h : r = 2
      · exact ⟨3, Nat.prime_three, by omega⟩
      · exact ⟨2, Nat.prime_two, fun e => h e.symm⟩
    obtain ⟨n, hn, hnx⟩ := step p hp hpr
    intro hd0
    have h1 : d ∣ (n : ℤ) := hdvd n ((hI n).2 (by exact_mod_cast hnx))
    rw [Int.natAbs_eq_zero.1 hd0, zero_dvd_iff, Int.natCast_eq_zero] at h1
    exact hn (h1 ▸ dvd_zero p)
  refine ⟨d.natAbs.primeFactorsList.length, ?_⟩
  rw [← Nat.eq_prime_pow_of_unique_prime_dvd hd0 hprime]
  have hmem : ((d.natAbs : ℤ) : ℚ) • x ∈ R := by
    rw [← hI]
    rcases Int.natAbs_eq d with h | h
    · rw [← h]; exact hdI
    · have : (d.natAbs : ℤ) = -d := by omega
      rw [this]; exact I.neg_mem hdI
  exact_mod_cast hmem

theorem nrd_eq_zpow_of_pow_smul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (ha : a < 0) (hb : b < 0)
    {r : ℕ} (hr : r.Prime) {x x' : ℍ[ℚ, a, b]} (hxx' : x * x' = 1)
    {k k' : ℕ} (hk : ((r ^ k : ℕ) : ℚ) • x ∈ R) (hk' : ((r ^ k' : ℕ) : ℚ) • x' ∈ R) :
    ∃ j : ℤ, QuaternionAlgebra.nrd x = (r : ℚ) ^ j := by
  obtain ⟨⟨-, A, -, hA⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hR hk
  obtain ⟨⟨-, B, -, hB⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hR hk'
  rw [nrd_smul'] at hA hB
  have hnn : QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd x' = 1 := by
    rw [← nrd_mul', hxx', QuaternionAlgebra.nrd_one]
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
  have hAB : (A : ℚ) * B = (r : ℚ) ^ (2 * k + 2 * k') := by
    rw [← hA, ← hB]
    calc ((r ^ k : ℕ) : ℚ) ^ 2 * QuaternionAlgebra.nrd x * (((r ^ k' : ℕ) : ℚ) ^ 2 * QuaternionAlgebra.nrd x')
        = ((r ^ k : ℕ) : ℚ) ^ 2 * ((r ^ k' : ℕ) : ℚ) ^ 2 * (QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd x') := by ring
      _ = (r : ℚ) ^ (2 * k + 2 * k') := by rw [hnn, mul_one]; push_cast; ring
  have hAB' : A * B = (r : ℤ) ^ (2 * k + 2 * k') := by exact_mod_cast hAB
  have hAdvd : A.natAbs ∣ r ^ (2 * k + 2 * k') := by
    have : A ∣ (r : ℤ) ^ (2 * k + 2 * k') := ⟨B, hAB'.symm⟩
    have h2 := Int.natAbs_dvd_natAbs.2 this
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).1 hAdvd

  have hpos : 0 < QuaternionAlgebra.nrd x := by
    rcases (nrd_nonneg ha hb x).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, zero_mul] at hnn; exact zero_ne_one hnn
  have hApos : 0 < (A : ℚ) := by
    rw [← hA]
    exact mul_pos (pow_pos (by exact_mod_cast pow_pos hr.pos k) 2) hpos
  have hAeq : A = (r : ℤ) ^ i := by
    rcases Int.natAbs_eq A with h | h
    · rw [h, hi]; push_cast; ring
    · exfalso
      have : (A : ℚ) ≤ 0 := by
        have h' : A ≤ 0 := by rw [h]; simp
        exact_mod_cast h'
      linarith
  refine ⟨(i : ℤ) - 2 * k, ?_⟩
  have hne : ((r ^ k : ℕ) : ℚ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast pow_ne_zero k hr.ne_zero)
  have e : QuaternionAlgebra.nrd x = (A : ℚ) / ((r ^ k : ℕ) : ℚ) ^ 2 := by
    rw [eq_div_iff hne, ← hA, mul_comm]
  rw [e, hAeq, zpow_sub₀ hr0, show ((2 : ℤ) * k) = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    zpow_natCast]
  push_cast
  ring

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

variable {w : HeightOneSpectrum (𝓞 ℚ)}
  {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}

theorem exists_nrd_eq_sq_add_of_mem_localBox_auxOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    (hφ : IsCoord a b w φ) (ℓ : ℕ)
    {X : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hX : X ∈ Submodule.localBox (auxOrder R ℓ) w) :
    ∃ c ∈ w.adicCompletionIntegers ℚ, ∃ t ∈ w.adicCompletionIntegers ℚ,
      QuaternionAlgebra.nrd (φ X) = c ^ 2 + (ℓ : w.adicCompletion ℚ) * t := by
  obtain ⟨c, hc, z, hz, rfl⟩ := exists_eq_of_mem_localBox_auxOrder R ℓ w hX
  refine ⟨c, hc, c * QuaternionAlgebra.trd (φ z) + (ℓ : w.adicCompletion ℚ) * QuaternionAlgebra.nrd (φ z),
    add_mem (mul_mem hc (trd_mem_integers hR hφ hz))
      (mul_mem (natCast_mem_integers w ℓ) (nrd_mem_integers hR hφ hz)), ?_⟩
  have e : φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c + (ℓ : ℚ) • z) =
      (c : ℍ[w.adicCompletion ℚ, cst w a, cst w b]) + (ℓ : w.adicCompletion ℚ) • φ z := by
    rw [RingEquiv.map_add, hφ.one_tmul, Nat.cast_smul_eq_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]
  rw [e, nrd_coe_add_smul]

end AuxOrder

section Main

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

theorem exists_place_not_isSquare (r : ℕ) (hr : r.Prime) (n : ℕ) :
    ∃ wl : HeightOneSpectrum (𝓞 ℚ), n < pgen wl ∧ ¬ IsSquare ((r : ZMod (pgen wl))) := by
  obtain ⟨ℓ, h1, hℓ, h2⟩ := exists_prime_not_isSquare r hr n
  refine ⟨place ℓ hℓ, by rw [pgen_place]; exact h1, ?_⟩
  exact (congrArg (fun m : ℕ => ¬ IsSquare ((r : ZMod m))) (pgen_place ℓ hℓ)).mpr h2

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

theorem isSquare_of_sq_eq_pow_odd {F : Type*} [Field F] {r X : F} (hr : r ≠ 0) {e : ℕ}
    (hX : X ^ 2 = r ^ (2 * e + 1)) : IsSquare r := by
  have hre : r ^ e ≠ 0 := pow_ne_zero _ hr
  refine ⟨X * (r ^ e)⁻¹, ?_⟩
  have h1 : X * (r ^ e)⁻¹ * (X * (r ^ e)⁻¹) = X ^ 2 * ((r ^ e)⁻¹ * (r ^ e)⁻¹) := by ring
  have h2 : r ^ (2 * e + 1) = r * (r ^ e * r ^ e) := by rw [pow_succ, two_mul, pow_add]; ring
  rw [h1, hX, h2, mul_assoc, mul_mul_mul_comm, mul_inv_cancel₀ hre, one_mul, mul_one]

theorem main {q : ℕ} (hqp : q.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    {r : ℕ} (hr : r.Prime) (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ γ : (ℍ[ℚ, a, b])ˣ, γ ∈ CosetGraph.awayUnits R v ∧
      QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) = (r : ℚ) := by
  classical
  haveI : Fact q.Prime := ⟨hqp⟩
  have hRo : IsOrder R := hR.isOrder
  have ha : a < 0 := hdef.1
  have hb : b < 0 := hdef.2.1
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
  have hgen : pgen v = r := pgen_eq_of_prime_mem hr v hv

  have hsplit : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x := by
    have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
      rw [natCast_mem_asIdeal_iff, hgen]
      intro h
      exact hrq ((Nat.prime_dvd_prime_iff_eq hr hqp).1 h)
    have h := (hdef.2.2 v).not.2 hqv
    push Not at h
    exact h

  obtain ⟨wl, hbig, hns⟩ := exists_place_not_isSquare r hr (q + r + 2)
  have hℓ : (pgen wl).Prime := pgen_prime wl
  haveI : Fact (pgen wl).Prime := ⟨hℓ⟩
  have hℓr : pgen wl ≠ r := by omega
  have hℓ0 : pgen wl ≠ 0 := hℓ.ne_zero
  have hwlv : wl ≠ v := by intro h; apply hℓr; rw [h, hgen]
  have hrℓ : ((r : ℕ) : ZMod (pgen wl)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hℓr ((Nat.prime_dvd_prime_iff_eq hℓ hr).1 h)

  set O : Submodule ℤ ℍ[ℚ, a, b] := auxOrder R (pgen wl) with hOdef
  have hO : IsOrder O := isOrder_auxOrder hRo hℓ0
  have hOR : O ≤ R := auxOrder_le hRo (pgen wl)

  set ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ :=
    fun w => if w = v then 1 else cst w (r : ℚ) with hε
  have hεv : ∀ w, Valued.v (ε w) = 1 := by
    intro w
    by_cases hw : w = v
    · simp [hε, hw]
    · rw [hε]
      simp only [if_neg hw]
      rw [valued_algebraMap, valuation_natCast_eq_one_of_not_dvd]
      intro hdvd
      apply hw
      apply pgen_injective
      rw [hgen]
      exact (Nat.prime_dvd_prime_iff_eq (pgen_prime w) hr).1 hdvd
  have hεne : ∀ w, w ≠ v → ε w = cst w (r : ℚ) := fun w hw => by simp [hε, hw]
  obtain ⟨m, hmstab, hm⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isDefiniteRamifiedExactlyAt hdef hR ε hεv

  obtain ⟨β₀', hβ₀'⟩ :=
    QuaternionAlgebra.exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt hdef (r : ℚ) (by exact_mod_cast hr.pos)
  have hβ₀mul : β₀' * ((r : ℚ)⁻¹ • star β₀') = 1 := by
    rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd, hβ₀', QuaternionAlgebra.smul_coe,
      inv_mul_cancel₀ hr0]; rfl
  have hβ₀mul' : ((r : ℚ)⁻¹ • star β₀') * β₀' = 1 := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd, hβ₀', QuaternionAlgebra.smul_coe,
      inv_mul_cancel₀ hr0]; rfl
  set β₀ : (ℍ[ℚ, a, b])ˣ := ⟨β₀', (r : ℚ)⁻¹ • star β₀', hβ₀mul, hβ₀mul'⟩ with hβ₀def
  have hnβ₀ : QuaternionAlgebra.nrd (β₀ : ℍ[ℚ, a, b]) = r := hβ₀'
  have hnβ₀inv : QuaternionAlgebra.nrd ((β₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (r : ℚ)⁻¹ := by
    have h : QuaternionAlgebra.nrd ((β₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * QuaternionAlgebra.nrd (β₀ : ℍ[ℚ, a, b]) = 1 := by
      rw [← nrd_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, QuaternionAlgebra.nrd_one]
    rw [hnβ₀] at h
    exact eq_inv_of_mul_eq_one_left h

  set D := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] with hD
  set y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (D β₀)⁻¹ * m with hy
  have hynorm : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ →
        QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
          (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) = 1 := by
    intro w hw φ hφ
    rw [hy, Units.val_mul, map_mul, RingEquiv.map_mul, nrd_mul', ← map_inv, ← coe_evU, coe_evU_diagonal,
      nrd_φ_tmul_one hφ, hnβ₀inv, hm w φ hφ, hεne w hw, ← map_mul, inv_mul_cancel₀ hr0, map_one]
  obtain ⟨β, g, u, hu, hg, hyeq⟩ :=
    QuaternionAlgebra.IsOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one ha hb hO v hsplit y hynorm

  set γ₁ : (ℍ[ℚ, a, b])ˣ := β₀ * β with hγ₁
  have hDγ₁ : D γ₁ = m * u⁻¹ * g⁻¹ := by
    have h1 : m = D β₀ * (D β * g * u) := by
      rw [← hyeq, hy, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hγ₁, map_mul, h1]; group
  have hev : ∀ w, w ≠ v → evU a b w (D γ₁) = evU a b w m * (evU a b w u)⁻¹ := by
    intro w hw
    have hg1 : evU a b w g = 1 := Units.ext (by rw [coe_evU, Units.val_one]; exact hg w hw)
    rw [hDγ₁, map_mul, map_mul, map_inv, map_inv, hg1, inv_one, mul_one]
  have hmloc := (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
    R hRo m).1 hmstab
  have huloc := (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
    O hO u).1 hu
  have hloc : ∀ w, w ≠ v →
      (γ₁ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w ∧
      ((γ₁⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w := by
    intro w hw
    have hm' := hmloc w
    have hu' := huloc w
    rw [Submodule.mem_localBoxUnits_iff] at hm' hu'
    constructor
    · rw [← coe_evU_diagonal w γ₁, ← hD, hev w hw, Units.val_mul]
      exact mul_mem_localBox hRo w hm'.1 (localBox_mono hOR w hu'.2)
    · rw [← coe_evU_diagonal w γ₁⁻¹, ← hD, map_inv, map_inv, hev w hw, mul_inv_rev, inv_inv, Units.val_mul]
      exact mul_mem_localBox hRo w (localBox_mono hOR w hu'.1) hm'.2
  have hγ₁away : γ₁ ∈ CosetGraph.awayUnits R v := (mem_awayUnits_iff hRo v γ₁).2 hloc

  obtain ⟨k, hk⟩ := exists_pow_smul_mem hRo hr v hv (fun w hw => (hloc w hw).1)
  obtain ⟨k', hk'⟩ := exists_pow_smul_mem hRo hr v hv (fun w hw => (hloc w hw).2)
  obtain ⟨j, hj⟩ := nrd_eq_zpow_of_pow_smul_mem hRo ha hb hr
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hk hk'

  obtain ⟨φ, hφ⟩ := exists_isCoord a b wl
  have hu' := huloc wl
  rw [Submodule.mem_localBoxUnits_iff] at hu'
  obtain ⟨c, hc, t, ht, hct⟩ := exists_nrd_eq_sq_add_of_mem_localBox_auxOrder hRo hφ (pgen wl) hu'.2
  have hK : (cst wl (r : ℚ)) ^ j = cst wl (r : ℚ) * (c ^ 2 + (pgen wl : wl.adicCompletion ℚ) * t) := by
    have h1 := congrArg (fun U : (ℍ[ℚ, a, b] ⊗[ℚ] wl.adicCompletion ℚ)ˣ =>
      QuaternionAlgebra.nrd (φ (U : ℍ[ℚ, a, b] ⊗[ℚ] wl.adicCompletion ℚ))) (hev wl hwlv)
    rw [hD, coe_evU_diagonal wl γ₁, nrd_φ_tmul_one hφ, hj, cst_zpow, Units.val_mul, RingEquiv.map_mul,
      nrd_mul', hct, coe_evU, hm wl φ hφ, hεne wl hwlv] at h1
    exact h1
  have hrK : cst wl (r : ℚ) = ((r : ℕ) : wl.adicCompletion ℚ) := map_natCast _ r
  rw [hrK] at hK
  have hrK0 : ((r : ℕ) : wl.adicCompletion ℚ) ≠ 0 := by rw [← hrK]; exact (map_ne_zero _).2 hr0

  have hjodd : Odd j := by
    by_contra hjev
    rw [Int.not_odd_iff_even] at hjev
    obtain ⟨i, hi⟩ := hjev
    apply hns

    set M : ℕ := j.natAbs + 1 with hM
    have hipos : 0 ≤ i + M - 1 := by omega
    set e : ℕ := (i + M - 1).toNat with hedef
    have he : (e : ℤ) = i + M - 1 := Int.toNat_of_nonneg hipos
    have hexp : ((2 * e + 1 : ℕ) : ℤ) = ((2 * M - 1 : ℕ) : ℤ) + j := by
      have hM1 : 1 ≤ 2 * M := by omega
      push_cast [Nat.cast_sub hM1]
      omega
    have hKnat : ((r : ℕ) : wl.adicCompletion ℚ) ^ (2 * e + 1) =
        (((r : ℕ) : wl.adicCompletion ℚ) ^ M * c) ^ 2 +
          (pgen wl : wl.adicCompletion ℚ) * (((r : ℕ) : wl.adicCompletion ℚ) ^ (2 * M) * t) := by
      have h2M : 2 * M = (2 * M - 1) + 1 := by omega
      calc ((r : ℕ) : wl.adicCompletion ℚ) ^ (2 * e + 1)
          = ((r : ℕ) : wl.adicCompletion ℚ) ^ (2 * M - 1) * ((r : ℕ) : wl.adicCompletion ℚ) ^ j := by
            rw [← zpow_natCast, hexp, zpow_add₀ hrK0, zpow_natCast]
        _ = ((r : ℕ) : wl.adicCompletion ℚ) ^ (2 * M - 1) * ((r : ℕ) : wl.adicCompletion ℚ) *
              (c ^ 2 + (pgen wl : wl.adicCompletion ℚ) * t) := by rw [hK, mul_assoc]
        _ = ((r : ℕ) : wl.adicCompletion ℚ) ^ (2 * M) * (c ^ 2 + (pgen wl : wl.adicCompletion ℚ) * t) := by
            rw [← pow_succ, ← h2M]
        _ = _ := by rw [pow_mul]; ring

    set S := wl.adicCompletionIntegers ℚ with hS
    have hrS : ((r : ℕ) : wl.adicCompletion ℚ) ∈ S := natCast_mem_integers wl r
    set Cz : S := ⟨((r : ℕ) : wl.adicCompletion ℚ) ^ M * c, mul_mem (pow_mem hrS M) hc⟩ with hCz
    set Tz : S := ⟨((r : ℕ) : wl.adicCompletion ℚ) ^ (2 * M) * t, mul_mem (pow_mem hrS _) ht⟩ with hTz
    have hZ : ((r : ℕ) : S) ^ (2 * e + 1) = Cz ^ 2 + ((pgen wl : ℕ) : S) * Tz := by
      apply Subtype.ext
      push_cast
      exact hKnat
    haveI : Fact (Nat.Prime ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) wl : Nat.Primes) : ℕ)) :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) wl).2⟩
    let ψ : S →+* ZMod (pgen wl) := (PadicInt.toZMod).comp
      ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) wl).toAlgEquiv.toRingEquiv.toRingHom)
    have hF := congrArg ψ hZ
    rw [map_pow, map_natCast, map_add, map_pow, map_mul, map_natCast, ZMod.natCast_self, zero_mul,
      add_zero] at hF
    exact isSquare_of_sq_eq_pow_odd hrℓ hF.symm

  obtain ⟨i, hi⟩ := hjodd
  have hri : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ∀ n : ℤ,
      (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] cst w ((r : ℚ) ^ n) ∈ Submodule.localBox R w := by
    intro w hw n
    refine tmul_mem_localBox hRo.one_mem w (zpow_natCast_mem_integers w ?_ n)
    intro hdvd
    apply hw
    apply pgen_injective
    rw [hgen]
    exact (Nat.prime_dvd_prime_iff_eq (pgen_prime w) hr).1 hdvd
  have hsc : ∀ (n : ℤ) (x : ℍ[ℚ, a, b]) (w : HeightOneSpectrum (𝓞 ℚ)),
      (((r : ℚ) ^ n) • x) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = (x ⊗ₜ[ℚ] 1) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] cst w ((r : ℚ) ^ n)) := by
    intro n x w
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have hmul1 : ((r : ℚ) ^ (-i)) • (γ₁ : ℍ[ℚ, a, b]) * (((r : ℚ) ^ i) • ((γ₁⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1 := by
    rw [smul_mul_smul_comm, ← zpow_add₀ hr0, neg_add_cancel, zpow_zero, one_smul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  have hmul2 : (((r : ℚ) ^ i) • ((γ₁⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) * (((r : ℚ) ^ (-i)) • (γ₁ : ℍ[ℚ, a, b])) = 1 := by
    rw [smul_mul_smul_comm, ← zpow_add₀ hr0, add_neg_cancel, zpow_zero, one_smul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  refine ⟨⟨_, _, hmul1, hmul2⟩, ?_, ?_⟩
  · rw [mem_awayUnits_iff hRo]
    intro w hw
    constructor
    · change (((r : ℚ) ^ (-i)) • (γ₁ : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ _
      rw [hsc]
      exact mul_mem_localBox hRo w (hloc w hw).1 (hri w hw _)
    · change (((r : ℚ) ^ i) • ((γ₁⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ _
      rw [hsc]
      exact mul_mem_localBox hRo w (hloc w hw).2 (hri w hw _)
  · change QuaternionAlgebra.nrd (((r : ℚ) ^ (-i)) • (γ₁ : ℍ[ℚ, a, b])) = r
    rw [nrd_smul', hj, hi, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hr0]
    norm_num
    rw [show (-(i * 2) + (2 * i + 1) : ℤ) = 1 by ring, zpow_one]

end Main

end R1AwayNrd

end

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ w : (ℍ[ℚ, a₁, b₁])ˣ, w ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v ∧ nrd (w : ℍ[ℚ, a₁, b₁]) = (r : ℚ) :=
  R1AwayNrd.main Fact.out hdef hR₁ Fact.out hrr.symm v hv

end S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder (solution)
