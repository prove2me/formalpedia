-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.finiteIndex_subgroupOf_inf_map_conj_awayUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/50c820df-7442-5ee3-b7cd-eb011ff0fca6

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_finiteIndex_subgroupOf_inf_map_conj_awayUnits

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

namespace R1AwayCong

section Places

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

theorem primesEquiv_place (q : ℕ) (hq : q.Prime) :
    Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) (place q hq) = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place (q : ℕ) (hq : q.Prime) :
    Rat.HeightOneSpectrum.natGenerator (place q hq) = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_eq_of_prime_mem {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : Rat.HeightOneSpectrum.natGenerator v = p :=
  (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).1
    ((natCast_mem_asIdeal_iff v p).1 hv)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) c) = w.valuation ℚ c := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w c

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : v.adicCompletion ℚ}
    (hc : c ∈ v.adicCompletionIntegers ℚ) : z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {z : D} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
  tmul_mem_localBox Λ v hz (one_mem _)

theorem mul_mem_localBox (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {x y : D ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v)
    (hy : y ∈ Submodule.localBox Λ v) : x * y ∈ Submodule.localBox Λ v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox Λ v (hmul _ _ hz' hz) (mul_mem hc' hc)
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | neg x _ hx => exact (neg_mul x _).symm ▸ neg_mem hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add x' y' _ _ hx' hy' => rw [mul_add]; exact add_mem hx' hy'
  | neg x' _ hx' => exact (mul_neg _ x').symm ▸ neg_mem hx'

end Box

section Coset

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

def boxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup (CosetGraph.Loc a b w)ˣ where
  carrier := Submodule.localBoxUnits Λ w
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one, Algebra.TensorProduct.one_def]
      exact tmul_one_mem_localBox Λ w hΛ.one_mem
    · rw [inv_one, Units.val_one, Algebra.TensorProduct.one_def]
      exact tmul_one_mem_localBox Λ w hΛ.one_mem
  mul_mem' {x y} hx hy := by
    have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ := fun x y hx hy => hΛ.mul_mem hx hy
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact mul_mem_localBox Λ w hmul hx.1 hy.1
    · rw [mul_inv_rev, Units.val_mul]; exact mul_mem_localBox Λ w hmul hy.2 hx.2
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem mem_boxUnits_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    (u : (CosetGraph.Loc a b w)ˣ) :
    u ∈ boxUnits hΛ w ↔ (u : CosetGraph.Loc a b w) ∈ Submodule.localBox Λ w ∧
      ((u⁻¹ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox Λ w :=
  Iff.rfl

theorem closure_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup.closure (Submodule.localBoxUnits Λ w) = boxUnits hΛ w :=
  (boxUnits hΛ w).closure_eq

theorem coe_toLoc (w : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) :
    ((CosetGraph.toLoc w γ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) =
      (γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) :=
  rfl

theorem tmul_one_mem_localBox_of_mem_awayUnits {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    {v : HeightOneSpectrum (𝓞 ℚ)} {γ : (ℍ[ℚ, a, b])ˣ} (hγ : γ ∈ CosetGraph.awayUnits R v)
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    (γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w := by
  have h : CosetGraph.toLoc w γ ∈ Subgroup.closure (Submodule.localBoxUnits R w) := by
    have h1 := Subgroup.mem_iInf.1 hγ w
    exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 hw)
  rw [closure_localBoxUnits hR w, mem_boxUnits_iff] at h
  rw [← coe_toLoc]
  exact h.1

end Coset

section Coordinates

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

def extendScalar (w : HeightOneSpectrum (𝓞 ℚ)) (φ : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ) :
    ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ →ₗ[ℚ] w.adicCompletion ℚ :=
  (TensorProduct.lid ℚ (w.adicCompletion ℚ)).toLinearMap ∘ₗ φ.rTensor (w.adicCompletion ℚ)

theorem extendScalar_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (φ : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ) (x : ℍ[ℚ, a, b])
    (y : w.adicCompletion ℚ) : extendScalar w φ (x ⊗ₜ[ℚ] y) = φ x • y := by
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
    ∃ n : ℕ, ¬ Rat.HeightOneSpectrum.natGenerator w ∣ n ∧ (n : ℚ) • x ∈ R := by
  have hden : ∀ i, ¬ Rat.HeightOneSpectrum.natGenerator w ∣ (B.repr x i).den := by
    intro i hdvd
    have hint := extendScalar_coord_mem_integers B hBR w i hx
    rw [extendScalar_tmul, Module.Basis.coord_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      Algebra.smul_def, mul_one, valued_algebraMap, Rat.valuation_le_one_iff_den] at hint
    exact hint ((natCast_mem_asIdeal_iff w _).2 hdvd)
  refine ⟨∏ i, (B.repr x i).den, ?_, ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ :=
      (Prime.dvd_finsetProd_iff (Rat.HeightOneSpectrum.prime_natGenerator w).prime _).1 h
    exact hden i hi
  · rw [← hBR, Module.Basis.mem_span_iff_repr_mem]
    intro i
    refine ⟨(∏ j ∈ Finset.univ.erase i, ((B.repr x j).den : ℤ)) * (B.repr x i).num, ?_⟩
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
      Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num]
    simp

end Coordinates

section LocalGlobal

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

theorem exists_pow_smul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) {x : ℍ[ℚ, a, b]}
    (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      x ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w) :
    ∃ k : ℕ, ((r ^ k : ℕ) : ℚ) • x ∈ R := by
  obtain ⟨B, -, hBR⟩ := hR.exists_basis_span_eq
  have hgen : Rat.HeightOneSpectrum.natGenerator v = r := natGenerator_eq_of_prime_mem hr v hv

  have step : ∀ q : ℕ, q.Prime → q ≠ r → ∃ n : ℕ, ¬ q ∣ n ∧ (n : ℚ) • x ∈ R := by
    intro q hq hqr
    have hw : place q hq ≠ v := by
      intro h; apply hqr; rw [← natGenerator_place q hq, h, hgen]
    obtain ⟨n, hn, hnx⟩ :=
      exists_natCast_smul_mem_of_tmul_one_mem_localBox B hBR (place q hq) (hx _ hw)
    rw [natGenerator_place] at hn
    exact ⟨n, hn, hnx⟩

  let I : Ideal ℤ := R.comap (LinearMap.toSpanSingleton ℤ ℍ[ℚ, a, b] x)
  have hI : ∀ n : ℤ, n ∈ I ↔ (n : ℚ) • x ∈ R := by
    intro n
    simp only [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Int.cast_smul_eq_zsmul ℚ]
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = Submodule.IsPrincipal.generator I := ⟨_, rfl⟩
  have hdI : d ∈ I := hd ▸ Submodule.IsPrincipal.generator_mem I
  have hdvd : ∀ n : ℤ, n ∈ I → d ∣ n := fun n hn =>
    hd ▸ (Submodule.IsPrincipal.mem_iff_generator_dvd I).1 hn
  have hprime : ∀ {q : ℕ}, q.Prime → q ∣ d.natAbs → q = r := by
    intro q hq hqd
    by_contra hqr
    obtain ⟨n, hn, hnx⟩ := step q hq hqr
    apply hn
    have h1 : d ∣ (n : ℤ) := hdvd n ((hI n).2 (by exact_mod_cast hnx))
    have h2 : (q : ℤ) ∣ (n : ℤ) := (Int.natCast_dvd.2 hqd).trans h1
    exact Int.natCast_dvd_natCast.1 h2
  have hd0 : d.natAbs ≠ 0 := by
    obtain ⟨q, hq, hqr⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ r := by
      by_cases h : r = 2
      · exact ⟨3, Nat.prime_three, by omega⟩
      · exact ⟨2, Nat.prime_two, fun e => h e.symm⟩
    obtain ⟨n, hn, hnx⟩ := step q hq hqr
    intro hd0
    have h1 : d ∣ (n : ℤ) := hdvd n ((hI n).2 (by exact_mod_cast hnx))
    rw [Int.natAbs_eq_zero.1 hd0, zero_dvd_iff, Int.natCast_eq_zero] at h1
    exact hn (h1 ▸ dvd_zero q)
  refine ⟨d.natAbs.primeFactorsList.length, ?_⟩
  rw [← Nat.eq_prime_pow_of_unique_prime_dvd hd0 hprime]
  have hmem : ((d.natAbs : ℤ) : ℚ) • x ∈ R := by
    rw [← hI]
    rcases Int.natAbs_eq d with h | h
    · rw [← h]; exact hdI
    · have : (d.natAbs : ℤ) = -d := by omega
      rw [this]; exact I.neg_mem hdI
  exact_mod_cast hmem

end LocalGlobal

section Away

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

theorem natCast_smul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ[ℚ, a, b]} (hx : x ∈ R) (n : ℕ) :
    (n : ℚ) • x ∈ R := by
  rw [Nat.cast_smul_eq_nsmul]; exact R.nsmul_mem hx n

def awayRing {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (r : ℕ) : Subring ℍ[ℚ, a, b] where
  carrier := {x | ∃ k : ℕ, ((r ^ k : ℕ) : ℚ) • x ∈ R}
  mul_mem' := by
    rintro x y ⟨k, hk⟩ ⟨m, hm⟩
    refine ⟨k + m, ?_⟩
    have : ((r ^ (k + m) : ℕ) : ℚ) • (x * y) =
        (((r ^ k : ℕ) : ℚ) • x) * (((r ^ m : ℕ) : ℚ) • y) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_add, Nat.cast_mul]
    rw [this]; exact hR.mul_mem hk hm
  one_mem' := ⟨0, by rw [pow_zero, Nat.cast_one, one_smul]; exact hR.one_mem⟩
  add_mem' := by
    rintro x y ⟨k, hk⟩ ⟨m, hm⟩
    refine ⟨k + m, ?_⟩
    rw [smul_add]
    refine R.add_mem ?_ ?_
    · rw [pow_add, Nat.cast_mul, mul_comm, mul_smul]; exact natCast_smul_mem hk _
    · rw [pow_add, Nat.cast_mul, mul_smul]; exact natCast_smul_mem hm _
  zero_mem' := ⟨0, by rw [smul_zero]; exact R.zero_mem⟩
  neg_mem' := by
    rintro x ⟨k, hk⟩
    exact ⟨k, by rw [smul_neg]; exact R.neg_mem hk⟩

theorem mem_awayRing_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (r : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ awayRing hR r ↔ ∃ k : ℕ, ((r ^ k : ℕ) : ℚ) • x ∈ R :=
  Iff.rfl

theorem mem_awayRing_of_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (r : ℕ) {x : ℍ[ℚ, a, b]}
    (hx : x ∈ R) : x ∈ awayRing hR r :=
  ⟨0, by rw [pow_zero, Nat.cast_one, one_smul]; exact hx⟩

theorem coe_mem_awayRing {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) {γ : (ℍ[ℚ, a, b])ˣ}
    (hγ : γ ∈ CosetGraph.awayUnits R v) : (γ : ℍ[ℚ, a, b]) ∈ awayRing hR r :=
  exists_pow_smul_mem hR hr v hv fun w hw => tmul_one_mem_localBox_of_mem_awayUnits hR hγ hw

def toAway {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) :
    CosetGraph.awayUnits R v →* (awayRing hR r)ˣ where
  toFun γ :=
    { val := ⟨((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), coe_mem_awayRing hR hr v hv γ.2⟩
      inv := ⟨((γ⁻¹ : CosetGraph.awayUnits R v) : (ℍ[ℚ, a, b])ˣ), coe_mem_awayRing hR hr v hv (γ⁻¹).2⟩
      val_inv := Subtype.ext (by simp)
      inv_val := Subtype.ext (by simp) }
  map_one' := Units.ext (Subtype.ext rfl)
  map_mul' x y := Units.ext (Subtype.ext rfl)

theorem coe_toAway {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) (γ : CosetGraph.awayUnits R v) :
    (((toAway hR hr v hv γ : (awayRing hR r)ˣ) : awayRing hR r) : ℍ[ℚ, a, b]) =
      ((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) :=
  rfl

abbrev ellIdeal (A : Type*) [Ring A] (ℓ : ℕ) : Ideal A := Ideal.span {(ℓ : A)}

scoped instance ellIdeal_isTwoSided (A : Type*) [Ring A] (ℓ : ℕ) : (ellIdeal A ℓ).IsTwoSided := by
  refine ⟨fun b ha => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  refine Ideal.mem_span_singleton'.2 ⟨c * b, ?_⟩
  rw [mul_assoc, mul_assoc, (Nat.cast_commute ℓ b).eq]

theorem finite_quotient {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r) :
    Finite (awayRing hR r ⧸ ellIdeal (awayRing hR r) ℓ) := by
  haveI : Module.Finite ℤ R := Module.Finite.iff_fg.2 hR.fg
  haveI : AddGroup.FG R := Module.Finite.iff_addGroup_fg.1 inferInstance

  let ι : R →+ awayRing hR r :=
    { toFun := fun z => ⟨(z : ℍ[ℚ, a, b]), mem_awayRing_of_mem hR r z.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk (ellIdeal (awayRing hR r) ℓ)).toAddMonoidHom.comp ι) := by
    intro qq
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective qq
    obtain ⟨k, hk⟩ := y.2
    have hcop : Nat.Coprime (r ^ k) ℓ :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hr hℓ).2 hℓr.symm)
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have hzR : (u : ℚ) • ((((r ^ k : ℕ) : ℚ)) • (y : ℍ[ℚ, a, b])) ∈ R := by
      rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hk u
    have hcA : ((-w : ℤ) : ℚ) • (y : ℍ[ℚ, a, b]) ∈ awayRing hR r := by
      refine ⟨k, ?_⟩
      rw [smul_comm, Int.cast_smul_eq_zsmul]
      exact zsmul_mem hk (-w)
    refine ⟨⟨_, hzR⟩, ?_⟩
    change Ideal.Quotient.mk _ (ι ⟨_, hzR⟩) = Ideal.Quotient.mk _ y
    rw [Ideal.Quotient.eq]
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, hcA⟩, ?_⟩
    apply Subtype.ext
    change (((-w : ℤ) : ℚ) • (y : ℍ[ℚ, a, b])) * ((ℓ : awayRing hR r) : ℍ[ℚ, a, b]) =
      (u : ℚ) • ((((r ^ k : ℕ) : ℚ)) • (y : ℍ[ℚ, a, b])) - (y : ℍ[ℚ, a, b])
    have key : ((-w : ℤ) : ℚ) * (ℓ : ℚ) = (u : ℚ) * ((r ^ k : ℕ) : ℚ) - 1 := by
      have := congrArg (Int.cast (R := ℚ)) huw
      push_cast at this ⊢
      linarith
    have hℓy : (((-w : ℤ) : ℚ) • (y : ℍ[ℚ, a, b])) * ((ℓ : awayRing hR r) : ℍ[ℚ, a, b]) =
        (((-w : ℤ) : ℚ) * (ℓ : ℚ)) • (y : ℍ[ℚ, a, b]) := by
      rw [Subring.coe_natCast, mul_smul, smul_mul_assoc]
      congr 1
      rw [← map_natCast (algebraMap ℚ ℍ[ℚ, a, b]) ℓ, ← Algebra.commutes, ← Algebra.smul_def]
    rw [hℓy, key, sub_smul, one_smul, mul_smul]
  haveI : AddGroup.FG (awayRing hR r ⧸ ellIdeal (awayRing hR r) ℓ) := AddGroup.fg_of_surjective hsurj

  have htors : AddMonoid.IsTorsion (awayRing hR r ⧸ ellIdeal (awayRing hR r) ℓ) := by
    intro qq
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective qq
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨ℓ, hℓ.pos, ?_⟩
    rw [← map_nsmul, nsmul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.2 ⟨y, (Nat.cast_commute ℓ y).eq.symm⟩
  exact AddCommGroup.finite_of_fg_torsion _ htors

def reduction {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) (ℓ : ℕ) :
    CosetGraph.awayUnits R v →* (awayRing hR r ⧸ ellIdeal (awayRing hR r) ℓ)ˣ :=
  (Units.map (Ideal.Quotient.mk (ellIdeal (awayRing hR r) ℓ)).toMonoidHom).comp (toAway hR hr v hv)

theorem exists_eq_one_add_smul_of_mem_ker {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ}
    (hr : r.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) (ℓ : ℕ)
    (γ : CosetGraph.awayUnits R v) (hγ : γ ∈ (reduction hR hr v hv ℓ).ker) :
    ∃ (k : ℕ) (y : ℍ[ℚ, a, b]), ((r ^ k : ℕ) : ℚ) • y ∈ R ∧
      (((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1 + (ℓ : ℚ) • y := by
  rw [MonoidHom.mem_ker] at hγ
  have h1 : Ideal.Quotient.mk (ellIdeal (awayRing hR r) ℓ) ((toAway hR hr v hv γ : (awayRing hR r)ˣ) :
      awayRing hR r) = Ideal.Quotient.mk (ellIdeal (awayRing hR r) ℓ) 1 := by
    rw [map_one]
    exact Units.ext_iff.1 hγ
  rw [Ideal.Quotient.eq] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨k, hk⟩ := c.2
  refine ⟨k, (c : ℍ[ℚ, a, b]), hk, ?_⟩
  have h2 := congrArg Subtype.val hc
  rw [Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub, Subring.coe_one, coe_toAway,
    eq_sub_iff_add_eq] at h2
  rw [← h2, add_comm]
  congr 1
  rw [Algebra.smul_def, map_natCast, (Nat.cast_commute ℓ (c : ℍ[ℚ, a, b])).eq]

theorem main {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r) :
    ∃ K : Subgroup ↥(CosetGraph.awayUnits R v), K.Normal ∧ K.FiniteIndex ∧
      ∀ γ : ↥(CosetGraph.awayUnits R v), γ ∈ K →
        ∃ (k : ℕ) (y : ℍ[ℚ, a, b]), ((r ^ k : ℕ) : ℚ) • y ∈ R ∧
          (((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1 + (ℓ : ℚ) • y := by
  haveI := finite_quotient hR hr hℓ hℓr
  refine ⟨(reduction hR hr v hv ℓ).ker, inferInstance, ?_,
    fun γ hγ => exists_eq_one_add_smul_of_mem_ker hR hr v hv ℓ γ hγ⟩
  refine ⟨?_⟩
  rw [Subgroup.index_ker]
  exact Nat.card_pos.ne'

end Away

section Conj

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

theorem finite_quotient' {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    {m : ℕ} (hm : 0 < m) (hmr : ¬ r ∣ m) :
    Finite (awayRing hR r ⧸ ellIdeal (awayRing hR r) m) := by
  haveI : Module.Finite ℤ R := Module.Finite.iff_fg.2 hR.fg
  haveI : AddGroup.FG R := Module.Finite.iff_addGroup_fg.1 inferInstance
  let ι : R →+ awayRing hR r :=
    { toFun := fun z => ⟨(z : ℍ[ℚ, a, b]), mem_awayRing_of_mem hR r z.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk (ellIdeal (awayRing hR r) m)).toAddMonoidHom.comp ι) := by
    intro qq
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective qq
    obtain ⟨k, hk⟩ := y.2
    have hcop : Nat.Coprime (r ^ k) m :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hmr)
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have hzR : (u : ℚ) • ((((r ^ k : ℕ) : ℚ)) • (y : ℍ[ℚ, a, b])) ∈ R := by
      rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hk u
    have hcA : ((-w : ℤ) : ℚ) • (y : ℍ[ℚ, a, b]) ∈ awayRing hR r := by
      refine ⟨k, ?_⟩
      rw [smul_comm, Int.cast_smul_eq_zsmul]
      exact zsmul_mem hk (-w)
    refine ⟨⟨_, hzR⟩, ?_⟩
    change Ideal.Quotient.mk _ (ι ⟨_, hzR⟩) = Ideal.Quotient.mk _ y
    rw [Ideal.Quotient.eq]
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, hcA⟩, ?_⟩
    apply Subtype.ext
    change (((-w : ℤ) : ℚ) • (y : ℍ[ℚ, a, b])) * ((m : awayRing hR r) : ℍ[ℚ, a, b]) =
      (u : ℚ) • ((((r ^ k : ℕ) : ℚ)) • (y : ℍ[ℚ, a, b])) - (y : ℍ[ℚ, a, b])
    have key : ((-w : ℤ) : ℚ) * (m : ℚ) = (u : ℚ) * ((r ^ k : ℕ) : ℚ) - 1 := by
      have := congrArg (Int.cast (R := ℚ)) huw
      push_cast at this ⊢
      linarith
    have hmy : (((-w : ℤ) : ℚ) • (y : ℍ[ℚ, a, b])) * ((m : awayRing hR r) : ℍ[ℚ, a, b]) =
        (((-w : ℤ) : ℚ) * (m : ℚ)) • (y : ℍ[ℚ, a, b]) := by
      rw [Subring.coe_natCast, mul_smul, smul_mul_assoc]
      congr 1
      rw [← map_natCast (algebraMap ℚ ℍ[ℚ, a, b]) m, ← Algebra.commutes, ← Algebra.smul_def]
    rw [hmy, key, sub_smul, one_smul, mul_smul]
  haveI : AddGroup.FG (awayRing hR r ⧸ ellIdeal (awayRing hR r) m) := AddGroup.fg_of_surjective hsurj
  have htors : AddMonoid.IsTorsion (awayRing hR r ⧸ ellIdeal (awayRing hR r) m) := by
    intro qq
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective qq
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨m, hm, ?_⟩
    rw [← map_nsmul, nsmul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.2 ⟨y, (Nat.cast_commute m y).eq.symm⟩
  exact AddCommGroup.finite_of_fg_torsion _ htors

theorem exists_nat_smul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (x : ℍ[ℚ, a, b]) :
    ∃ n : ℕ, 0 < n ∧ (n : ℚ) • x ∈ R := by
  obtain ⟨B, hBmem, -⟩ := hR.exists_basis_span_eq
  set c := B.repr x with hc
  refine ⟨∏ i, (c i).den, Finset.prod_pos (fun i _ => (c i).den_pos), ?_⟩
  rw [← B.sum_repr x, Finset.smul_sum]
  refine R.sum_mem fun i _ => ?_
  rw [smul_smul]
  obtain ⟨e, he⟩ : (c i).den ∣ ∏ j, (c j).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hz : ((∏ j, (c j).den : ℕ) : ℚ) * c i = ((e * (c i).num : ℤ) : ℚ) := by
    rw [he]; push_cast
    have h1 : (c i) * ((c i).den : ℚ) = ((c i).num : ℚ) := Rat.mul_den_eq_num (c i)
    calc (((c i).den : ℚ) * (e : ℚ)) * c i = (e : ℚ) * ((c i) * ((c i).den : ℚ)) := by ring
      _ = (e : ℚ) * ((c i).num : ℚ) := by rw [h1]
  rw [show B.repr x i = c i from rfl, hz, Int.cast_smul_eq_zsmul]
  exact zsmul_mem (hBmem i) _

theorem exists_nat_smul_conj_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (t t' : ℍ[ℚ, a, b]) :
    ∃ M : ℕ, 0 < M ∧ ∀ y ∈ R, (M : ℚ) • (t * y * t') ∈ R := by
  obtain ⟨B, hBmem, hBR⟩ := hR.exists_basis_span_eq
  choose n hn hnR using fun i => exists_nat_smul_mem hR (t * B i * t')
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun y hy => ?_⟩
  rw [← hBR] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨e, he⟩ : n i ∣ ∏ j, n j := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    rw [he, Nat.cast_mul, mul_comm, mul_smul]
    exact natCast_smul_mem (hnR i) e
  | zero => rw [mul_zero, zero_mul, smul_zero]; exact R.zero_mem
  | add x y _ _ hx hy => rw [mul_add, add_mul, smul_add]; exact R.add_mem hx hy
  | smul z x _ hx =>
    rw [mul_smul_comm, smul_mul_assoc, smul_comm]
    exact R.smul_mem z hx

theorem exists_smul_conj_mem_awayRing {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (t t' : ℍ[ℚ, a, b]) :
    ∃ m : ℕ, 0 < m ∧ ¬ r ∣ m ∧ ∀ y ∈ awayRing hR r, (m : ℚ) • (t * y * t') ∈ awayRing hR r := by
  obtain ⟨M, hM, hMR⟩ := exists_nat_smul_conj_mem hR t t'
  obtain ⟨e, m, hmr, hMeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' r hr.one_lt.ne'
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hMeq; exact hM.ne' hMeq
  refine ⟨m, hm, hmr, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := hy
  refine ⟨k + e, ?_⟩
  have h1 := hMR _ hk

  have h2 : (M : ℚ) • (t * ((((r ^ k : ℕ) : ℚ)) • y) * t') =
      ((r ^ (k + e) : ℕ) : ℚ) • ((m : ℚ) • (t * y * t')) := by
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, smul_smul, hMeq]
    congr 1
    push_cast
    ring
  rw [← h2]
  exact h1

theorem natCast_not_mem_of_ne {r : ℕ} (hr : r.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) (hw : w ≠ v) : (r : 𝓞 ℚ) ∉ w.asIdeal := by
  intro h
  apply hw
  have e1 := natGenerator_eq_of_prime_mem hr w h
  have e2 := natGenerator_eq_of_prime_mem hr v hv
  have : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w = Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v :=
    Subtype.ext (e1.trans e2.symm)
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective this

theorem tmul_one_mem_localBox_of_mem_awayRing {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v)
    {y : ℍ[ℚ, a, b]} (hy : y ∈ awayRing hR r) :
    y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w := by
  obtain ⟨k, hk⟩ := hy
  have hr0 : ((r ^ k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (pow_pos hr.pos k).ne'
  have hint : algebraMap ℚ (w.adicCompletion ℚ) (((r ^ k : ℕ) : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, map_inv₀]
    have : w.valuation ℚ ((r : ℕ) : ℚ) = 1 := by
      rw [show ((r : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (r : 𝓞 ℚ) by simp, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_eq_one_iff]
      exact natCast_not_mem_of_ne hr hv hw
    rw [Nat.cast_pow, map_pow, this, one_pow, inv_one]
  have : y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
      (((r ^ k : ℕ) : ℚ) • y) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) (((r ^ k : ℕ) : ℚ)⁻¹)) := by
    rw [TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hr0, map_one]
  rw [this]
  exact tmul_mem_localBox R w hk hint

theorem mem_awayUnits_of_mem_awayRing {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) (x : (ℍ[ℚ, a, b])ˣ)
    (hx : (x : ℍ[ℚ, a, b]) ∈ awayRing hR r) (hx' : ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ awayRing hR r) :
    x ∈ CosetGraph.awayUnits R v := by
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => Subgroup.mem_comap.2 ?_
  rw [closure_localBoxUnits hR w, mem_boxUnits_iff]
  refine ⟨?_, ?_⟩
  · rw [coe_toLoc]; exact tmul_one_mem_localBox_of_mem_awayRing hR hr hv hw hx
  · rw [← map_inv, coe_toLoc]; exact tmul_one_mem_localBox_of_mem_awayRing hR hr hv hw hx'

theorem finiteIndex_conj {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) (s : (ℍ[ℚ, a, b])ˣ) :
    ((CosetGraph.awayUnits R v ⊓ (CosetGraph.awayUnits R v).map (MulAut.conj s).toMonoidHom).subgroupOf
      (CosetGraph.awayUnits R v)).FiniteIndex := by

  obtain ⟨m, hm, hmr, hconj⟩ :=
    exists_smul_conj_mem_awayRing hR hr ((s⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) (s : ℍ[ℚ, a, b])
  haveI := finite_quotient' hR hr hm hmr

  set K := (reduction hR hr v hv m).ker with hK
  haveI hKfi : K.FiniteIndex := by
    refine ⟨?_⟩
    rw [hK, Subgroup.index_ker]
    exact Nat.card_pos.ne'

  refine Subgroup.finiteIndex_of_le (H := K) fun γ hγ => ?_
  rw [Subgroup.mem_subgroupOf]
  refine ⟨γ.2, ?_⟩

  have key : ∀ δ : ↥(CosetGraph.awayUnits R v), δ ∈ K →
      ((s⁻¹ * (δ : (ℍ[ℚ, a, b])ˣ) * s : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ awayRing hR r := by
    intro δ hδ
    obtain ⟨k, y, hy, hδeq⟩ := exists_eq_one_add_smul_of_mem_ker hR hr v hv m δ (hK ▸ hδ)
    have hy' : y ∈ awayRing hR r := ⟨k, hy⟩
    rw [Units.val_mul, Units.val_mul, hδeq, mul_add, add_mul, mul_one, Units.inv_mul, mul_smul_comm, smul_mul_assoc]
    exact (awayRing hR r).add_mem (awayRing hR r).one_mem (hconj y hy')
  have h1 := key γ hγ
  have h2 := key γ⁻¹ (K.inv_mem hγ)
  have hmem : s⁻¹ * (γ : (ℍ[ℚ, a, b])ˣ) * s ∈ CosetGraph.awayUnits R v := by
    refine mem_awayUnits_of_mem_awayRing hR hr v hv _ h1 ?_
    have : (s⁻¹ * (γ : (ℍ[ℚ, a, b])ˣ) * s)⁻¹ = s⁻¹ * ((γ⁻¹ : ↥(CosetGraph.awayUnits R v)) : (ℍ[ℚ, a, b])ˣ) * s := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]; rfl
    rw [this]; exact h2
  refine Subgroup.mem_map.2 ⟨s⁻¹ * (γ : (ℍ[ℚ, a, b])ˣ) * s, hmem, ?_⟩
  show s * (s⁻¹ * (γ : (ℍ[ℚ, a, b])ˣ) * s) * s⁻¹ = (γ : (ℍ[ℚ, a, b])ˣ)
  group

end Conj

end R1AwayCong
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_finiteIndex_subgroupOf_inf_map_conj_awayUnits.R1AwayCong"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_finiteIndex_subgroupOf_inf_map_conj_awayUnits.R1AwayCong"

open QuaternionAlgebra CerednikDrinfeld in
theorem solution
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {r : ℕ} [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (s : (ℍ[ℚ, a, b])ˣ) :
    ((CosetGraph.awayUnits R v ⊓ (CosetGraph.awayUnits R v).map (MulAut.conj s).toMonoidHom).subgroupOf
      (CosetGraph.awayUnits R v)).FiniteIndex :=
  R1AwayCong.finiteIndex_conj hR Fact.out v hv s

end S_CerednikDrinfeld_CosetGraph_finiteIndex_subgroupOf_inf_map_conj_awayUnits
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_finiteIndex_subgroupOf_inf_map_conj_awayUnits (solution)
