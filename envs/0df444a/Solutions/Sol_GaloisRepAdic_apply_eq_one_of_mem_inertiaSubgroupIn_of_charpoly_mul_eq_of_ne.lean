-- Prove2me | solution 1 for GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e2d4258a-d7b5-5129-a91d-6b9820207799

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_frobConj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne
p2m_attr_erase "instance" "GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra"
p2m_attr_erase "simp" "GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec"

set_option autoImplicit false

open IsLocalRing Polynomial

noncomputable section

namespace InertiaRigidity

section TwoByTwo

variable {K : Type} [Field K]

theorem mul_self_fin_two (A : Matrix (Fin 2) (Fin 2) K) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem det_one_add_fin_two (U : Matrix (Fin 2) (Fin 2) K) :
    (1 + U).det = 1 + U.trace + U.det := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  ring

theorem exists_mul_of_trace_mul_eq_zero (a b c d a' b' c' d' : K)
    (hu : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0))
    (htu : a + d = 0) (hdu : a * d - b * c = 0) (htv : a' + d' = 0) (hdv : a' * d' - b' * c' = 0)
    (huv : a * a' + b * c' + (c * b' + d * d') = 0) :
    ∃ e : K, a' = e * a ∧ b' = e * b ∧ c' = e * c ∧ d' = e * d := by
  have h1 : b * c = -a ^ 2 := by linear_combination -hdu + a * htu
  have h2 : b' * c' = -a' ^ 2 := by linear_combination -hdv + a' * htv
  have h3 : 2 * (a * a') + b * c' + c * b' = 0 := by
    linear_combination huv - d * htv + a' * htu
  by_cases hb : b = 0
  ·
    have ha : a = 0 := by
      have : a ^ 2 = 0 := by linear_combination h1 - c * hb
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hd : d = 0 := by linear_combination htu - ha
    have hc : c ≠ 0 := fun hc => hu ⟨ha, hb, hc, hd⟩
    have hb' : b' = 0 := by
      have : c * b' = 0 := by linear_combination h3 - (2 * a') * ha - c' * hb
      exact (mul_eq_zero.mp this).resolve_left hc
    have ha' : a' = 0 := by
      have : a' ^ 2 = 0 := by linear_combination h2 - c' * hb'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hd' : d' = 0 := by linear_combination htv - ha'
    refine ⟨c' / c, ?_, ?_, ?_, ?_⟩
    · rw [ha, ha', mul_zero]
    · rw [hb, hb', mul_zero]
    · exact (div_mul_cancel₀ c' hc).symm
    · rw [hd, hd', mul_zero]
  ·
    have hX : (b * a' - a * b') ^ 2 = 0 := by
      linear_combination (-(b * b')) * h3 + b ^ 2 * h2 + b' ^ 2 * h1
    have hX0 : b * a' - a * b' = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hX
    have hcc : b * c' = b' * c := by
      have : b * (b * c') = b * (b' * c) := by
        linear_combination b * h3 + (-2 * a) * hX0 + (-2 * b') * h1
      exact mul_left_cancel₀ hb this
    refine ⟨b' / b, ?_, ?_, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, eq_div_iff hb]
      linear_combination hX0
    · exact (div_mul_cancel₀ b' hb).symm
    · rw [div_mul_eq_mul_div, eq_div_iff hb]
      linear_combination hcc
    · rw [div_mul_eq_mul_div, eq_div_iff hb]
      linear_combination b * htv - b' * htu - hX0

theorem exists_smul_of_trace_mul_eq_zero {u v : Matrix (Fin 2) (Fin 2) K} (hu : u ≠ 0)
    (htu : u.trace = 0) (hdu : u.det = 0) (htv : v.trace = 0) (hdv : v.det = 0)
    (huv : (u * v).trace = 0) : ∃ e : K, v = e • u := by
  have hu' : ¬ (u 0 0 = 0 ∧ u 0 1 = 0 ∧ u 1 0 = 0 ∧ u 1 1 = 0) := by
    rintro ⟨h1, h2, h3, h4⟩
    apply hu
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]
  rw [Matrix.trace_fin_two] at htu htv huv
  rw [Matrix.det_fin_two] at hdu hdv
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at huv
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_mul_of_trace_mul_eq_zero (u 0 0) (u 0 1) (u 1 0) (u 1 1)
    (v 0 0) (v 0 1) (v 1 0) (v 1 1) hu' htu hdu htv hdv huv
  refine ⟨e, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem trace_sq_rel {T u : Matrix (Fin 2) (Fin 2) K} {q : K} (hu : u ≠ 0)
    (hdet : T.det ≠ 0) (hq1 : (1 : K) - q ≠ 0) (h : T * u = q • (u * T)) :
    q * T.trace ^ 2 = (q + 1) ^ 2 * T.det := by
  set s := T.trace with hs
  set δ := T.det with hδ
  have CH : T * T = s • T - δ • (1 : Matrix (Fin 2) (Fin 2) K) := mul_self_fin_two T

  have L1 : T * T * u = (q * q) • (u * T * T) := by
    calc T * T * u = T * (T * u) := by rw [Matrix.mul_assoc]
      _ = T * (q • (u * T)) := by rw [h]
      _ = q • (T * u * T) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = q • ((q • (u * T)) * T) := by rw [h]
      _ = (q * q) • (u * T * T) := by rw [Matrix.smul_mul, smul_smul]

  have L2 : T * T * u = (s * q) • (u * T) - δ • u := by
    rw [CH, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, h, smul_smul]
  have L3 : u * T * T = s • (u * T) - δ • u := by
    rw [Matrix.mul_assoc, CH, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
  have E1 : (s * q) • (u * T) - δ • u = (q * q) • (s • (u * T) - δ • u) := by
    rw [← L2, L1, L3]

  have eqC : (q * s) • (u * T) = ((1 + q) * δ) • u := by
    have h0 : (1 - q) • ((q * s) • (u * T) - ((1 + q) * δ) • u) = 0 := by
      have E1' : (s * q) • (u * T) - δ • u - (q * q) • (s • (u * T) - δ • u) = 0 :=
        sub_eq_zero.mpr E1
      calc (1 - q) • ((q * s) • (u * T) - ((1 + q) * δ) • u)
          = (s * q) • (u * T) - δ • u - (q * q) • (s • (u * T) - δ • u) := by module
        _ = 0 := E1'
    rcases smul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 hq1
    · exact sub_eq_zero.mp h0

  have L5 : (q * s) • (u * T * T) = ((1 + q) * δ) • (u * T) := by
    have := congrArg (· * T) eqC
    simpa only [Matrix.smul_mul] using this
  rw [L3] at L5

  have eqCs : (s * (q * s)) • (u * T) = (s * ((1 + q) * δ)) • u := by
    rw [mul_smul, eqC, smul_smul]
  have L6 : ((1 + q) * δ) • (u * T) = (s * δ) • u := by
    rw [← L5]
    have : (q * s) • (s • (u * T) - δ • u) = (s * (q * s)) • (u * T) - (q * s * δ) • u := by module
    rw [this, eqCs]
    module

  have eqD : (1 + q) • (u * T) = s • u := by
    have h0 : δ • ((1 + q) • (u * T) - s • u) = 0 := by
      have : δ • ((1 + q) • (u * T) - s • u) = ((1 + q) * δ) • (u * T) - (s * δ) • u := by module
      rw [this, L6, sub_self]
    rcases smul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 hdet
    · exact sub_eq_zero.mp h0

  have hfin : (q * s ^ 2 - (q + 1) ^ 2 * δ) • u = 0 := by
    have h1 : (q * s) • ((1 + q) • (u * T)) = (q * s) • (s • u) := by rw [eqD]
    have h2 : (q * s) • ((1 + q) • (u * T)) = (1 + q) • ((q * s) • (u * T)) := by module
    rw [h2, eqC] at h1
    have : (q * s ^ 2 - (q + 1) ^ 2 * δ) • u = (q * s) • (s • u) - (1 + q) • (((1 + q) * δ) • u) := by
      module
    rw [this, h1, sub_self]
  rcases smul_eq_zero.mp hfin with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hu

end TwoByTwo

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O]

theorem main_aux (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ρ : GaloisRepAdic O) {p : ℕ} (hp : p.Prime) (hpO : (p : O) ∈ maximalIdeal O)
    {q : ℕ} (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hcp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ.ρ (σ * g)) = LinearMap.charpoly (ρ.ρ g))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : P.IsFrobeniusAt τ q)
    (hne : (q : O) * LinearMap.trace O ρ.V (ρ.ρ τ) ^ 2 ≠ ((q : O) + 1) ^ 2 * LinearMap.det (ρ.ρ τ)) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1 := by
  classical
  set I := P.inertiaSubgroupIn ℚ with hIdef

  let alg : O →+* K := algebraMap O K
  have halg : Function.Injective alg := IsFractionRing.injective O K
  haveI : CharZero K := charZero_of_injective_algebraMap halg
  let bO := Module.finBasisOfFinrankEq O ρ.V ρ.finrank_eq
  let M : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Matrix (Fin 2) (Fin 2) O :=
    fun g => LinearMap.toMatrix bO bO (ρ.ρ g)
  let mapM : Matrix (Fin 2) (Fin 2) O →+* Matrix (Fin 2) (Fin 2) K := alg.mapMatrix
  have hmapM : Function.Injective mapM := fun A B h =>
    Matrix.map_injective halg (by simpa [mapM, RingHom.mapMatrix_apply] using h)
  let Mk : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Matrix (Fin 2) (Fin 2) K :=
    fun g => mapM (M g)
  have M_mul : ∀ g h, M (g * h) = M g * M h := fun g h => by
    simp only [M, map_mul, LinearMap.toMatrix_mul]
  have M_one : M 1 = 1 := by simp only [M, map_one, LinearMap.toMatrix_one]
  have Mk_mul : ∀ g h, Mk (g * h) = Mk g * Mk h := fun g h => by
    simp only [Mk, M_mul, map_mul]
  have Mk_one : Mk 1 = 1 := by simp only [Mk, M_one, map_one]
  have Mk_sub_one : ∀ g, Mk g - 1 = mapM (M g - 1) := fun g => by
    simp only [Mk, map_sub, map_one]

  have hcpK : ∀ σ ∈ I, ∀ g, (Mk (σ * g)).charpoly = (Mk g).charpoly := by
    intro σ hσ g
    simp only [Mk, mapM, RingHom.mapMatrix_apply, Matrix.charpoly_map, M,
      LinearMap.charpoly_toMatrix, hcp σ hσ g]
  have htr : ∀ σ ∈ I, ∀ g, (Mk (σ * g)).trace = (Mk g).trace := by
    intro σ hσ g
    rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hcpK σ hσ g]
  have hdet : ∀ σ ∈ I, ∀ g, (Mk (σ * g)).det = (Mk g).det := by
    intro σ hσ g
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, hcpK σ hσ g]
  have hU_tr : ∀ σ ∈ I, (Mk σ - 1).trace = 0 := by
    intro σ hσ
    have h := htr σ hσ 1
    rw [mul_one, Mk_one] at h
    rw [Matrix.trace_sub, h, sub_self]
  have hU_det : ∀ σ ∈ I, (Mk σ - 1).det = 0 := by
    intro σ hσ
    have h1 := hdet σ hσ 1
    rw [mul_one, Mk_one, Matrix.det_one] at h1
    have h2 := det_one_add_fin_two (Mk σ - 1)
    rw [add_sub_cancel, h1, hU_tr σ hσ, add_zero] at h2
    linear_combination -h2
  have hU_sq : ∀ σ ∈ I, (Mk σ - 1) * (Mk σ - 1) = 0 := by
    intro σ hσ
    rw [mul_self_fin_two, hU_tr σ hσ, hU_det σ hσ, zero_smul, zero_smul, sub_zero]
  have hU_trmul : ∀ σ ∈ I, ∀ g, ((Mk σ - 1) * Mk g).trace = 0 := by
    intro σ hσ g
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, ← Mk_mul, htr σ hσ g, sub_self]
  have hU_trUU : ∀ σ ∈ I, ∀ σ' ∈ I, ((Mk σ - 1) * (Mk σ' - 1)).trace = 0 := by
    intro σ hσ σ' hσ'
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, hU_trmul σ hσ σ', hU_tr σ hσ, sub_zero]

  by_contra hcon
  push Not at hcon
  obtain ⟨σ₀, hσ₀, hσ₀ne⟩ := hcon
  set U₀ := Mk σ₀ - 1 with hU₀def
  have hU₀ : U₀ ≠ 0 := by
    intro h0
    apply hσ₀ne
    have hM : M σ₀ = 1 := by
      apply hmapM
      rw [map_one]
      exact sub_eq_zero.mp h0
    exact (LinearMap.toMatrix bO bO).injective (hM.trans (LinearMap.toMatrix_one bO).symm)

  have hc_ex : ∀ σ, σ ∈ I → ∃ e : K, Mk σ - 1 = e • U₀ := fun σ hσ =>
    exists_smul_of_trace_mul_eq_zero hU₀ (hU_tr σ₀ hσ₀) (hU_det σ₀ hσ₀) (hU_tr σ hσ)
      (hU_det σ hσ) (hU_trUU σ₀ hσ₀ σ hσ)
  choose! c hc using hc_ex
  have hc_mul : ∀ σ ∈ I, ∀ σ' ∈ I, c (σ * σ') = c σ + c σ' := by
    intro σ hσ σ' hσ'
    have hprod : Mk (σ * σ') - 1 = (c σ + c σ') • U₀ := by
      have e1 : Mk (σ * σ') - 1 = (Mk σ - 1) + (Mk σ' - 1) + (Mk σ - 1) * (Mk σ' - 1) := by
        rw [Mk_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
        abel
      rw [e1, hc σ hσ, hc σ' hσ', smul_mul_smul_comm, hU₀def, hU_sq σ₀ hσ₀, smul_zero, add_zero,
        add_smul]
    exact smul_left_injective K hU₀ ((hc _ (I.mul_mem hσ hσ')).symm.trans hprod)
  have hc_one : c 1 = 0 := by
    have h := hc 1 I.one_mem
    rw [Mk_one, sub_self] at h
    exact ((smul_eq_zero.mp h.symm).resolve_right hU₀)
  have hc_pow : ∀ σ ∈ I, ∀ n : ℕ, c (σ ^ n) = n * c σ := by
    intro σ hσ n
    induction n with
    | zero => rw [pow_zero, hc_one, Nat.cast_zero, zero_mul]
    | succ n ih =>
      rw [pow_succ, hc_mul _ (I.pow_mem hσ n) _ hσ, ih]
      push_cast
      ring
  have hc_σ₀ : c σ₀ = 1 := by
    have h := hc σ₀ hσ₀
    rw [← hU₀def] at h
    have h' : (1 : K) • U₀ = c σ₀ • U₀ := by rw [one_smul]; exact h
    exact (smul_left_injective K hU₀ h').symm

  have htame : ∀ n : ℕ, ∃ w ∈ I, τ * σ₀ * τ⁻¹ = w ^ (p ^ n) * σ₀ ^ q := by
    intro n

    obtain ⟨w, hw, hweq⟩ : ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        w ∈ I ∧ w ^ (p ^ n) = τ * σ₀ * τ⁻¹ * (σ₀ ^ q)⁻¹ := by
      obtain ⟨w, hw, hweq⟩ :=
        ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_frobConj hp hq hpq P hP τ hτ n σ₀ hσ₀
      exact ⟨w, hw, hweq⟩
    refine ⟨w, hw, ?_⟩
    have h1 : τ * σ₀ * τ⁻¹ = τ * σ₀ * τ⁻¹ * (σ₀ ^ q)⁻¹ * σ₀ ^ q := by group
    rw [h1, ← hweq]
  have hconjI : τ * σ₀ * τ⁻¹ ∈ I := by
    obtain ⟨w, hw, hweq⟩ := htame 0
    rw [hweq]
    exact I.mul_mem (I.pow_mem hw _) (I.pow_mem hσ₀ _)
  set r := c (τ * σ₀ * τ⁻¹) with hrdef
  have hr_n : ∀ n : ℕ, ∃ w ∈ I, r = (p : K) ^ n * c w + q := by
    intro n
    obtain ⟨w, hw, hweq⟩ := htame n
    refine ⟨w, hw, ?_⟩
    rw [hrdef, hweq, hc_mul _ (I.pow_mem hw _) _ (I.pow_mem hσ₀ _), hc_pow w hw, hc_pow σ₀ hσ₀,
      hc_σ₀]
    push_cast
    ring

  obtain ⟨j, k, hjk⟩ : ∃ j k, (M σ₀ - 1) j k ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hU₀
    have h0 : M σ₀ - 1 = 0 := by ext j k; exact hall j k
    rw [hU₀def, Mk_sub_one, h0, map_zero]
  have hcint : ∀ w ∈ I, alg ((M w - 1) j k) = c w * alg ((M σ₀ - 1) j k) := by
    intro w hw
    have h := congrFun (congrFun (hc w hw) j) k
    rw [Mk_sub_one, hU₀def, Mk_sub_one] at h
    simpa [mapM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply]
      using h

  obtain ⟨r₁, r₂, hr₂, hr12⟩ := IsFractionRing.div_surjective (A := O) r
  have hr₂0 : r₂ ≠ 0 := nonZeroDivisors.ne_zero hr₂
  have halgr₂ : alg r₂ ≠ 0 := (map_ne_zero_iff alg halg).mpr hr₂0
  have he : alg (r₁ - q * r₂) = alg r₂ * (r - q) := by
    rw [map_sub, map_mul, map_natCast, ← hr12, mul_sub, mul_comm (alg r₂) (alg r₁ / alg r₂),
      div_mul_cancel₀ (alg r₁) halgr₂]
    ring
  have hed : ∀ n : ℕ, (r₁ - q * r₂) * (M σ₀ - 1) j k ∈ maximalIdeal O ^ n := by
    intro n
    obtain ⟨w, hw, hrw⟩ := hr_n n
    have key : alg ((r₁ - q * r₂) * (M σ₀ - 1) j k) = alg (p ^ n * (r₂ * (M w - 1) j k)) := by
      rw [map_mul, map_mul, map_mul, hcint w hw, map_pow, map_natCast, he, hrw]
      ring
    rw [halg key]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpO n)
  have hed0 : (r₁ - q * r₂) * (M σ₀ - 1) j k = 0 := by
    have hmem : (r₁ - q * r₂) * (M σ₀ - 1) j k ∈ (⨅ n : ℕ, maximalIdeal O ^ n) :=
      Ideal.mem_iInf.mpr hed
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top,
      Ideal.mem_bot] at hmem
  have he0 : r₁ - q * r₂ = 0 := (mul_eq_zero.mp hed0).resolve_right hjk
  have hrq : r = q := by
    have h1 : r₁ = q * r₂ := sub_eq_zero.mp he0
    rw [← hr12, h1, map_mul, map_natCast, mul_div_assoc, div_self halgr₂, mul_one]

  have hconj : Mk τ * U₀ * Mk τ⁻¹ = r • U₀ := by
    rw [hrdef, ← hc _ hconjI, Mk_mul, Mk_mul, hU₀def, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      ← Mk_mul τ τ⁻¹, mul_inv_cancel, Mk_one]
  have hTU : Mk τ * U₀ = (q : K) • (U₀ * Mk τ) := by
    have h := congrArg (· * Mk τ) hconj
    rwa [Matrix.mul_assoc (Mk τ * U₀), ← Mk_mul, inv_mul_cancel, Mk_one, Matrix.mul_one, hrq,
      Matrix.smul_mul] at h
  have hdetT : (Mk τ).det ≠ 0 := by
    intro h0
    have h : (Mk τ * Mk τ⁻¹).det = 1 := by rw [← Mk_mul, mul_inv_cancel, Mk_one, Matrix.det_one]
    rw [Matrix.det_mul, h0, zero_mul] at h
    exact zero_ne_one h
  have hq1 : (1 : K) - q ≠ 0 := by
    have h : (q : K) ≠ 1 := by exact_mod_cast hq.one_lt.ne'
    exact sub_ne_zero.mpr h.symm
  have key := trace_sq_rel hU₀ hdetT hq1 hTU

  have htrT : (Mk τ).trace = alg (LinearMap.trace O ρ.V (ρ.ρ τ)) := by
    rw [LinearMap.trace_eq_matrix_trace O bO, AddMonoidHom.map_trace alg]
    rfl
  have hdetT' : (Mk τ).det = alg (LinearMap.det (ρ.ρ τ)) := by
    rw [← LinearMap.det_toMatrix bO, RingHom.map_det]
  rw [htrT, hdetT'] at key
  apply hne
  apply halg
  rw [map_mul, map_mul, map_pow, map_pow, map_add, map_natCast, map_one]
  exact key

theorem main (ρ : GaloisRepAdic O) {p : ℕ} (hp : p.Prime) (hpO : (p : O) ∈ maximalIdeal O)
    {q : ℕ} (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hcp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ.ρ (σ * g)) = LinearMap.charpoly (ρ.ρ g))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : P.IsFrobeniusAt τ q)
    (hne : (q : O) * LinearMap.trace O ρ.V (ρ.ρ τ) ^ 2 ≠ ((q : O) + 1) ^ 2 * LinearMap.det (ρ.ρ τ)) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1 :=
  main_aux (FractionRing O) ρ hp hpO hq hpq P hP hcp hτ hne

end Main

end InertiaRigidity

end

theorem solution
    {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O]
    (ρ : GaloisRepAdic O) {p : ℕ} (hp : p.Prime) (hpO : (p : O) ∈ maximalIdeal O)
    {q : ℕ} (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hcp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ.ρ (σ * g)) = LinearMap.charpoly (ρ.ρ g))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : P.IsFrobeniusAt τ q)
    (hne : (q : O) * LinearMap.trace O ρ.V (ρ.ρ τ) ^ 2 ≠ ((q : O) + 1) ^ 2 * LinearMap.det (ρ.ρ τ)) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1 :=
  InertiaRigidity.main ρ hp hpO hq hpq P hP hcp hτ hne

end S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne
end P2MW
export P2MW.S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne (solution)
