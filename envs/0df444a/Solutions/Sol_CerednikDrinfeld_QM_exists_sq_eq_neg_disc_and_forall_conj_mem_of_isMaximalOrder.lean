-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a4cbe201-2f05-574e-9e8b-6e29499c3cd9

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
import Theorems.Thm_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
import Theorems.Thm_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace HSICC

section Places

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem intCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) :
    (z : 𝓞 ℚ) ∈ w.asIdeal ↔ (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣ z := by
  rw [Int.natCast_dvd, ← natCast_mem_asIdeal_iff]
  rcases Int.natAbs_eq z with h | h
  · conv_lhs => rw [h]
    simp
  · conv_lhs => rw [h]
    simp

theorem asIdeal_eq_span_natGenerator (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ)} := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) w
  have h1 : w.asIdeal = (w.asIdeal.map e).comap e := (Ideal.comap_map_of_bijective e e.bijective).symm
  rw [h1, ← h, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [e]

theorem valuation_natGenerator_self (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [show ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) =
      algebraMap (𝓞 ℚ) ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  refine HeightOneSpectrum.intValuation_singleton w ?_ (asIdeal_eq_span_natGenerator w)
  exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero

theorem valuation_intCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ)
    (hz : ¬ (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣ z) : w.valuation ℚ (z : ℚ) = 1 := by
  rw [show (z : ℚ) = algebraMap (𝓞 ℚ) ℚ z from (map_intCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (z : 𝓞 ℚ))).2 ?_
  rwa [intCast_mem_asIdeal_iff]

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : ¬ Rat.HeightOneSpectrum.natGenerator w ∣ n) : w.valuation ℚ (n : ℚ) = 1 := by
  have := valuation_intCast_eq_one_of_not_dvd w n (by rwa [Int.natCast_dvd_natCast])
  simpa using this

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

theorem natGenerator_place (q : ℕ) (hq : q.Prime) : Rat.HeightOneSpectrum.natGenerator (place q hq) = q := by
  have := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, hq⟩
  exact congrArg Subtype.val this

theorem natCast_mem_asIdeal_place (q : ℕ) (hq : q.Prime) : (q : 𝓞 ℚ) ∈ (place q hq).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

theorem eq_place_of_mem {q : ℕ} (hq : q.Prime) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) :
    w = place q hq := by
  rw [natCast_mem_asIdeal_iff] at hw
  have := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).mp hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [place, Equiv.apply_symm_apply]
  exact Subtype.ext this

end Places

section NonSquare

theorem not_isSquare_of_valuation_odd (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) (n : ℤ)
    (hn : Odd n) (hx : Valued.v x = WithZero.exp n) : ¬ IsSquare x := by
  rintro ⟨s, rfl⟩
  have hs0 : Valued.v s ≠ 0 := by
    intro h0
    rw [map_mul, h0, mul_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  have hs : WithZero.exp (WithZero.log (Valued.v s)) = Valued.v s := WithZero.exp_log hs0
  rw [map_mul, ← hs, ← WithZero.exp_add, WithZero.exp_inj] at hx
  obtain ⟨k, hk⟩ := hn
  omega

theorem padic_isSquare_zmod_of_isSquare {p : ℕ} [Fact p.Prime] (u : ℤ) (hu : ¬ (p : ℤ) ∣ u)
    (h : IsSquare ((u : ℚ) : ℚ_[p])) : IsSquare ((u : ℤ) : ZMod p) := by
  obtain ⟨s, hs⟩ := h
  have hcast : ((u : ℚ) : ℚ_[p]) = ((u : ℤ) : ℚ_[p]) := by push_cast; rfl
  rw [hcast] at hs
  have hu1 : ‖((u : ℤ) : ℚ_[p])‖ = 1 := by
    have h1 : ‖((u : ℤ) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one u
    have h2 : ¬ ‖((u : ℤ) : ℚ_[p])‖ < 1 := by rwa [Padic.norm_intCast_lt_one_iff]
    push Not at h2
    exact le_antisymm h1 h2
  have hs1 : ‖s‖ = 1 := by
    have hmul : ‖s‖ * ‖s‖ = 1 := by rw [← norm_mul, ← hs, hu1]
    rcases mul_self_eq_one_iff.1 hmul with h | h
    · exact h
    · linarith [norm_nonneg s]
  let S : ℤ_[p] := ⟨s, hs1.le⟩
  have hS : ((u : ℤ) : ℤ_[p]) = S * S := by
    apply Subtype.ext
    rw [PadicInt.coe_intCast, PadicInt.coe_mul, hs]
  have := congrArg (PadicInt.toZMod (p := p)) hS
  rw [map_intCast, map_mul] at this
  exact ⟨_, this⟩

theorem isSquare_zmod_of_isSquare_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℤ)
    (hu : ¬ (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣ u)
    (h : IsSquare (algebraMap ℚ (w.adicCompletion ℚ) (u : ℚ))) :
    IsSquare ((u : ℤ) : ZMod (Rat.HeightOneSpectrum.natGenerator w)) := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator w)) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) w
  have h' : IsSquare (e (algebraMap ℚ (w.adicCompletion ℚ) (u : ℚ))) := h.map e
  have he : e (algebraMap ℚ (w.adicCompletion ℚ) (u : ℚ)) =
      ((u : ℚ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)]) := by
    rw [AlgHomClass.commutes]
    simp
  rw [he] at h'
  exact padic_isSquare_zmod_of_isSquare u hu h'

theorem isSquare_of_isSquare_sq_mul {K : Type*} [Field K] {s r : K} (hs : s ≠ 0)
    (h : IsSquare (s ^ 2 * r)) : IsSquare r := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t / s, ?_⟩
  field_simp
  linear_combination ht

end NonSquare

section Local

variable {a b : ℚ}

theorem not_nonempty_algEquiv_matrix_of_forall_isUnit (v : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ¬ Nonempty (ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]
        ≃ₐ[v.adicCompletion ℚ] Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  rintro ⟨ψ⟩
  set K := v.adicCompletion ℚ
  obtain ⟨φ₀, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl AlgEquiv.refl
  let E : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, 0]
  let F : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, 1]
  have hEF : E * F = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [E, F]
  have hF : F ≠ 0 := fun h => by simpa [F] using congrFun (congrFun h 1) 1
  have hE : E ≠ 0 := fun h => by simpa [E] using congrFun (congrFun h 0) 0
  have hEu : ¬ IsUnit E := fun hu => hF ((hu.mul_right_eq_zero).1 hEF)
  have hx0 : φ₀.symm (ψ.symm E) ≠ 0 := by
    intro h0
    apply hE
    have := congrArg ψ (congrArg φ₀ h0)
    simpa using this
  have hxu := hdiv _ hx0
  have : IsUnit E := by simpa using (hxu.map φ₀).map ψ
  exact hEu this

theorem exists_pureNrd_eq_of_not_forall_isUnit (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hndiv : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∀ c : v.adicCompletion ℚ, ∃ x y z : v.adicCompletion ℚ,
      -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2 = c := by
  set K := v.adicCompletion ℚ
  intro c
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  set A := algebraMap ℚ K a
  set B := algebraMap ℚ K b
  obtain ⟨φ₀, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := A) (d₂ := (0 : K)) (d₃ := B) rfl (map_zero _) rfl AlgEquiv.refl
  have hK : ¬ ∀ x : ℍ[K, A, B], x ≠ 0 → IsUnit x := by
    intro hall
    apply hndiv
    intro x hx
    have hx' : φ₀ x ≠ 0 := by
      intro h0; apply hx; simpa using congrArg φ₀.symm h0
    have hu := hall (φ₀ x) hx'
    simpa using hu.map φ₀.symm
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hAK : A ≠ 0 := by simpa [A] using (algebraMap ℚ K).injective.ne ha
  have hBK : B ≠ 0 := by simpa [B] using (algebraMap ℚ K).injective.ne hb
  have hiso : ∃ x₀ x₁ x₂ x₃ : K, ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      x₀ ^ 2 - A * x₁ ^ 2 - B * x₂ ^ 2 + A * B * x₃ ^ 2 = 0 := by
    by_contra hno
    apply hK
    refine (QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero K A B).2 fun x₀ x₁ x₂ x₃ h0 => ?_
    by_contra hne
    exact hno ⟨x₀, x₁, x₂, x₃, hne, h0⟩
  obtain ⟨x₀, x₁, x₂, x₃, hx, h0⟩ := hiso
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero K h2 A B hAK hBK x₀ x₁ x₂ x₃ hx h0

  let Nm : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
  have hNm : Nm * Nm = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Nm]
  have hNm0 : Nm ≠ 0 := fun h => by simpa [Nm] using congrFun (congrFun h 0) 1
  obtain ⟨n₀, n₁, n₂, n₃, hn⟩ : ∃ n₀ n₁ n₂ n₃ : K, ψ.symm Nm = ⟨n₀, n₁, n₂, n₃⟩ :=
    ⟨(ψ.symm Nm).re, (ψ.symm Nm).imI, (ψ.symm Nm).imJ, (ψ.symm Nm).imK, by ext <;> rfl⟩
  have hnn : (⟨n₀, n₁, n₂, n₃⟩ : ℍ[K, A, B]) * ⟨n₀, n₁, n₂, n₃⟩ = 0 := by
    rw [← hn, ← map_mul, hNm, map_zero]
  have hn0 : (⟨n₀, n₁, n₂, n₃⟩ : ℍ[K, A, B]) ≠ 0 := by
    rw [← hn]
    intro h0
    apply hNm0
    simpa using congrArg ψ h0
  rw [QuaternionAlgebra.mk_mul_mk] at hnn
  have hre := congrArg QuaternionAlgebra.re hnn
  have hI := congrArg QuaternionAlgebra.imI hnn
  have hJ := congrArg QuaternionAlgebra.imJ hnn
  have hKk := congrArg QuaternionAlgebra.imK hnn
  change _ = (0 : K) at hre hI hJ hKk
  have hn₀ : n₀ = 0 := by
    by_contra h
    have h1 : n₁ = 0 := by
      have : (2 * n₀) * n₁ = 0 := by linear_combination hI
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero h2 h)
      · exact h'
    have h2' : n₂ = 0 := by
      have : (2 * n₀) * n₂ = 0 := by linear_combination hJ
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero h2 h)
      · exact h'
    have h3 : n₃ = 0 := by
      have : (2 * n₀) * n₃ = 0 := by linear_combination hKk
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero h2 h)
      · exact h'
    subst h1 h2' h3
    have : n₀ * n₀ = 0 := by linear_combination hre
    exact h (mul_self_eq_zero.1 this)
  subst hn₀
  have hiso3 : ∃ x y z : K, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -A * x ^ 2 - B * y ^ 2 + A * B * z ^ 2 = 0 := by
    refine ⟨n₁, n₂, n₃, ?_, by linear_combination (-1 : K) * hre⟩
    rintro ⟨rfl, rfl, rfl⟩
    exact hn0 (by ext <;> rfl)
  exact QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero K A B hAK hBK hiso3 c

end Local

section Indef

variable {a b : ℚ}

theorem ne_zero_and_ne_zero_of_forall_isUnit (v : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) : a ≠ 0 ∧ b ≠ 0 := by
  set K := v.adicCompletion ℚ
  set A := algebraMap ℚ K a
  set B := algebraMap ℚ K b
  obtain ⟨φ₀, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := A) (d₂ := (0 : K)) (d₃ := B) rfl (map_zero _) rfl AlgEquiv.refl

  have key : ∀ y : ℍ[K, A, B], y ≠ 0 → y * y = 0 → False := by
    intro y hy hyy
    have hx0 : φ₀.symm y ≠ 0 := by
      intro h0
      apply hy
      simpa using congrArg φ₀ h0
    have hu := hdiv _ hx0
    have hsq : φ₀.symm y * φ₀.symm y = 0 := by rw [← map_mul, hyy, map_zero]
    exact hx0 (hu.mul_left_eq_zero.1 hsq)
  refine ⟨fun ha => ?_, fun hb => ?_⟩
  · have hA : A = 0 := by simp [A, ha]
    refine key ⟨0, 1, 0, 0⟩ (fun h => ?_) ?_
    · have := congrArg QuaternionAlgebra.imI h
      simp at this
    · ext <;> simp [hA]
  · have hB : B = 0 := by simp [B, hb]
    refine key ⟨0, 0, 1, 0⟩ (fun h => ?_) ?_
    · have := congrArg QuaternionAlgebra.imJ h
      simp at this
    · ext <;> simp [hB]

theorem real_repr (hind : 0 < a ∨ 0 < b) (ha : a ≠ 0) (hb : b ≠ 0) (c : ℚ) :
    ∃ x y z : ℝ, -(algebraMap ℚ ℝ a) * x ^ 2 - (algebraMap ℚ ℝ b) * y ^ 2
      + (algebraMap ℚ ℝ a) * (algebraMap ℚ ℝ b) * z ^ 2 = algebraMap ℚ ℝ c := by
  simp only [eq_ratCast]
  have aux : ∀ k d : ℝ, k ≠ 0 → 0 ≤ d / k → k * Real.sqrt (d / k) ^ 2 = d := by
    intro k d hk h
    rw [Real.sq_sqrt h]
    field_simp
  have hA : ((a : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ha
  have hB : ((b : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hb
  have sx : 0 ≤ (c : ℝ) / (-(a : ℝ)) →
      ∃ x y z : ℝ, -(a : ℝ) * x ^ 2 - (b : ℝ) * y ^ 2 + (a : ℝ) * (b : ℝ) * z ^ 2 = (c : ℝ) := fun h =>
    ⟨Real.sqrt ((c : ℝ) / (-(a : ℝ))), 0, 0, by
      have e := aux _ _ (neg_ne_zero.2 hA) h
      linear_combination e⟩
  have sy : 0 ≤ (c : ℝ) / (-(b : ℝ)) →
      ∃ x y z : ℝ, -(a : ℝ) * x ^ 2 - (b : ℝ) * y ^ 2 + (a : ℝ) * (b : ℝ) * z ^ 2 = (c : ℝ) := fun h =>
    ⟨0, Real.sqrt ((c : ℝ) / (-(b : ℝ))), 0, by
      have e := aux _ _ (neg_ne_zero.2 hB) h
      linear_combination e⟩
  have sz : 0 ≤ (c : ℝ) / ((a : ℝ) * (b : ℝ)) →
      ∃ x y z : ℝ, -(a : ℝ) * x ^ 2 - (b : ℝ) * y ^ 2 + (a : ℝ) * (b : ℝ) * z ^ 2 = (c : ℝ) := fun h =>
    ⟨0, 0, Real.sqrt ((c : ℝ) / ((a : ℝ) * (b : ℝ))), by
      have e := aux _ _ (mul_ne_zero hA hB) h
      linear_combination e⟩
  rcases le_or_gt (c : ℝ) 0 with hc | hc
  · rcases hind with ha' | hb'
    · have : (0 : ℝ) < a := by exact_mod_cast ha'
      exact sx (div_nonneg_of_nonpos hc (by linarith))
    · have : (0 : ℝ) < b := by exact_mod_cast hb'
      exact sy (div_nonneg_of_nonpos hc (by linarith))
  · rcases hind with ha' | hb'
    · have ha'' : (0 : ℝ) < a := by exact_mod_cast ha'
      rcases lt_or_gt_of_ne hb with hb' | hb'
      · have : (b : ℝ) < 0 := by exact_mod_cast hb'
        exact sy (div_nonneg hc.le (by linarith))
      · have : (0 : ℝ) < b := by exact_mod_cast hb'
        exact sz (div_nonneg hc.le (mul_pos ha'' this).le)
    · have hb'' : (0 : ℝ) < b := by exact_mod_cast hb'
      rcases lt_or_gt_of_ne ha with ha' | ha'
      · have : (a : ℝ) < 0 := by exact_mod_cast ha'
        exact sx (div_nonneg hc.le (by linarith))
      · have : (0 : ℝ) < a := by exact_mod_cast ha'
        exact sz (div_nonneg hc.le (mul_pos this hb'').le)

theorem exists_nrd_eq_of_forall_not_isSquare {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q') (c : ℚ) (hc : c ≠ 0)
    (hns : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal) →
      ¬ IsSquare (-(algebraMap ℚ (v.adicCompletion ℚ) c))) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = c := by
  have hqP : q.Prime := Fact.out
  obtain ⟨ha0, hb0⟩ := ne_zero_and_ne_zero_of_forall_isUnit (a := a) (b := b) (place q hqP)
    ((hB.2 (place q hqP)).2 (Or.inl (natCast_mem_asIdeal_place q hqP)))
  have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ x y z : v.adicCompletion ℚ,
      -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2
        = algebraMap ℚ (v.adicCompletion ℚ) c := by
    intro v
    by_cases hram : (q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal
    · have hdiv := (hB.2 v).2 hram
      exact QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split a b ha0 hb0
        v (not_nonempty_algEquiv_matrix_of_forall_isUnit v hdiv) _ (hns v hram)
    · exact exists_pureNrd_eq_of_not_forall_isUnit ha0 hb0 v (fun h => hram ((hB.2 v).1 h)) _
  have hR := real_repr hB.1 ha0 hb0 c
  obtain ⟨x, y, z, hxyz⟩ :=
    QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real a b ha0 hb0 c hc hv hR
  exact ⟨⟨0, x, y, z⟩, by rw [QuaternionAlgebra.nrd_mk]; linear_combination hxyz⟩

theorem not_isSquare_neg_algebraMap_of_odd (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (n : ℤ) (hn : Odd n)
    (h : w.valuation ℚ c = WithZero.exp n) : ¬ IsSquare (-(algebraMap ℚ (w.adicCompletion ℚ) c)) := by
  refine not_isSquare_of_valuation_odd w _ n hn ?_
  rw [Valuation.map_neg, valued_algebraMap, h]

end Indef

section NormGroup

variable {a b : ℚ}

def IsNrd (a b : ℚ) (t : ℚ) : Prop := ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = t

theorem nrd_mul (x y : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_smul (r : ℚ) (y : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (r • y) = r ^ 2 * QuaternionAlgebra.nrd y := by
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp [QuaternionAlgebra.nrd]
  ring

theorem IsNrd.mul {s t : ℚ} (hs : IsNrd a b s) (ht : IsNrd a b t) : IsNrd a b (s * t) := by
  obtain ⟨γ, rfl⟩ := hs
  obtain ⟨δ, rfl⟩ := ht
  exact ⟨γ * δ, nrd_mul γ δ⟩

theorem IsNrd.inv {t : ℚ} (ht : IsNrd a b t) (h0 : t ≠ 0) : IsNrd a b t⁻¹ := by
  obtain ⟨γ, rfl⟩ := ht
  refine ⟨(QuaternionAlgebra.nrd γ)⁻¹ • γ, ?_⟩
  rw [nrd_smul]
  field_simp

theorem IsNrd.div {s t : ℚ} (hs : IsNrd a b s) (ht : IsNrd a b t) (h0 : t ≠ 0) : IsNrd a b (s / t) := by
  rw [div_eq_mul_inv]
  exact hs.mul (ht.inv h0)

theorem IsNrd.of_mul_left {s t : ℚ} (hs : IsNrd a b s) (hst : IsNrd a b (s * t)) (h0 : s ≠ 0) :
    IsNrd a b t := by
  have := hst.div hs h0
  rwa [mul_div_cancel_left₀ _ h0] at this

theorem IsNrd.of_mul_right {s t : ℚ} (ht : IsNrd a b t) (hst : IsNrd a b (s * t)) (h0 : t ≠ 0) :
    IsNrd a b s := by
  have := hst.div ht h0
  rwa [mul_div_cancel_right₀ _ h0] at this

end NormGroup

section Val

theorem valuation_place_self (p : ℕ) (hp : p.Prime) :
    (place p hp).valuation ℚ (p : ℚ) = WithZero.exp (-1 : ℤ) := by
  have := valuation_natGenerator_self (place p hp)
  rwa [natGenerator_place] at this

theorem valuation_place_natCast_of_not_dvd (p : ℕ) (hp : p.Prime) (n : ℕ) (h : ¬ p ∣ n) :
    (place p hp).valuation ℚ (n : ℚ) = 1 :=
  valuation_natCast_eq_one_of_not_dvd _ n (by rwa [natGenerator_place])

theorem valuation_place_prime_of_ne (p r : ℕ) (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    (place p hp).valuation ℚ (r : ℚ) = 1 :=
  valuation_place_natCast_of_not_dvd p hp r fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 h)

theorem exists_valuation_eq_exp (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (hc : c ≠ 0) :
    ∃ m : ℤ, w.valuation ℚ c = WithZero.exp m :=
  ⟨WithZero.log (w.valuation ℚ c), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hc)).symm⟩

theorem forall_odd_of_place {q q' : ℕ} (hqP : q.Prime) (hq'P : q'.Prime) (c : ℚ) (n n' : ℤ)
    (hn : Odd n) (hn' : Odd n')
    (hc : (place q hqP).valuation ℚ c = WithZero.exp n) (hc' : (place q' hq'P).valuation ℚ c = WithZero.exp n') :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal) →
      ∃ k : ℤ, Odd k ∧ v.valuation ℚ c = WithZero.exp k := by
  intro v hv
  rcases hv with hv | hv
  · rw [eq_place_of_mem hqP hv]; exact ⟨n, hn, hc⟩
  · rw [eq_place_of_mem hq'P hv]; exact ⟨n', hn', hc'⟩

end Val

section Main

variable {a b : ℚ}

theorem isIndefiniteRamifiedExactlyAt_comm {q q' : ℕ} (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q') :
    QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q' q :=
  ⟨hB.1, fun v => (hB.2 v).trans or_comm⟩

theorem isNrd_of_odd {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q') (c : ℚ) (hc : c ≠ 0) (n n' : ℤ)
    (hn : Odd n) (hn' : Odd n')
    (hcq : (place q (Fact.out : q.Prime)).valuation ℚ c = WithZero.exp n)
    (hcq' : (place q' (Fact.out : q'.Prime)).valuation ℚ c = WithZero.exp n') : IsNrd a b c :=
  exists_nrd_eq_of_forall_not_isSquare hB c hc fun v hv => by
    obtain ⟨k, hk, h⟩ := forall_odd_of_place Fact.out Fact.out c n n' hn hn' hcq hcq' v hv
    exact not_isSquare_neg_algebraMap_of_odd v c k hk h

theorem isSquare_zmod_cast_of_eq {p r : ℕ} (h : p = r) (x : ℤ) (hx : IsSquare ((x : ℤ) : ZMod p)) :
    IsSquare ((x : ℤ) : ZMod r) := by
  subst h
  exact hx

theorem isNrd_prime_of_ne_of_ne_two {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q') (hqq' : q ≠ q') (hq'2 : q' ≠ 2) :
    IsNrd a b q ∧ IsNrd a b q' := by
  have hqP : q.Prime := Fact.out
  have hq'P : q'.Prime := Fact.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqP.ne_zero
  have hq'0 : (q' : ℚ) ≠ 0 := by exact_mod_cast hq'P.ne_zero

  have hchar : ringChar (ZMod q') ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq'2
  obtain ⟨u₀, hu₀⟩ := FiniteField.exists_nonsquare hchar
  have hu₀0 : u₀ ≠ 0 := by rintro rfl; exact hu₀ (IsSquare.zero)
  have hqz : (q : ZMod q') ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hqq' ((Nat.prime_dvd_prime_iff_eq hq'P hqP).1 h).symm
  set τ : ZMod q' := u₀ * (-(q : ZMod q'))⁻¹ with hτ
  have hτ0 : τ ≠ 0 := mul_ne_zero hu₀0 (inv_ne_zero (neg_ne_zero.2 hqz))
  have hqτ : -(q : ZMod q') * τ = u₀ := by
    rw [hτ, mul_comm u₀, ← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.2 hqz), one_mul]

  obtain ⟨n, hnq, hnq', hnτ⟩ : ∃ n : ℕ, ¬ q ∣ n ∧ ¬ q' ∣ n ∧ (n : ZMod q') = τ := by
    have hval : ¬ q' ∣ τ.val := fun h => by
      have h1 : τ.val = 0 := Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt τ)
      exact hτ0 ((ZMod.val_eq_zero τ).1 h1)
    by_cases hdq : q ∣ τ.val
    · refine ⟨τ.val + q', fun h => ?_, fun h => hval ((Nat.dvd_add_self_right).1 h), by simp⟩
      have : q ∣ q' := (Nat.dvd_add_right hdq).1 h
      exact hqq' ((Nat.prime_dvd_prime_iff_eq hqP hq'P).1 this)
    · exact ⟨τ.val, hdq, hval, ZMod.natCast_zmod_val τ⟩
  have hn0 : (n : ℚ) ≠ 0 := by
    have : n ≠ 0 := fun h => hnq (h ▸ dvd_zero q)
    exact_mod_cast this

  have h1 : IsNrd a b ((q : ℚ) * n) := by
    refine exists_nrd_eq_of_forall_not_isSquare hB _ (mul_ne_zero hq0 hn0) fun v hv => ?_
    by_cases hvq : (q : 𝓞 ℚ) ∈ v.asIdeal
    ·
      rw [eq_place_of_mem hqP hvq]
      refine not_isSquare_neg_algebraMap_of_odd _ _ (-1) (by decide) ?_
      rw [map_mul, valuation_place_self, valuation_place_natCast_of_not_dvd q hqP n hnq, mul_one]
    · have hvq' : (q' : 𝓞 ℚ) ∈ v.asIdeal := hv.resolve_left hvq
      rw [eq_place_of_mem hq'P hvq']
      intro hsq
      apply hu₀
      have hu : ¬ (Rat.HeightOneSpectrum.natGenerator (place q' hq'P) : ℤ) ∣ (-((q * n : ℕ) : ℤ)) := by
        rw [natGenerator_place, Int.dvd_neg, Int.natCast_dvd_natCast]
        intro h
        rcases (Nat.Prime.dvd_mul hq'P).1 h with h | h
        · exact hqq' ((Nat.prime_dvd_prime_iff_eq hq'P hqP).1 h).symm
        · exact hnq' h
      have hsq' : IsSquare (algebraMap ℚ ((place q' hq'P).adicCompletion ℚ) ((-((q * n : ℕ) : ℤ) : ℤ) : ℚ)) := by
        have e : ((-((q * n : ℕ) : ℤ) : ℤ) : ℚ) = -((q : ℚ) * n) := by push_cast; ring
        rw [e, map_neg]
        exact hsq
      have h2 := isSquare_zmod_cast_of_eq (natGenerator_place q' hq'P) _
        (isSquare_zmod_of_isSquare_algebraMap (place q' hq'P) _ hu hsq')
      have e2 : ((-((q * n : ℕ) : ℤ) : ℤ) : ZMod q') = -(q : ZMod q') * τ := by
        rw [← hnτ]; push_cast; ring
      rwa [e2, hqτ] at h2

  have hqq'N : IsNrd a b ((q : ℚ) * q') :=
    isNrd_of_odd hB _ (mul_ne_zero hq0 hq'0) (-1) (-1) (by decide) (by decide)
      (by rw [map_mul, valuation_place_self, valuation_place_prime_of_ne q q' hqP hq'P hqq', mul_one])
      (by rw [map_mul, valuation_place_prime_of_ne q' q hq'P hqP (Ne.symm hqq'), valuation_place_self, one_mul])
  have hnqq'N : IsNrd a b ((n : ℚ) * ((q : ℚ) * q')) :=
    isNrd_of_odd hB _ (mul_ne_zero hn0 (mul_ne_zero hq0 hq'0)) (-1) (-1) (by decide) (by decide)
      (by rw [map_mul, map_mul, valuation_place_natCast_of_not_dvd q hqP n hnq, valuation_place_self,
            valuation_place_prime_of_ne q q' hqP hq'P hqq', one_mul, mul_one])
      (by rw [map_mul, map_mul, valuation_place_natCast_of_not_dvd q' hq'P n hnq',
            valuation_place_prime_of_ne q' q hq'P hqP (Ne.symm hqq'), valuation_place_self, one_mul, one_mul])
  have hnN : IsNrd a b (n : ℚ) := IsNrd.of_mul_right hqq'N hnqq'N (mul_ne_zero hq0 hq'0)
  have hqN : IsNrd a b (q : ℚ) := IsNrd.of_mul_right hnN h1 hn0
  exact ⟨hqN, IsNrd.of_mul_left hqN hqq'N hq0⟩

private theorem _root_.HSICC.main {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q') (t : ℚ) (ht : t ≠ 0) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = t := by
  have hqP : q.Prime := Fact.out
  have hq'P : q'.Prime := Fact.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqP.ne_zero
  have hq'0 : (q' : ℚ) ≠ 0 := by exact_mod_cast hq'P.ne_zero
  obtain ⟨m, hm⟩ := exists_valuation_eq_exp (place q hqP) t ht
  obtain ⟨m', hm'⟩ := exists_valuation_eq_exp (place q' hq'P) t ht
  change IsNrd a b t
  by_cases hqq' : q = q'
  ·
    subst hqq'
    have hpl : m' = m := by
      have : WithZero.exp m' = WithZero.exp m := by rw [← hm', ← hm]
      exact WithZero.exp_injective this
    rcases Int.even_or_odd m with he | ho
    · have h1 : IsNrd a b (t * q) :=
        isNrd_of_odd hB _ (mul_ne_zero ht hq0) (m + (-1)) (m + (-1)) (he.add_odd odd_neg_one) (he.add_odd odd_neg_one)
          (by rw [map_mul, hm, valuation_place_self, WithZero.exp_add])
          (by rw [map_mul, hm, valuation_place_self, WithZero.exp_add])
      have h2 : IsNrd a b (q : ℚ) :=
        isNrd_of_odd hB _ hq0 (-1) (-1) (by decide) (by decide) (valuation_place_self q hqP) (valuation_place_self q hqP)
      exact IsNrd.of_mul_right h2 h1 hq0
    · exact isNrd_of_odd hB t ht m m ho ho hm (hpl ▸ hm')
  ·
    obtain ⟨hqN, hq'N⟩ : IsNrd a b (q : ℚ) ∧ IsNrd a b (q' : ℚ) := by
      by_cases hq'2 : q' = 2
      · have hq2 : q ≠ 2 := fun h => hqq' (h.trans hq'2.symm)
        obtain ⟨h1, h2⟩ := isNrd_prime_of_ne_of_ne_two (isIndefiniteRamifiedExactlyAt_comm hB) (Ne.symm hqq') hq2
        exact ⟨h2, h1⟩
      · exact isNrd_prime_of_ne_of_ne_two hB hqq' hq'2
    have vq_q' : (place q hqP).valuation ℚ (q' : ℚ) = 1 := valuation_place_prime_of_ne q q' hqP hq'P hqq'
    have vq'_q : (place q' hq'P).valuation ℚ (q : ℚ) = 1 := valuation_place_prime_of_ne q' q hq'P hqP (Ne.symm hqq')
    rcases Int.even_or_odd m with he | ho <;> rcases Int.even_or_odd m' with he' | ho'
    ·
      have h1 : IsNrd a b (t * q * q') :=
        isNrd_of_odd hB _ (mul_ne_zero (mul_ne_zero ht hq0) hq'0) (m + (-1)) (m' + (-1))
          (he.add_odd odd_neg_one) (he'.add_odd odd_neg_one)
          (by rw [map_mul, map_mul, hm, valuation_place_self, vq_q', mul_one, WithZero.exp_add])
          (by rw [map_mul, map_mul, hm', vq'_q, valuation_place_self, mul_one, WithZero.exp_add])
      exact IsNrd.of_mul_right hqN (IsNrd.of_mul_right hq'N h1 hq'0) hq0
    ·
      have h1 : IsNrd a b (t * q) :=
        isNrd_of_odd hB _ (mul_ne_zero ht hq0) (m + (-1)) m' (he.add_odd odd_neg_one) ho'
          (by rw [map_mul, hm, valuation_place_self, WithZero.exp_add])
          (by rw [map_mul, hm', vq'_q, mul_one])
      exact IsNrd.of_mul_right hqN h1 hq0
    ·
      have h1 : IsNrd a b (t * q') :=
        isNrd_of_odd hB _ (mul_ne_zero ht hq'0) m (m' + (-1)) ho (he'.add_odd odd_neg_one)
          (by rw [map_mul, hm, vq_q', mul_one])
          (by rw [map_mul, hm', valuation_place_self, WithZero.exp_add])
      exact IsNrd.of_mul_right hq'N h1 hq'0
    · exact isNrd_of_odd hB t ht m m' ho ho' hm hm'

p2m_export "HSICC" "main"
end Main

section Pure

variable {a b : ℚ}

theorem sq_eq_trd_mul_sub_nrd' (x : ℍ[ℚ, a, b]) :
    x * x = ((QuaternionAlgebra.trd x : ℚ) : ℍ[ℚ, a, b]) * x - ((QuaternionAlgebra.nrd x : ℚ) : ℍ[ℚ, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  have hc : ∀ c : ℚ, ((c : ℚ) : ℍ[ℚ, a, b]) = ⟨c, 0, 0, 0⟩ := fun _ => rfl
  rw [hc, hc]
  ext <;> simp [QuaternionAlgebra.trd, QuaternionAlgebra.nrd] <;> ring

theorem exists_pure_sq_eq {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q') (hqq' : q ≠ q') :
    ∃ γ : ℍ[ℚ, a, b], γ * γ = -((((q * q' : ℕ)) : ℚ) • (1 : ℍ[ℚ, a, b])) := by
  have hqP : q.Prime := Fact.out
  have hq'P : q'.Prime := Fact.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqP.ne_zero
  have hq'0 : (q' : ℚ) ≠ 0 := by exact_mod_cast hq'P.ne_zero
  set c : ℚ := ((q * q' : ℕ) : ℚ) with hcdef
  have hc0 : c ≠ 0 := by rw [hcdef]; push_cast; exact mul_ne_zero hq0 hq'0
  have hcq : (place q hqP).valuation ℚ c = WithZero.exp (-1 : ℤ) := by
    rw [hcdef, Nat.cast_mul, map_mul, valuation_place_self, valuation_place_prime_of_ne q q' hqP hq'P hqq', mul_one]
  have hcq' : (place q' hq'P).valuation ℚ c = WithZero.exp (-1 : ℤ) := by
    rw [hcdef, Nat.cast_mul, map_mul, valuation_place_prime_of_ne q' q hq'P hqP (Ne.symm hqq'), valuation_place_self,
      one_mul]
  have hns : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal) →
      ¬ IsSquare (-(algebraMap ℚ (v.adicCompletion ℚ) c)) := fun v hv => by
    obtain ⟨k, hk, h⟩ := forall_odd_of_place hqP hq'P c (-1) (-1) (by decide) (by decide) hcq hcq' v hv
    exact not_isSquare_neg_algebraMap_of_odd v c k hk h

  obtain ⟨ha0, hb0⟩ := ne_zero_and_ne_zero_of_forall_isUnit (a := a) (b := b) (place q hqP)
    ((hB.2 (place q hqP)).2 (Or.inl (natCast_mem_asIdeal_place q hqP)))
  have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ x y z : v.adicCompletion ℚ,
      -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2
        = algebraMap ℚ (v.adicCompletion ℚ) c := by
    intro v
    by_cases hram : (q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal
    · have hdiv := (hB.2 v).2 hram
      exact QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split a b ha0 hb0
        v (not_nonempty_algEquiv_matrix_of_forall_isUnit v hdiv) _ (hns v hram)
    · exact exists_pureNrd_eq_of_not_forall_isUnit ha0 hb0 v (fun h => hram ((hB.2 v).1 h)) _
  have hR := real_repr hB.1 ha0 hb0 c
  obtain ⟨x, y, z, hxyz⟩ :=
    QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real a b ha0 hb0 c hc0 hv hR
  refine ⟨⟨0, x, y, z⟩, ?_⟩
  have hn : QuaternionAlgebra.nrd (⟨0, x, y, z⟩ : ℍ[ℚ, a, b]) = c := by
    rw [QuaternionAlgebra.nrd_mk]; linear_combination hxyz
  have ht : QuaternionAlgebra.trd (⟨0, x, y, z⟩ : ℍ[ℚ, a, b]) = 0 := by
    rw [QuaternionAlgebra.trd_mk]; ring
  rw [sq_eq_trd_mul_sub_nrd', hn, ht, QuaternionAlgebra.coe_zero, zero_mul, zero_sub, hcdef,
    ← QuaternionAlgebra.coe_mul_eq_smul, mul_one]

end Pure

end HSICC

namespace MuAlg
p2m_open "QuaternionAlgebra~nrd_mul"

section Algebra

variable {K : Type*} [Field K] {A B : K}

theorem nrd_mul' (x y : ℍ[K, A, B]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem nrd_add' (x y : ℍ[K, A, B]) : nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, nrd_mk, trd_mk]
  ring

theorem trd_add' (x y : ℍ[K, A, B]) : trd (x + y) = trd x + trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, trd_mk]
  ring

theorem trd_mul_comm' (x y : ℍ[K, A, B]) : trd (x * y) = trd (y * x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, trd_mk]
  ring

theorem trd_sub' (x y : ℍ[K, A, B]) : trd (x - y) = trd x - trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_sub_mk, trd_mk]
  ring

theorem trd_neg' (x : ℍ[K, A, B]) : trd (-x) = -trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.neg_mk, trd_mk]
  ring

theorem coe_eq_mk (c : K) : ((c : K) : ℍ[K, A, B]) = ⟨c, 0, 0, 0⟩ := rfl

theorem trd_coe' (c : K) : trd ((c : K) : ℍ[K, A, B]) = 2 * c := by
  rw [coe_eq_mk, trd_mk]

theorem nrd_coe' (c : K) : nrd ((c : K) : ℍ[K, A, B]) = c ^ 2 := by
  rw [coe_eq_mk, nrd_mk]; ring

theorem trd_coe_mul' (c : K) (x : ℍ[K, A, B]) : trd ((c : ℍ[K, A, B]) * x) = c * trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  rw [coe_eq_mk, QuaternionAlgebra.mk_mul_mk, trd_mk, trd_mk]
  ring

theorem nrd_coe_mul' (c : K) (x : ℍ[K, A, B]) : nrd ((c : ℍ[K, A, B]) * x) = c ^ 2 * nrd x := by
  rw [nrd_mul', nrd_coe']

theorem star_coe' (c : K) : star ((c : K) : ℍ[K, A, B]) = c := by
  rw [coe_eq_mk, QuaternionAlgebra.star_mk]; ext <;> simp

theorem sq_eq_trd_mul_sub_nrd (x : ℍ[K, A, B]) :
    x * x = ((trd x : K) : ℍ[K, A, B]) * x - ((nrd x : K) : ℍ[K, A, B]) := by
  have h1 : x + star x = ((trd x : K) : ℍ[K, A, B]) := add_star_eq_coe_trd x
  have h2 : x * star x = ((nrd x : K) : ℍ[K, A, B]) := mul_star_eq_coe_nrd x
  have h3 : star x = ((trd x : K) : ℍ[K, A, B]) - x := by rw [← h1, add_sub_cancel_left]
  rw [h3, mul_sub, ← QuaternionAlgebra.coe_commutes] at h2

  rw [← h2]
  abel

theorem intCast_eq_coe (z : ℤ) : ((z : ℤ) : ℍ[K, A, B]) = ((z : K) : ℍ[K, A, B]) := by
  ext <;> simp

theorem natCast_eq_coe (m : ℕ) : ((m : ℕ) : ℍ[K, A, B]) = ((m : K) : ℍ[K, A, B]) := by
  ext <;> simp

section Division

variable (hD : ∀ x : ℍ[K, A, B], x ≠ 0 → IsUnit x)
include hD

theorem nrd_ne_zero_of_ne_zero {x : ℍ[K, A, B]} (hx : x ≠ 0) : nrd x ≠ 0 := by
  intro h0
  have h2 : x * star x = 0 := by rw [mul_star_eq_coe_nrd, h0]; rfl
  have hs : star x = 0 := (hD x hx).mul_right_eq_zero.1 h2
  apply hx
  have := congrArg star hs
  rwa [star_star, star_zero] at this

theorem eq_zero_of_nrd_eq_zero {x : ℍ[K, A, B]} (h : nrd x = 0) : x = 0 := by
  by_contra hx
  exact nrd_ne_zero_of_ne_zero hD hx h

theorem eq_zero_or_eq_zero_of_mul_eq_zero {x y : ℍ[K, A, B]} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr ((hD x hx).mul_right_eq_zero.1 h)

theorem trd_eq_and_nrd_eq_of_sq_eq {x : ℍ[K, A, B]} (hx : ∀ c : K, x ≠ (c : ℍ[K, A, B]))
    {s r : K} (h : x * x = ((s : K) : ℍ[K, A, B]) * x - ((r : K) : ℍ[K, A, B])) :
    trd x = s ∧ nrd x = r := by
  have hch := sq_eq_trd_mul_sub_nrd x

  have e : ((trd x : K) : ℍ[K, A, B]) * x - ((nrd x : K) : ℍ[K, A, B]) =
      ((s : K) : ℍ[K, A, B]) * x - ((r : K) : ℍ[K, A, B]) := hch.symm.trans h
  have key : (((trd x - s : K)) : ℍ[K, A, B]) * x = (((nrd x - r : K)) : ℍ[K, A, B]) := by
    rw [QuaternionAlgebra.coe_sub, QuaternionAlgebra.coe_sub, sub_mul]
    calc ((trd x : K) : ℍ[K, A, B]) * x - ((s : K) : ℍ[K, A, B]) * x
        = (((trd x : K) : ℍ[K, A, B]) * x - ((nrd x : K) : ℍ[K, A, B]))
            - (((s : K) : ℍ[K, A, B]) * x - ((r : K) : ℍ[K, A, B]))
            + (((nrd x : K) : ℍ[K, A, B]) - ((r : K) : ℍ[K, A, B])) := by abel
      _ = ((nrd x : K) : ℍ[K, A, B]) - ((r : K) : ℍ[K, A, B]) := by rw [e, sub_self, zero_add]
  by_cases hts : trd x - s = 0
  · have h1 : trd x = s := sub_eq_zero.1 hts
    refine ⟨h1, ?_⟩
    rw [hts, QuaternionAlgebra.coe_zero, zero_mul, ← QuaternionAlgebra.coe_zero] at key
    have := QuaternionAlgebra.coe_injective key
    exact (sub_eq_zero.1 this.symm)
  · exfalso
    apply hx ((trd x - s)⁻¹ * (nrd x - r))
    have h1 : x = (((trd x - s)⁻¹ : K) : ℍ[K, A, B]) * ((((trd x - s : K)) : ℍ[K, A, B]) * x) := by
      rw [← mul_assoc, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hts, QuaternionAlgebra.coe_one, one_mul]
    calc x = (((trd x - s)⁻¹ : K) : ℍ[K, A, B]) * ((((trd x - s : K)) : ℍ[K, A, B]) * x) := h1
      _ = (((trd x - s)⁻¹ : K) : ℍ[K, A, B]) * (((nrd x - r : K)) : ℍ[K, A, B]) := by rw [key]
      _ = ((((trd x - s)⁻¹ * (nrd x - r) : K)) : ℍ[K, A, B]) := by rw [QuaternionAlgebra.coe_mul]

theorem trd_eq_zero_of_sq_eq_coe {x : ℍ[K, A, B]} (hx : ∀ c : K, x ≠ (c : ℍ[K, A, B]))
    {d : K} (h : x * x = ((d : K) : ℍ[K, A, B])) : trd x = 0 ∧ nrd x = -d := by
  have := trd_eq_and_nrd_eq_of_sq_eq hD hx (s := 0) (r := -d)
    (by rw [h, QuaternionAlgebra.coe_zero, zero_mul, QuaternionAlgebra.coe_neg, zero_sub, neg_neg])
  exact this

end Division

end Algebra

end MuAlg

namespace MuInput

variable {a b : ℚ}

private theorem _root_.MuInput.nrd_mul' (x y : ℍ[ℚ, a, b]) : QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

p2m_export "MuInput" "nrd_mul'"
theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    star x ∈ Λ := by
  obtain ⟨-, t, ht⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hx
  have hs : star x = ((QuaternionAlgebra.trd x : ℚ) : ℍ[ℚ, a, b]) - x := by
    rw [← QuaternionAlgebra.add_star_eq_coe_trd, add_sub_cancel_left]
  have hc : ((QuaternionAlgebra.trd x : ℚ) : ℍ[ℚ, a, b]) = (t : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← ht, ← Int.cast_smul_eq_zsmul ℚ, ← QuaternionAlgebra.coe_mul_eq_smul, mul_one]
  rw [hs, hc]
  exact Λ.sub_mem (Λ.smul_mem _ hO.one_mem) hx

theorem eq_zero_of_mul_eq_zero_right {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q') {A x : ℍ[ℚ, a, b]} (hx : x ≠ 0) (h : A * x = 0) :
    A = 0 := by
  obtain ⟨u, hu⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB x hx
  calc A = A * x * ((u⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by rw [← hu, Units.mul_inv_cancel_right]
    _ = 0 := by rw [h, zero_mul]

theorem exists_mu {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    ∃ μ : ↥Λ, (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])) := by
  classical
  have hO : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder
  obtain ⟨γ₀, hγ₀⟩ := HSICC.exists_pure_sq_eq hB (Ne.symm hqq')
  set c : ℚ := ((q * q' : ℕ) : ℚ) with hcdef

  let f : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b] := LinearMap.mulRight ℤ γ₀
  have hf : ∀ x, f x = x * γ₀ := fun _ => rfl
  set I : Submodule ℤ ℍ[ℚ, a, b] := Λ ⊔ Λ.map f with hI
  have hmemI : ∀ y, y ∈ I ↔ ∃ l ∈ Λ, ∃ l' ∈ Λ, y = l + l' * γ₀ := by
    intro y
    rw [hI, Submodule.mem_sup]
    constructor
    · rintro ⟨y₁, hy₁, y₂, hy₂, rfl⟩
      obtain ⟨l', hl', rfl⟩ := Submodule.mem_map.1 hy₂
      exact ⟨y₁, hy₁, l', hl', by rw [hf]⟩
    · rintro ⟨l, hl, l', hl', rfl⟩
      exact ⟨l, hl, f l', Submodule.mem_map.2 ⟨l', hl', rfl⟩, by rw [hf]⟩
  have hIfg : I.FG := Submodule.FG.sup hO.fg (Submodule.FG.map f hO.fg)
  have hΛI : Λ ≤ I := by rw [hI]; exact le_sup_left
  have hIspan : Submodule.span ℚ (I : Set ℍ[ℚ, a, b]) = ⊤ := by
    apply top_le_iff.1
    rw [← hO.spanTop]
    exact Submodule.span_mono hΛI
  have hIstab : ∀ x ∈ Λ, ∀ y ∈ I, x * y ∈ I := by
    intro x hx y hy
    obtain ⟨l, hl, l', hl', rfl⟩ := (hmemI y).1 hy
    exact (hmemI _).2 ⟨x * l, hO.mul_mem hx hl, x * l', hO.mul_mem hx hl', by rw [mul_add, mul_assoc]⟩
  obtain ⟨x₀, hx₀, hprinc⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ I hIfg hIspan hIstab
  have hx₀I : x₀ ∈ I := (hprinc x₀).2 ⟨1, hO.one_mem, one_mul _⟩

  have hcΛ : ∀ l ∈ Λ, c • l ∈ Λ := by
    intro l hl
    rw [hcdef, Nat.cast_smul_eq_nsmul]
    exact Λ.toAddSubmonoid.nsmul_mem hl _
  have hIγ : ∀ y ∈ I, y * γ₀ ∈ I := by
    intro y hy
    obtain ⟨l, hl, l', hl', rfl⟩ := (hmemI y).1 hy
    refine (hmemI _).2 ⟨-(c • l'), Λ.neg_mem (hcΛ l' hl'), l, hl, ?_⟩
    rw [add_mul, mul_assoc, hγ₀, mul_neg, mul_smul_comm, mul_one]
    abel
  obtain ⟨μ, hμΛ, hμ⟩ := (hprinc (x₀ * γ₀)).1 (hIγ x₀ hx₀I)
  refine ⟨⟨μ, hμΛ⟩, ?_⟩

  have h1 : (μ * μ - -(c • (1 : ℍ[ℚ, a, b]))) * x₀ = 0 := by
    rw [sub_mul, mul_assoc, hμ, ← mul_assoc, hμ, mul_assoc, hγ₀, neg_mul, smul_mul_assoc, one_mul, mul_neg,
      mul_smul_comm, mul_one, sub_self]
  have := eq_zero_of_mul_eq_zero_right hB hx₀ h1
  exact sub_eq_zero.1 this

theorem forall_conj_mem {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (x : ↥Λ) : ∃ y : ↥Λ, (μ : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) = star (x : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) := by
  classical
  have hO : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder
  have hqP : q.Prime := Fact.out
  have hq'P : q'.Prime := Fact.out
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqP.ne_zero
  have hq'0 : (q' : ℚ) ≠ 0 := by exact_mod_cast hq'P.ne_zero
  have hD : ∀ z : ℍ[ℚ, a, b], z ≠ 0 → IsUnit z := fun z hz =>
    QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB z hz
  set c : ℚ := ((q * q' : ℕ) : ℚ) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; push_cast; exact mul_pos (by exact_mod_cast hqP.pos) (by exact_mod_cast hq'P.pos)
  have hμ' : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = (((-c : ℚ)) : ℍ[ℚ, a, b]) := by
    rw [hμ, QuaternionAlgebra.coe_neg, ← QuaternionAlgebra.coe_mul_eq_smul, mul_one]
  have hnc : ∀ d : ℚ, (μ : ℍ[ℚ, a, b]) ≠ ((d : ℚ) : ℍ[ℚ, a, b]) := by
    intro d hd
    have h1 := hμ'
    rw [hd, ← QuaternionAlgebra.coe_mul] at h1
    have h2 := QuaternionAlgebra.coe_injective h1
    nlinarith [mul_self_nonneg d]
  obtain ⟨htr, hn⟩ := MuAlg.trd_eq_zero_of_sq_eq_coe hD hnc hμ'
  rw [neg_neg] at hn

  obtain ⟨πq, hπqΛ, hπqn, -, hπqR, hPq⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ q (Or.inl rfl)
  obtain ⟨πq', hπq'Λ, hπq'n, -, hπq'R, hPq'⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ q' (Or.inr rfl)

  obtain ⟨l, hlΛ, hμl⟩ := (hPq (μ : ℍ[ℚ, a, b]) μ.2).1 ⟨q', by rw [hn, hcdef]; push_cast; ring⟩

  have hnl : QuaternionAlgebra.nrd l = (q' : ℚ) ∨ QuaternionAlgebra.nrd l = -(q' : ℚ) := by
    have e := congrArg QuaternionAlgebra.nrd hμl
    rw [MuAlg.nrd_mul', hn, hcdef] at e
    push_cast at e
    rcases hπqn with h | h <;> rw [h] at e
    · left; field_simp at e ⊢; linarith
    · right; field_simp at e ⊢; linarith
  obtain ⟨l', hl'Λ, hll'⟩ := (hPq' l hlΛ).1 (by
    rcases hnl with h | h
    · exact ⟨1, by rw [h]; ring⟩
    · exact ⟨-1, by rw [h]; push_cast; ring⟩)

  have hnl' : QuaternionAlgebra.nrd l' = 1 ∨ QuaternionAlgebra.nrd l' = -1 := by
    have e := congrArg QuaternionAlgebra.nrd hll'
    rw [MuAlg.nrd_mul'] at e
    rcases hnl with h | h <;> rcases hπq'n with h' | h' <;> rw [h, h'] at e
    · left; field_simp at e ⊢; linarith
    · right; field_simp at e ⊢; linarith
    · right; field_simp at e ⊢; linarith
    · left; field_simp at e ⊢; linarith

  obtain ⟨li, hliΛ, hli⟩ : ∃ li ∈ Λ, l' * li = 1 := by
    rcases hnl' with h | h
    · refine ⟨star l', star_mem hO hl'Λ, ?_⟩
      rw [QuaternionAlgebra.mul_star_eq_coe_nrd, h, QuaternionAlgebra.coe_one]
    · refine ⟨-star l', Λ.neg_mem (star_mem hO hl'Λ), ?_⟩
      rw [mul_neg, QuaternionAlgebra.mul_star_eq_coe_nrd, h, QuaternionAlgebra.coe_neg, QuaternionAlgebra.coe_one, neg_neg]

  set s : ℍ[ℚ, a, b] := star (x : ℍ[ℚ, a, b]) with hs
  have hsΛ : s ∈ Λ := star_mem hO x.2
  set s₁ : ℍ[ℚ, a, b] := li * s * l' with hs₁
  have hs₁Λ : s₁ ∈ Λ := hO.mul_mem (hO.mul_mem hliΛ hsΛ) hl'Λ
  have hls₁ : l' * s₁ = s * l' := by rw [hs₁, ← mul_assoc, ← mul_assoc, hli, one_mul]
  obtain ⟨s₂, hs₂Λ, hs₂⟩ := hπq'R s₁ hs₁Λ
  obtain ⟨s₃, hs₃Λ, hs₃⟩ := hπqR s₂ hs₂Λ
  refine ⟨⟨s₃, hs₃Λ⟩, ?_⟩
  show (μ : ℍ[ℚ, a, b]) * s₃ = s * (μ : ℍ[ℚ, a, b])
  rw [hμl, hll']
  calc l' * πq' * πq * s₃ = l' * πq' * (πq * s₃) := by simp only [mul_assoc]
    _ = l' * πq' * (s₂ * πq) := by rw [hs₃]
    _ = l' * (πq' * s₂) * πq := by simp only [mul_assoc]
    _ = l' * (s₁ * πq') * πq := by rw [hs₂]
    _ = (l' * s₁) * πq' * πq := by simp only [mul_assoc]
    _ = (s * l') * πq' * πq := by rw [hls₁]
    _ = s * (l' * πq' * πq) := by simp only [mul_assoc]

theorem main {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    (∃ μ : ↥Λ, (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b]))) ∧
    (∀ μ : ↥Λ, (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])) →
      ∀ x : ↥Λ, ∃ y : ↥Λ, (μ : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) = star (x : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b])) :=
  ⟨exists_mu hqq' hB Λ hΛ, fun μ hμ x => forall_conj_mem hqq' hB Λ hΛ μ hμ x⟩

end MuInput

end

open scoped Quaternion in
p2m_open "QuaternionAlgebra~nrd_mul" in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    (∃ μ : ↥Λ, (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b]))) ∧
    (∀ μ : ↥Λ, (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])) →
      ∀ x : ↥Λ, ∃ y : ↥Λ, (μ : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) = star (x : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b])) :=
  MuInput.main hqq' hB Λ hΛ

end S_CerednikDrinfeld_QM_exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder (solution)
