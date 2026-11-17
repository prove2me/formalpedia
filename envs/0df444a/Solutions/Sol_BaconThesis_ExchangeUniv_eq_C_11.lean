-- Prove2me | solution 1 for BaconThesis.ExchangeUniv.eq_C_11
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:28:17.901766+00:00
-- url     : https://prove2.me/submissions/c94bd083-fd75-4474-a2b8-19f53597d235

import Mathlib
import Definitions.Def_BaconThesis_ExchangeUniv_collS
import Definitions.Def_BaconThesis_Collective_exchange

open scoped Matrix

namespace BaconThesis.ExchangeUniv.SolC11

lemma exchange_mulVec {n : ℕ} (i j : Fin n) (f : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2) :
    (BaconThesis.Collective.exchange i j *ᵥ f) x = f (x ∘ Equiv.swap i j) := by
  have h : ∀ y : Fin n → Fin 2, (x = y ∘ Equiv.swap i j) ↔ (x ∘ Equiv.swap i j = y) := by
    intro y
    constructor
    · rintro rfl
      ext k
      simp
    · rintro rfl
      ext k
      simp
  simp only [Matrix.mulVec, dotProduct, BaconThesis.Collective.exchange, h, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The real coefficient identities behind (C.11). -/
lemma coeffs (A B C : ℝ) (hB : 0 < B) (hC : 0 < C) (hA : A ^ 2 = B ^ 2 - 1) (hC2 : C ^ 2 = B ^ 2 + 1) :
    (C * B)⁻¹ = 1 / B ^ 2 * (B / C) ∧
    -(B / C) = -(1 / B ^ 2) * (C * B)⁻¹ + A * C / B ^ 2 * -(A / B) ∧
    A / (B * C) = -(1 / B ^ 2) * (A / (B * C)) + A * C / B ^ 2 * B⁻¹ ∧
    -(A / B) = A * C / B ^ 2 * -(B / C) ∧
    (0 : ℝ) = A * C / B ^ 2 * (C * B)⁻¹ + 1 / B ^ 2 * -(A / B) ∧
    B⁻¹ = A * C / B ^ 2 * (A / (B * C)) + 1 / B ^ 2 * B⁻¹ := by
  have hB' := hB.ne'
  have hC' := hC.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> (try simp only [hA, hC2]) <;> ring

end BaconThesis.ExchangeUniv.SolC11

open BaconThesis.ExchangeUniv BaconThesis.ExchangeUniv.SolC11 in
theorem solution (m : ℕ) (J : ℝ) (hJ : 0 ≤ J) (u v w : (Fin m → Fin 2) → ℂ) :
    let a : Fin (m + 2) := Fin.castSucc (Fin.last m)
    let b : Fin (m + 2) := Fin.last (m + 1)
    let ext : ((Fin m → Fin 2) → ℂ) → Fin 2 → Fin 2 → (Fin (m + 2) → Fin 2) → ℂ :=
      fun y s t x => if x a = s ∧ x b = t then y (fun k => x (Fin.castSucc (Fin.castSucc k))) else 0
    let Sm : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ := collS m 0 - Complex.I • collS m 1
    let c : ℝ → ℂ := fun r => ((Real.sqrt r : ℝ) : ℂ)
    let u' := (c (2 * J))⁻¹ • (Sm *ᵥ u)
    let v' := (c (2 * J + 2))⁻¹ • (Sm *ᵥ v)
    let v'' := (c (2 * (2 * J + 1)))⁻¹ • (Sm *ᵥ v')
    let TT := c ((2 * J + 1) / (2 * J + 3)) • ext v 1 1
      - c ((2 * J + 1) / ((2 * J + 2) * (2 * J + 3))) • (ext v' 0 1 + ext v' 1 0)
      + c (2 / ((2 * J + 2) * (2 * J + 3))) • ext v'' 0 0
    let BT := -c ((2 * J + 1) / (2 * J + 2)) • ext u 0 1
      + (c ((2 * J + 2) * (2 * J + 1)))⁻¹ • ext u 1 0
      + c (2 * J / ((2 * J + 1) * (2 * J + 2))) • ext u' 0 0
    let TB := -c (2 * J / (2 * J + 1)) • ext u 1 0 + (c (2 * J + 1))⁻¹ • ext u' 0 0
    let BB := ext w 0 0
    let θ := Real.arctan (2 * Real.sqrt (J * (J + 1)))
    let E := BaconThesis.Collective.exchange a b
    E *ᵥ TT = TT ∧
    E *ᵥ BT = (-(Real.cos θ : ℂ)) • BT + (Real.sin θ : ℂ) • TB ∧
    E *ᵥ TB = (Real.sin θ : ℂ) • BT + (Real.cos θ : ℂ) • TB ∧
    E *ᵥ BB = BB := by
  intro a b ext Sm c u' v' v'' TT BT TB BB θ E
  have hE : ∀ y s t, E *ᵥ ext y s t = ext y t s := by
    intro y s t
    funext x
    rw [exchange_mulVec]
    have h1 : (x ∘ Equiv.swap a b) a = x b := by simp
    have h2 : (x ∘ Equiv.swap a b) b = x a := by simp
    have h3 : ∀ k : Fin m, (x ∘ Equiv.swap a b) (Fin.castSucc (Fin.castSucc k)) =
        x (Fin.castSucc (Fin.castSucc k)) := by
      intro k
      simp only [Function.comp]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · intro h
        have := congrArg Fin.val h
        simp [a] at this
        omega
      · intro h
        have := congrArg Fin.val h
        simp [b] at this
        omega
    simp only [ext, h1, h2, h3, and_comm]
  -- real coefficients
  set A := Real.sqrt (2 * J) with hAdef
  set B := Real.sqrt (2 * J + 1) with hBdef
  set C := Real.sqrt (2 * J + 2) with hCdef
  have hB : 0 < B := Real.sqrt_pos.mpr (by linarith)
  have hC : 0 < C := Real.sqrt_pos.mpr (by linarith)
  have hA2 : A ^ 2 = 2 * J := Real.sq_sqrt (by linarith)
  have hB2 : B ^ 2 = 2 * J + 1 := Real.sq_sqrt (by linarith)
  have hC2 : C ^ 2 = 2 * J + 2 := Real.sq_sqrt (by linarith)
  have hden : Real.sqrt (1 + (2 * Real.sqrt (J * (J + 1))) ^ 2) = B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hB2,
      show 1 + 2 ^ 2 * (J * (J + 1)) = (2 * J + 1) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have hnum : 2 * Real.sqrt (J * (J + 1)) = A * C := by
    have h : A * C = Real.sqrt (2 ^ 2 * (J * (J + 1))) := by
      rw [hAdef, hCdef, ← Real.sqrt_mul (by linarith)]
      congr 1
      ring
    rw [h, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hcos : Real.cos θ = 1 / B ^ 2 := by rw [Real.cos_arctan, hden]
  have hsin : Real.sin θ = A * C / B ^ 2 := by rw [Real.sin_arctan, hden, hnum]
  have hp : Real.sqrt ((2 * J + 1) / (2 * J + 2)) = B / C := Real.sqrt_div (by linarith) _
  have hq : Real.sqrt ((2 * J + 2) * (2 * J + 1)) = C * B := Real.sqrt_mul (by linarith) _
  have hr : Real.sqrt (2 * J / ((2 * J + 1) * (2 * J + 2))) = A / (B * C) := by
    rw [Real.sqrt_div (by linarith), Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * J + 1)]
  have hs : Real.sqrt (2 * J / (2 * J + 1)) = A / B := Real.sqrt_div (by linarith) _
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ :=
    coeffs A B C hB hC (by rw [hA2, hB2]; ring) (by rw [hC2, hB2]; ring)
  have cast : ∀ {x y : ℝ}, x = y → (x : ℂ) = (y : ℂ) := fun h => by rw [h]
  have k1' := cast k1
  have k2' := cast k2
  have k3' := cast k3
  have k4' := cast k4
  have k5' := cast k5
  have k6' := cast k6
  push_cast at k1' k2' k3' k4' k5' k6'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [TT, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hE]
    rw [add_comm (ext v' 1 0)]
  · simp only [BT, TB, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, hE, neg_smul]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, c, hp, hq, hr, hs, hcos,
      hsin]
    push_cast
    linear_combination k1' * ext u 0 1 x + k2' * ext u 1 0 x + k3' * ext u' 0 0 x
  · simp only [BT, TB, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, hE, neg_smul]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, c, hp, hq, hr, hs, hcos,
      hsin]
    push_cast
    linear_combination k4' * ext u 0 1 x + k5' * ext u 1 0 x + k6' * ext u' 0 0 x
  · exact hE w 0 0
