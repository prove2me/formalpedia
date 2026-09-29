-- Prove2me | solution 1 for ExactSDPDuality.ELSD.lemma13
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:02:42.665955+00:00
-- url     : https://prove2.me/submissions/6ada0025-d2fc-432c-bfab-b3399ad50a5e

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

theorem aux_l13_frob_nonneg {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ frob A B := by
  have h := (hA.hadamard hB).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  simpa [frob, dotProduct, mulVec, hadamard] using h

theorem aux_l13_dot_Qstar {n m : ℕ} (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ Qstar Q U = frob U (Qhat Q x) := by
  simp only [dotProduct, Qstar, frob, Qhat, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem aux_l13_frob_sub {n : ℕ} (U A B : Matrix (Fin n) (Fin n) ℝ) :
    frob U (A - B) = frob U A - frob U B := by
  simp [frob, mul_sub, Finset.sum_sub_distrib]

theorem aux_l13_frob_smul_left {n : ℕ} (t : ℝ) (U A : Matrix (Fin n) (Fin n) ℝ) :
    frob (t • U) A = t * frob U A := by
  simp [frob, Finset.mul_sum, mul_assoc]

theorem aux_l13_frob_add_left {n : ℕ} (U V A : Matrix (Fin n) (Fin n) ℝ) :
    frob (U + V) A = frob U A + frob V A := by
  simp [frob, add_mul, Finset.sum_add_distrib]

theorem aux_l13_frob_vecMulVec {n : ℕ} (v : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    frob (vecMulVec v v) A = v ⬝ᵥ (A *ᵥ v) := by
  simp only [frob, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem aux_l13_Qhat_zero {n m : ℕ} (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Qhat Q 0 = 0 := by
  simp [Qhat]

theorem aux_l13_Qhat_smul {n m : ℕ} (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (x : Fin m → ℝ) : Qhat Q (t • x) = t • Qhat Q x := by
  simp [Qhat, Finset.smul_sum, smul_smul]

theorem aux_l13_polar_closed {m : ℕ} (G : Set (Fin m → ℝ)) : IsClosed (polar G) := by
  have : polar G = ⋂ x ∈ G, {y : Fin m → ℝ | x ⬝ᵥ y ≤ 1} := by
    ext y; simp [polar]
  rw [this]
  refine isClosed_biInter fun x _ => ?_
  exact isClosed_le (continuous_const.dotProduct continuous_id) continuous_const

theorem aux_l13_algPolar_convex {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) : Convex ℝ (algPolar Q0 Q) := by
  rintro _ ⟨U1, h1, h1', rfl⟩ _ ⟨U2, h2, h2', rfl⟩ a b ha hb hab
  refine ⟨a • U1 + b • U2, (h1.smul ha).add (h2.smul hb), ?_, ?_⟩
  · rw [aux_l13_frob_add_left, aux_l13_frob_smul_left, aux_l13_frob_smul_left]
    nlinarith
  · funext i
    simp only [Qstar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [aux_l13_frob_add_left, aux_l13_frob_smul_left, aux_l13_frob_smul_left]

end ExactSDPDuality.ELSD

open Matrix
open ExactSDPDuality.ELSD

theorem solution {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q) :
    polar (feasibleSet Q0 Q) = closure (algPolar Q0 Q) := by
  have hQ0psd : Q0.PosSemidef := by
    have := h0
    simp only [feasibleSet, Set.mem_ofPred_eq, Qaff, aux_l13_Qhat_zero, sub_zero] at this
    exact this
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hyc
    obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point
      (aux_l13_algPolar_convex Q0 Q).closure isClosed_closure hyc
    have h0mem : (0 : Fin m → ℝ) ∈ algPolar Q0 Q :=
      ⟨0, PosSemidef.zero, by simp [frob], by funext i; simp [Qstar, frob]⟩
    have hu0 : 0 < u := by
      have := hf 0 (subset_closure h0mem)
      simpa using this
    set z : Fin m → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hz
    have hfz : ∀ w, f w = w ⬝ᵥ z := by
      intro w
      rw [show f w = (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) w from rfl, LinearMap.pi_apply_eq_sum_univ]
      simp [dotProduct, hz]
    set x : Fin m → ℝ := u⁻¹ • z with hx
    have hxG : x ∈ feasibleSet Q0 Q := by
      simp only [feasibleSet, Set.mem_ofPred_eq, Qaff]
      refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
      · refine IsHermitian.ext fun i j => ?_
        simp only [Qhat, star_trivial, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
          smul_eq_mul]
        rw [hQ0.apply]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [(hQ k).apply]
      · intro v
        rw [star_trivial]
        by_contra hneg
        push Not at hneg
        set a := v ⬝ᵥ (Q0 *ᵥ v) with ha
        set b := frob (vecMulVec v v) (Qhat Q z) with hb
        have ha0 : 0 ≤ a := by simpa using hQ0psd.dotProduct_mulVec_nonneg v
        have hkey : v ⬝ᵥ ((Q0 - Qhat Q x) *ᵥ v) = a - u⁻¹ * b := by
          rw [← aux_l13_frob_vecMulVec, aux_l13_frob_sub, aux_l13_frob_vecMulVec, hx,
            aux_l13_Qhat_smul]
          simp only [frob, Matrix.smul_apply, smul_eq_mul, hb, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
          ring
        rw [hkey] at hneg
        have hbua : u * a < b := by
          have : a < u⁻¹ * b := by linarith
          have := mul_lt_mul_of_pos_left this hu0
          rwa [← mul_assoc, mul_inv_cancel₀ hu0.ne', one_mul] at this
        have hbpos : 0 < b := by nlinarith
        set t : ℝ := u / b with ht
        have ht0 : 0 ≤ t := div_nonneg hu0.le hbpos.le
        have hmem : Qstar Q (t • vecMulVec v v) ∈ algPolar Q0 Q := by
          refine ⟨t • vecMulVec v v, (posSemidef_vecMulVec_self_star v).smul ht0, ?_, rfl⟩
          rw [aux_l13_frob_smul_left, aux_l13_frob_vecMulVec, ← ha, ht, div_mul_eq_mul_div,
            div_le_one hbpos]
          linarith
        have hlt := hf _ (subset_closure hmem)
        rw [hfz, dotProduct_comm, aux_l13_dot_Qstar, aux_l13_frob_smul_left, ← hb, ht,
          div_mul_cancel₀ u hbpos.ne'] at hlt
        exact lt_irrefl _ hlt
    have hxy := hy x hxG
    rw [hfz, dotProduct_comm] at hu
    rw [hx, smul_dotProduct, smul_eq_mul] at hxy
    have : z ⬝ᵥ y ≤ u := by
      have := mul_le_mul_of_nonneg_left hxy hu0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hu0.ne', one_mul, mul_one] at this
    linarith
  · refine closure_minimal ?_ (aux_l13_polar_closed _)
    rintro _ ⟨U, hU, hU1, rfl⟩ x hx
    rw [aux_l13_dot_Qstar]
    have hQx : (Qaff Q0 Q x).PosSemidef := hx
    have h1 := aux_l13_frob_nonneg hU hQx
    have h2 : Qhat Q x = Q0 - Qaff Q0 Q x := by simp [Qaff]
    rw [h2, aux_l13_frob_sub]
    linarith
