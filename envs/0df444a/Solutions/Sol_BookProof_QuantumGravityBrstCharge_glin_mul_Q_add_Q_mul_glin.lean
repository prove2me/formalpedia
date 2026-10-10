-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.glin_mul_Q_add_Q_mul_glin
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:39.663339+00:00
-- url     : https://prove2.me/submissions/bd37efad-b8cc-4095-b81e-87fc673ef798

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.glin_mul_Q_add_Q_mul_glin
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_chi_comm_pair
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.QuantumGravityBrstCharge




open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}

set_option maxHeartbeats 1000000 in
theorem solution (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) :
    glin G χ * Q f χ β + Q f χ β * glin G χ
      = ∑ d, ∑ g, ∑ h, f d g h • (G h * (χ d * χ g)) := by

  have hterm : ∀ a d g h : Fin n,
      (G a * χ a) * (f d g h • (χ d * χ g * β h)) + (f d g h • (χ d * χ g * β h)) * (G a * χ a)
        = f d g h • ((if h = a then G a * (χ d * χ g) else 0)) := by
    intro a d g h
    have hbeta : β h * χ a = (if h = a then 1 else 0) - χ a * β h :=
      eq_sub_of_add_eq (hCAR.betachi h a)
    have hL : (G a * χ a) * (f d g h • (χ d * χ g * β h))
        = f d g h • (G a * (χ a * (χ d * χ g) * β h)) := by
      rw [mul_smul_comm]
      congr 1
      simp only [mul_assoc]
    have hR : (f d g h • (χ d * χ g * β h)) * (G a * χ a)
        = f d g h • (G a * ((χ d * χ g) * (β h * χ a))) := by
      rw [smul_mul_assoc]
      congr 1
      calc (χ d * χ g * β h) * (G a * χ a) = (χ d * χ g) * ((β h * G a) * χ a) := by
            simp only [mul_assoc]
        _ = (χ d * χ g) * ((G a * β h) * χ a) := by rw [← hCA.comm_beta a h]
        _ = G a * ((χ d * χ g) * (β h * χ a)) := by
            have h1 : (χ d * χ g) * G a = G a * (χ d * χ g) := by
              calc (χ d * χ g) * G a = χ d * (χ g * G a) := by rw [mul_assoc]
                _ = χ d * (G a * χ g) := by rw [← hCA.comm_chi a g]
                _ = (χ d * G a) * χ g := by rw [mul_assoc]
                _ = (G a * χ d) * χ g := by rw [← hCA.comm_chi a d]
                _ = G a * (χ d * χ g) := by rw [mul_assoc]
            calc (χ d * χ g) * ((G a * β h) * χ a)
                = ((χ d * χ g) * G a) * (β h * χ a) := by simp only [mul_assoc]
              _ = (G a * (χ d * χ g)) * (β h * χ a) := by rw [h1]
              _ = G a * ((χ d * χ g) * (β h * χ a)) := by simp only [mul_assoc]
    rw [hL, hR, ← smul_add]
    congr 1
    rw [hbeta, chi_comm_pair hCAR a d g]
    by_cases hh : h = a
    · simp only [if_pos hh]
      noncomm_ring
    · simp only [if_neg hh]
      noncomm_ring
  have hL : glin G χ * Q f χ β = ∑ a, ∑ d, ∑ g, ∑ h,
      (G a * χ a) * (f d g h • (χ d * χ g * β h)) := by
    unfold glin Q
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.mul_sum]
  have hR : Q f χ β * glin G χ = ∑ a, ∑ d, ∑ g, ∑ h,
      (f d g h • (χ d * χ g * β h)) * (G a * χ a) := by
    have step : Q f χ β * glin G χ = ∑ d, ∑ g, ∑ h, ∑ a,
        (f d g h • (χ d * χ g * β h)) * (G a * χ a) := by
      unfold glin Q
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum]
    rw [step]
    calc (∑ d, ∑ g, ∑ h, ∑ a, (f d g h • (χ d * χ g * β h)) * (G a * χ a))
        = ∑ d, ∑ g, ∑ a, ∑ h, (f d g h • (χ d * χ g * β h)) * (G a * χ a) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun g _ => Finset.sum_comm
      _ = ∑ d, ∑ a, ∑ g, ∑ h, (f d g h • (χ d * χ g * β h)) * (G a * χ a) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = ∑ a, ∑ d, ∑ g, ∑ h, (f d g h • (χ d * χ g * β h)) * (G a * χ a) := Finset.sum_comm
  have hsum : glin G χ * Q f χ β + Q f χ β * glin G χ
      = ∑ a, ∑ d, ∑ g, ∑ h, f d g h • ((if h = a then G a * (χ d * χ g) else 0)) := by
    rw [hL, hR, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => hterm a d g h
  rw [hsum]
  calc (∑ a, ∑ d, ∑ g, ∑ h, f d g h • ((if h = a then G a * (χ d * χ g) else 0)))
      = ∑ d, ∑ a, ∑ g, ∑ h, f d g h • ((if h = a then G a * (χ d * χ g) else 0)) :=
        Finset.sum_comm
    _ = ∑ d, ∑ g, ∑ a, ∑ h, f d g h • ((if h = a then G a * (χ d * χ g) else 0)) :=
        Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ g, ∑ h, ∑ a, f d g h • ((if h = a then G a * (χ d * χ g) else 0)) :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun g _ => Finset.sum_comm
    _ = ∑ d, ∑ g, ∑ h, f d g h • (G h * (χ d * χ g)) := by
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun g _ =>
          Finset.sum_congr rfl fun h _ => ?_
        simp [Finset.sum_ite_eq]
