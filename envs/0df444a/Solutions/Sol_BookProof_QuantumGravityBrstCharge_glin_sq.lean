-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.glin_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:38.314067+00:00
-- url     : https://prove2.me/submissions/6b327dfc-83c7-485c-af4b-ae81ff407f0f

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.glin_sq
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_chi_anticomm
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.QuantumGravityBrstCharge




open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}

set_option maxHeartbeats 1000000 in
theorem solution (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) :
    glin G χ * glin G χ = (1 / 2 : ℝ) • ∑ a, ∑ b, ∑ e, f a b e • (G e * (χ a * χ b)) := by

  have hexp : glin G χ * glin G χ = ∑ a, ∑ b, (G a * G b) * (χ a * χ b) := by
    unfold glin
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    calc (G a * χ a) * (G b * χ b) = G a * ((χ a * G b) * χ b) := by
          simp only [mul_assoc]
      _ = G a * ((G b * χ a) * χ b) := by rw [← hCA.comm_chi b a]
      _ = (G a * G b) * (χ a * χ b) := by simp only [mul_assoc]
  have hswap : ∑ a, ∑ b, (G a * G b) * (χ a * χ b)
      = -∑ a, ∑ b, (G b * G a) * (χ a * χ b) := by
    rw [Finset.sum_comm (f := fun a b => (G a * G b) * (χ a * χ b))]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [chi_anticomm hCAR b a, mul_neg]
  have htwo : (glin G χ * glin G χ) + (glin G χ * glin G χ)
      = ∑ a, ∑ b, ∑ e, f a b e • (G e * (χ a * χ b)) := by
    rw [hexp]
    nth_rewrite 2 [hswap]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← neg_mul, ← add_mul, ← sub_eq_add_neg, hCA.bracket a b, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by rw [smul_mul_assoc]
  have h2 : ((2 : ℝ)) • (glin G χ * glin G χ)
      = ∑ a, ∑ b, ∑ e, f a b e • (G e * (χ a * χ b)) := by
    rw [two_smul]; exact htwo
  calc glin G χ * glin G χ = (1 / 2 : ℝ) • ((2 : ℝ) • (glin G χ * glin G χ)) := by
        rw [smul_smul]; norm_num
    _ = (1 / 2 : ℝ) • ∑ a, ∑ b, ∑ e, f a b e • (G e * (χ a * χ b)) := by rw [h2]
