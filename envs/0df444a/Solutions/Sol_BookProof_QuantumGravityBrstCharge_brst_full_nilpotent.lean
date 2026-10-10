-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.brst_full_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:41.232842+00:00
-- url     : https://prove2.me/submissions/e4ecaca0-cd9c-4baf-8e5f-1609517f09e9

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.brst_full_nilpotent
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_glin_sq
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_glin_mul_Q_add_Q_mul_glin
import Theorems.Thm_BookProof_BRSTNilpotent_brst_charge_nilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterSmBrstGhost
open BookProof.QuantumGravityBrstCharge




open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}

set_option maxHeartbeats 1000000 in
theorem solution (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin n,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    brstCharge f G χ β * brstCharge f G χ β = 0 := by

  have hQ : Q f χ β * Q f χ β = 0 := brst_charge_nilpotent f χ β hCAR hf12 hjac
  have hX : glin G χ * glin G χ
      = (1 / 2 : ℝ) • ∑ a, ∑ b, ∑ e, f a b e • (G e * (χ a * χ b)) := glin_sq hCAR hCA
  have hC : glin G χ * Q f χ β + Q f χ β * glin G χ
      = ∑ d, ∑ g, ∑ h, f d g h • (G h * (χ d * χ g)) :=
    glin_mul_Q_add_Q_mul_glin hCAR hCA
  have hexp : brstCharge f G χ β * brstCharge f G χ β
      = glin G χ * glin G χ - (1 / 2 : ℝ) • (glin G χ * Q f χ β + Q f χ β * glin G χ)
        + ((1 / 2 : ℝ) * (1 / 2 : ℝ)) • (Q f χ β * Q f χ β) := by
    simp only [brstCharge, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    module
  rw [hexp, hX, hC, hQ, smul_zero, add_zero, sub_self]
