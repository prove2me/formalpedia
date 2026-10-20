-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.qgBRST_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:52:40.400307+00:00
-- url     : https://prove2.me/submissions/8daacf8b-e216-49c0-9b67-f2c4f7a6bf88

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.qgBRST_nilpotent
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_prod
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_sub
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_contract_left
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_contract_right
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_sum4_sub_distrib
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_sum4_swap_blocks
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_elemGen_bracket
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_qgGhostCar
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_sub
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_mul
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_smul
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_sum
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_ghostOp_comm
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_smul_sum
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_brst_full_nilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}
variable {α : Type*}
theorem linGenBracketAux {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    linGen A * linGen B - linGen B * linGen A = linGen (A * B - B * A) := by
  have hswap : (∑ j, ∑ k, ∑ l, ∑ m, (B j k * A l m) • (elemGen j k * elemGen l m))
      = ∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (elemGen l m * elemGen j k) := by
    have h := sum4_swap_blocks (fun l m j k => (A j k * B l m) • (elemGen l m * elemGen j k))
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm (B j k)]
  rw [linGen_prod, linGen_prod, hswap, sum4_sub_distrib, linGen_sub, ← linGen_contract_left,
    ← linGen_contract_right, sum4_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  have := congrArg (fun x => (A j k * B l m) • x) (elemGen_bracket j k l m)
  simpa only [smul_sub] using this

theorem solution (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ)
    (f : Fin 19 → Fin 19 → Fin 19 → ℝ)
    (hclose : ∀ a b, M a * M b - M b * M a = ∑ e, f a b e • M e)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin 19,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    qgBRST M f * qgBRST M f = 0 := by
  unfold qgBRST
  refine brst_full_nilpotent qgGhostCar ⟨fun a b => bosOp_ghostOp_comm _ _,
    fun a b => bosOp_ghostOp_comm _ _, fun a b => ?_⟩ hf12 hjac
  unfold qgConstraint
  rw [← bosOp_mul, ← bosOp_mul, ← bosOp_sub, linGenBracketAux, hclose, linGen_smul_sum, bosOp_sum]
  simp only [bosOp_smul]
