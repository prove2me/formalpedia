-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.linGen_bracket
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:51:12.930142+00:00
-- url     : https://prove2.me/submissions/8c153620-f199-40e4-a8e7-3223096d9509

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.linGen_bracket
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

theorem solution (A B : Matrix (Fin d) (Fin d) ℝ) :
    linGen A * linGen B - linGen B * linGen A = linGen (A * B - B * A) := by
  exact linGenBracketAux A B
