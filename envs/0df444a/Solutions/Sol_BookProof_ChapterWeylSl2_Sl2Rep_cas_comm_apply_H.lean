-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.cas_comm_apply_H
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:28:54.215476+00:00
-- url     : https://prove2.me/submissions/1bcfec17-a645-43ec-b97a-b865504e8152

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.cas_comm_apply_H
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}
open BookProof.ChapterWeylSl2.Sl2Rep

theorem solution(v : V) : R.cas (R.H v) = R.H (R.cas v) := by
  have h1 : R.H * R.E = 2 • R.E + R.E * R.H := sub_eq_iff_eq_add.mp R.he
  have h2 : R.H * R.F = -(2 • R.F) + R.F * R.H := sub_eq_iff_eq_add.mp R.hf
  have hEF : R.H * (R.E * R.F) = R.E * R.F * R.H := by
    rw [← mul_assoc, h1, add_mul, mul_assoc R.E R.H R.F, h2]
    simp only [mul_add, mul_neg, smul_mul_assoc, mul_smul_comm, mul_assoc]
    abel
  have hFE : R.H * (R.F * R.E) = R.F * R.E * R.H := by
    rw [← mul_assoc, h2, add_mul, mul_assoc R.F R.H R.E, h1]
    simp only [mul_add, neg_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    abel
  have key : R.cas * R.H = R.H * R.cas := by
    show (2 • (R.E * R.F + R.F * R.E) + R.H * R.H) * R.H
        = R.H * (2 • (R.E * R.F + R.F * R.E) + R.H * R.H)
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    rw [hEF, hFE]
    simp only [mul_assoc]
  exact LinearMap.congr_fun key v
