-- Prove2me | solution 1 for GL2QFT.lemma_6_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T06:48:13.193654+00:00
-- url     : https://prove2.me/submissions/2b2367ce-8b1d-4861-85c7-e81e7fd21ffe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Uniform
import Definitions.Def_GL2QFT_Circuits_Combinators
import Theorems.Thm_GL2QFT_Circuits_lemma_6_8_Fplus
import Theorems.Thm_GL2QFT_Circuits_lemma_6_8_Fmult
import Theorems.Thm_GL2QFT_Circuits_lemma_6_8_log_g
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_eq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_adjoint
import Theorems.Thm_GL2QFT_Circuits_phi_isometries

open Classical
noncomputable section

namespace GL2QFT_Lemma68_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.FieldData QAlgorithms

lemma gen_ne_zero (D : FieldData) : D.gen ≠ 0 := by
  have hh0 : D.h ≠ 0 := by
    intro h0
    have ho := D.h_order
    rw [h0, orderOf_zero] at ho
    have hq1 : 1 < D.q := D.one_lt_q
    have hq2 : 1 < D.q ^ 2 := by nlinarith
    exact Nat.sub_ne_zero_of_lt hq2 ho.symm
  unfold FieldData.gen
  exact mt Algebra.norm_eq_zero_iff.mp hh0

lemma phiLog_conjTranspose_eq_phiExp (D : FieldData) :
    (phiLog D).conjTranspose = phiExp D := by
  ext y inp
  simp only [Matrix.conjTranspose_apply, phiLog, phiExp, Matrix.of_apply]
  cases inp with
  | none =>
      by_cases hy : y = 0 <;> simp [hy]
  | some d =>
      dsimp only
      have hpow : D.gen ^ d.val ≠ 0 := pow_ne_zero _ (gen_ne_zero D)
      by_cases hy : y = D.gen ^ d.val
      · have hy0 : y ≠ 0 := hy ▸ hpow
        rw [if_pos (And.intro hy0 hy.symm), star_one, if_pos hy]
      · have hnd : ¬(y ≠ 0 ∧ D.gen ^ d.val = y) := fun h => hy h.2.symm
        rw [if_neg hnd, star_zero, if_neg hy]

end GL2QFT_Lemma68_Aux

open Classical GL2QFT GL2QFT.FieldData GL2QFT.Circuits GL2QFT_Lemma68_Aux

theorem solution :
    UniformlyImplementsOn (fun _ => True) (X := fun D => D.Fq) (Y := fun D => D.Fq)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D a => D.tagCode (.inl a)) (fun D a => D.tagCode (.inl a))
      (fun D => fun y x => isqrt D.q * D.psi (x * y)) ∧
    UniformlyImplementsOn (fun _ => True) (X := fun D => Option D.Lab) (Y := fun D => Option D.Lab)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D c => D.tagCode (D.xEmb c)) (fun D c => D.tagCode (D.xEmb c))
      (fun D => fun out inp =>
        match out, inp with
        | none, none => 1
        | some α, some d => isqrt (D.q - 1) * D.chi α (D.gen ^ d.val)
        | _, _ => 0) ∧
    UniformlyImplementsOn (fun _ => True) (X := fun D => Option D.Lab) (Y := fun D => D.Fq)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D c => D.tagCode (D.xEmb c)) (fun D a => D.tagCode (.inl a))
      (fun D => fun y inp =>
        match inp with
        | none => if y = 0 then 1 else 0
        | some d => if y = D.gen ^ d.val then 1 else 0) ∧
    UniformlyImplementsOn (fun _ => True) (X := fun D => D.Fq) (Y := fun D => Option D.Lab)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D a => D.tagCode (.inl a)) (fun D c => D.tagCode (D.xEmb c))
      (fun D => fun out a =>
        match out with
        | none => if a = 0 then 1 else 0
        | some d => if a ≠ 0 ∧ D.gen ^ d.val = a then 1 else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine uniformlyImplementsOn_eq lemma_6_8_Fplus fun D _ => ?_
    ext y x
    rfl
  · refine uniformlyImplementsOn_eq lemma_6_8_Fmult fun D _ => ?_
    ext out inp
    rfl
  · have hadj : UniformlyImplementsOn (fun _ => True)
        (fun D c => D.tagCode (D.xEmb c)) (fun D a => D.tagCode (.inl a))
        (fun D => (phiLog D).conjTranspose) :=
      uniformlyImplementsOn_adjoint lemma_6_8_log_g fun D _ => by
        convert (phi_isometries D).2.2.2
    refine uniformlyImplementsOn_eq hadj fun D _ => ?_
    rw [phiLog_conjTranspose_eq_phiExp]
    ext y inp
    rfl
  · refine uniformlyImplementsOn_eq lemma_6_8_log_g fun D _ => ?_
    ext out a
    rfl
