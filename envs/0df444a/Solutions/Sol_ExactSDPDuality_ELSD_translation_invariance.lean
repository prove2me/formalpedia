-- Prove2me | solution 1 for ExactSDPDuality.ELSD.translation_invariance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:59:01.427304+00:00
-- url     : https://prove2.me/submissions/f2e97ae1-64b5-447c-9c8b-c1a4e21ccb9d

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

theorem aux_ti_frob_Qaff {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    frob (Qaff Q0 Q x) X = frob Q0 X - ∑ i, x i * frob X (Q i) := by
  unfold frob Qaff Qhat
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring

theorem aux_ti_qsharp {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    QsharpZero (Qaff Q0 Q x) Q X ↔ QsharpZero Q0 Q X := by
  unfold QsharpZero
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 : ∀ i, frob X (Q i) = 0 := fun i => congrFun h2 i
    rw [aux_ti_frob_Qaff] at h1
    simpa [h3] using h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 : ∀ i, frob X (Q i) = 0 := fun i => congrFun h2 i
    rw [aux_ti_frob_Qaff]
    simpa [h3] using h1

theorem aux_ti_cseq {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) (k : ℕ)
    (U W : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    IsCSeq (Qaff Q0 Q x) Q k U W ↔ IsCSeq Q0 Q k U W := by
  unfold IsCSeq
  simp only [aux_ti_qsharp]

end ExactSDPDuality.ELSD

open ExactSDPDuality.ELSD
open Matrix

theorem solution {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (xbar : Fin m → ℝ) (hx : xbar ∈ feasibleSet Q0 Q) (k : ℕ) :
    (∀ U W : ℕ → Matrix (Fin n) (Fin n) ℝ,
        IsCSeq (Qaff Q0 Q xbar) Q k U W ↔ IsCSeq Q0 Q k U W) ∧
      Uset (Qaff Q0 Q xbar) Q k = Uset Q0 Q k ∧
      Wset (Qaff Q0 Q xbar) Q k = Wset Q0 Q k := by
  refine ⟨fun U W => aux_ti_cseq Q0 Q xbar k U W, ?_, ?_⟩
  · ext X
    simp only [Uset, Set.mem_ofPred_eq, aux_ti_cseq]
  · ext X
    simp only [Wset, Set.mem_ofPred_eq, aux_ti_cseq]
