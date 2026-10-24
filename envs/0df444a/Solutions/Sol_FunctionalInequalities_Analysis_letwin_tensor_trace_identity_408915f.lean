-- Prove2me | solution 1 for FunctionalInequalities.Analysis.letwin_tensor_trace_identity_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:41:28.594875+00:00
-- url     : https://prove2.me/submissions/5a17f941-6954-41fb-832f-5915dc242ab5

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section TensorComparison
private lemma FunctionalInequalities.Analysis.letwin_sum_four_swap {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ i, ∑ j, f a b i j) =
      ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  classical
  have h :
      (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
        f p.1 p.2 q.1 q.2) =
      ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n,
        f p.1 p.2 q.1 q.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h
private lemma FunctionalInequalities.Analysis.letwin_trace_contract {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) :
    (M * N).trace = ∑ i, ∑ j, M i j * N i j := by
  classical
  change (∑ i, ∑ j, M i j * N j i) = ∑ i, ∑ j, M i j * N i j
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hm : M j i = M i j :=
    congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hM
  rw [hm]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution {n : ℕ}
    (G M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M)
    (T : Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ a b c, T a b c = T a c b) :
    (∑ a, ∑ c, G a c *
      (M * Matrix.of (fun i j => T a i j) * G *
        Matrix.of (fun i j => T c i j)).trace) =
      ∑ i, ∑ j, M i j *
        ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * T a b i * T c d j := by
  classical
  let V : Fin n → Matrix (Fin n) (Fin n) ℝ :=
    fun a => Matrix.of (fun i j => T a i j)
  change (∑ a, ∑ c, G a c * (M * V a * G * V c).trace) = _
  have entry (i j : Fin n) :
      (∑ a, ∑ c, G a c * (V a * G * V c) i j) =
        ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * T a b i * T c d j := by
    calc
      (∑ a, ∑ c, G a c * (V a * G * V c) i j) =
          ∑ a, ∑ c, ∑ b, ∑ d,
            G a c * G b d * T a b i * T c d j := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro c _
        change G a c * (∑ d, (∑ b, T a i b * G b d) * T c d j) = _
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro d _
        rw [hT a i b]
        ring
      _ = ∑ a, ∑ b, ∑ c, ∑ d,
          G a c * G b d * T a b i * T c d j := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
  have ht (a c : Fin n) :
      (M * V a * G * V c).trace =
        ∑ i, ∑ j, M i j * (V a * G * V c) i j := by
    calc
      (M * V a * G * V c).trace = (M * (V a * G * V c)).trace := by
        simp only [Matrix.mul_assoc]
      _ = ∑ i, ∑ j, M i j * (V a * G * V c) i j :=
        letwin_trace_contract M _ hM
  calc
    (∑ a, ∑ c, G a c * (M * V a * G * V c).trace) =
        ∑ a, ∑ c, ∑ i, ∑ j,
          M i j * (G a c * (V a * G * V c) i j) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      rw [ht a c]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, ∑ a, ∑ c,
        M i j * (G a c * (V a * G * V c) i j) :=
      letwin_sum_four_swap _
    _ = ∑ i, ∑ j, M i j *
        (∑ a, ∑ c, G a c * (V a * G * V c) i j) := by
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ j, M i j *
        ∑ a, ∑ b, ∑ c, ∑ d, G a c * G b d * T a b i * T c d j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [entry i j]
