-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.slot_bound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:52:58.697989+00:00
-- url     : https://prove2.me/submissions/891917b9-6032-4bce-b048-db6212f5f4e6

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.CoordinateTensor
variable {n r : ℕ}
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities.Analysis.CoordinateTensor in
 lemma solution (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
    (T : (Fin r → Fin n) → ℝ) (s : Fin r) :
    ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 ≤
      8 * ∑ J, T J ^ 2 := by
  classical
  cases r with
  | zero =>
      exact Fin.elim0 s
  | succ q =>
      let e := Fin.insertNthEquiv (fun _ : Fin (q + 1) => Fin n) s
      have heval (a : Fin n) (K : Fin q → Fin n) :
          e (a, K) s = a := by
        simp [e, Fin.insertNthEquiv_apply, Fin.insertNth, Fin.succAboveCases]
      have hupd (a b : Fin n) (K : Fin q → Fin n) :
          Function.update (e (a, K)) s b = e (b, K) := by
        funext j
        by_cases hj : j = s
        · subst j
          simp [e, Fin.insertNthEquiv_apply, Fin.insertNth, Fin.succAboveCases]
        · simp [Function.update, hj, e, Fin.insertNthEquiv_apply, Fin.insertNth,
            Fin.succAboveCases]
      have hri (i : Fin n) :
          ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
            ∑ x : Fin n × (Fin q → Fin n),
              (∑ k, H i x.1 k * T (e (k, x.2))) ^ 2 := by
        symm
        refine Fintype.sum_equiv (M := ℝ) e
          (fun x : Fin n × (Fin q → Fin n) =>
            (∑ k, H i x.1 k * T (e (k, x.2))) ^ 2)
          (fun J => (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2) ?_
        rintro ⟨a, K⟩
        simp only [heval, hupd]
      have hsum :
          ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
            ∑ K : Fin q → Fin n, ∑ i, ∑ a,
              (∑ k, H i a k * T (e (k, K))) ^ 2 := by
        calc
          ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
              ∑ i, ∑ x : Fin n × (Fin q → Fin n),
                (∑ k, H i x.1 k * T (e (k, x.2))) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hri i
          _ = ∑ i, ∑ a, ∑ K : Fin q → Fin n,
                (∑ k, H i a k * T (e (k, K))) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                exact Fintype.sum_prod_type' (γ := ℝ) (α₁ := Fin n)
                  (α₂ := Fin q → Fin n)
                  (fun a K => (∑ k, H i a k * T (e (k, K))) ^ 2)
          _ = ∑ i, ∑ K : Fin q → Fin n, ∑ a,
                (∑ k, H i a k * T (e (k, K))) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_comm]
          _ = ∑ K : Fin q → Fin n, ∑ i, ∑ a,
                (∑ k, H i a k * T (e (k, K))) ^ 2 := by
                rw [Finset.sum_comm]
      have hpoint (K : Fin q → Fin n) :
          ∑ i, ∑ a, (∑ k, H i a k * T (e (k, K))) ^ 2 ≤
            8 * ∑ a, T (e (a, K)) ^ 2 := by
        simpa using h8 (fun b => T (e (b, K)))
      have heq :
          ∑ K : Fin q → Fin n, ∑ a, T (e (a, K)) ^ 2 =
            ∑ J, T J ^ 2 := by
        calc
          ∑ K : Fin q → Fin n, ∑ a, T (e (a, K)) ^ 2 =
              ∑ a, ∑ K : Fin q → Fin n, T (e (a, K)) ^ 2 := by
                rw [Finset.sum_comm]
          _ = ∑ x : Fin n × (Fin q → Fin n), T (e x) ^ 2 := by
                symm
                exact Fintype.sum_prod_type' (γ := ℝ) (α₁ := Fin n)
                  (α₂ := Fin q → Fin n)
                  (fun a K => T (e (a, K)) ^ 2)
          _ = ∑ J, T J ^ 2 := by
                exact Fintype.sum_equiv (M := ℝ) e
                  (fun x : Fin n × (Fin q → Fin n) => T (e x) ^ 2)
                  (fun J => T J ^ 2) (fun _ => rfl)
      calc
        ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
            ∑ K : Fin q → Fin n, ∑ i, ∑ a,
              (∑ k, H i a k * T (e (k, K))) ^ 2 := hsum
        _ ≤ ∑ K : Fin q → Fin n, 8 * ∑ a, T (e (a, K)) ^ 2 := by
              apply Finset.sum_le_sum
              intro K hK
              exact hpoint K
        _ = 8 * (∑ K : Fin q → Fin n, ∑ a, T (e (a, K)) ^ 2) := by
              rw [Finset.mul_sum]
        _ = 8 * ∑ J, T J ^ 2 := by rw [heq]
