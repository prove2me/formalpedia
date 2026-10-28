-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.cumulantEnergy_succ_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:35:37.559981+00:00
-- url     : https://prove2.me/submissions/1e8c3294-f45f-4847-8aa6-ae0d3866308c

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}
private lemma FunctionalInequalities.KLS.BKL.fin_snoc_comp
    {r n : ℕ} {α : Type*} (g : Fin n → α)
    (p : Fin r → Fin n) (x : Fin n) :
    (fun k : Fin (r + 1) =>
        g ((Fin.snoc (α := fun _ : Fin (r + 1) => Fin n) p x) k)) =
      Fin.snoc (α := fun _ : Fin (r + 1) => α)
        (fun s => g (p s)) (g x) := by
  funext i
  refine Fin.lastCases ?_ (fun s => ?_) i
  · simp
  · simp [Fin.snoc_castSucc]
/-- **The cumulant energy of the next order, reindexed** (BKL (90), `Σ_i |W_i|² = E_{m+1}`): splitting the last
slot, `E_{r+2}(u) = Σ_K Σ_k κ_{r+3}(u, σ e_{K_1}, …, σ e_{r}, σ e_k)²`. -/
theorem solution (ν : Measure (EuclideanSpace ℝ (Fin n))) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    FunctionalInequalities.KLS.BKL.cumulantEnergy ν (r + 1) u =
      ∑ K : Fin r → Fin n, ∑ k : Fin n, FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1 + 1)
        (Fin.cons u (Fin.snoc (fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
          (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ k)))) ^ 2 := by
  classical
  unfold FunctionalInequalities.KLS.BKL.cumulantEnergy
  let reindex :
      (Fin r → Fin n) × Fin n ≃ (Fin (r + 1) → Fin n) :=
    { toFun := fun q =>
        Fin.snoc (α := fun _ : Fin (r + 1) => Fin n) q.1 q.2
      invFun := fun J => (fun s => J s.castSucc, J (Fin.last r))
      left_inv := by
        intro q
        simp
      right_inv := by
        intro J
        funext i
        refine Fin.lastCases ?_ (fun s => ?_) i
        · simp
        · simp }
  let g : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun j => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  have harg (q : (Fin r → Fin n) × Fin n) :
      Fin.cons (α := fun _ : Fin (r + 1 + 1) => EuclideanSpace ℝ (Fin n)) u
          (fun k => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
            (EuclideanSpace.basisFun (Fin n) ℝ ((reindex q) k))) =
        Fin.cons (α := fun _ : Fin (r + 1 + 1) => EuclideanSpace ℝ (Fin n)) u
          (Fin.snoc (α := fun _ : Fin (r + 1) => EuclideanSpace ℝ (Fin n))
            (fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
              (EuclideanSpace.basisFun (Fin n) ℝ (q.1 s)))
            (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
              (EuclideanSpace.basisFun (Fin n) ℝ q.2))) := by
    have hs := FunctionalInequalities.KLS.BKL.fin_snoc_comp g q.1 q.2
    have h :=
      congrArg
        (fun f : Fin (r + 1) → EuclideanSpace ℝ (Fin n) =>
          Fin.cons (α := fun _ : Fin (r + 1 + 1) => EuclideanSpace ℝ (Fin n)) u f) hs
    simpa [reindex, g] using h
  calc
    ∑ J : Fin (r + 1) → Fin n,
        FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1 + 1)
          (Fin.cons u
            (fun k => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
              (EuclideanSpace.basisFun (Fin n) ℝ (J k)))) ^ 2 =
        ∑ q : (Fin r → Fin n) × Fin n,
          FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1 + 1)
            (Fin.cons u
              (Fin.snoc
                (α := fun _ : Fin (r + 1) => EuclideanSpace ℝ (Fin n))
                (fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
                  (EuclideanSpace.basisFun (Fin n) ℝ (q.1 s)))
                (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
                  (EuclideanSpace.basisFun (Fin n) ℝ q.2)))) ^ 2 := by
      refine
        (Fintype.sum_equiv reindex
          (fun q : (Fin r → Fin n) × Fin n =>
            FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1 + 1)
              (Fin.cons u
                (Fin.snoc
                  (α := fun _ : Fin (r + 1) => EuclideanSpace ℝ (Fin n))
                  (fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
                    (EuclideanSpace.basisFun (Fin n) ℝ (q.1 s)))
                  (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
                    (EuclideanSpace.basisFun (Fin n) ℝ q.2)))) ^ 2)
          (fun J : Fin (r + 1) → Fin n =>
            FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1 + 1)
              (Fin.cons u
                (fun k => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
                  (EuclideanSpace.basisFun (Fin n) ℝ (J k)))) ^ 2) ?_).symm
      intro q
      exact congrArg
        (fun z : Fin (r + 1 + 1) → EuclideanSpace ℝ (Fin n) =>
          FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1 + 1) z ^ 2)
        (harg q).symm
    _ = ∑ K : Fin r → Fin n, ∑ k : Fin n, FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1 + 1)
        (Fin.cons u (Fin.snoc (fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
          (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
          (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator ν)
            (EuclideanSpace.basisFun (Fin n) ℝ k)))) ^ 2 := by
      rw [Fintype.sum_prod_type]
