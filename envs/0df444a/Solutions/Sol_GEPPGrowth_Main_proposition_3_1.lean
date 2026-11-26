-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:00:13.607531+00:00
-- url     : https://prove2.me/submissions/187c434a-f1aa-4bd7-8cd6-369e42c49a5b

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPProp31

open GEPPGrowth.Main

/-- A linear image of a centered multivariate Gaussian is the Gaussian with covariance `A S Aᵀ`. -/
lemma mvG_map {m n : ℕ} (S : Mat n) (hS : S.PosSemidef) (A : Matrix (Fin m) (Fin n) ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S).map
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) =
    multivariateGaussian 0 (A * S * Aᵀ) := by
  have hS' : (A * S * Aᵀ).PosSemidef := by
    simpa using hS.mul_mul_conjTranspose_same A
  apply IsGaussian.ext
  · simp only [id]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · have hadj : ∀ w : EuclideanSpace ℝ (Fin m),
        ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).adjoint w).ofLp =
          Aᵀ *ᵥ w.ofLp := by
      intro w
      have h1 := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
      have h2 := congrArg (fun f => (f w).ofLp) h1
      simp only [Matrix.ofLp_toEuclideanLin_apply] at h2
      rw [← ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_toLinearMap]
      simpa using h2.symm
    ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hS', hadj, hadj]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u.ofLp A,
      Matrix.mulVec_transpose]


/-- `normal` version of `mvG_map`: `A x` for `x ~ N(0,S)` has law `N(0, A S Aᵀ)`. -/
lemma normal_map_mulVec {m n : ℕ} (S : Mat n) (hS : S.PosSemidef) (A : Matrix (Fin m) (Fin n) ℝ) :
    (normal S).map (fun x => A *ᵥ x) = normal (A * S * Aᵀ) := by
  unfold normal
  rw [← mvG_map S hS A, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- A pushforward of a product measure is the bind of the sections. -/
lemma prod_map_eq_bind {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure α) (π : Measure β) [SFinite π] (G : α × β → γ) (hG : Measurable G) :
    (ν.prod π).map G = ν.bind (fun y => π.map (fun w => G (y, w))) := by
  have hk : Measurable (fun y => π.map (fun w => G (y, w))) := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    have : (fun y => π.map (fun w => G (y, w)) s) = fun y => π (Prod.mk y ⁻¹' (G ⁻¹' s)) := by
      funext y
      rw [Measure.map_apply (f := fun w => G (y, w)) (hG.comp measurable_prodMk_left) hs]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left (hG hs)
  ext s hs
  rw [Measure.map_apply hG hs, Measure.prod_apply (hG hs), Measure.bind_apply hs hk.aemeasurable]
  refine lintegral_congr (fun y => ?_)
  rw [Measure.map_apply (f := fun w => G (y, w)) (hG.comp measurable_prodMk_left) hs]
  rfl

/-- Proposition 3.1 for any measurable choice of compression matrix `Φ y`. -/
lemma main_general {d : ℕ} (S : Mat (d+1)) (hS : S.PosSemidef)
    (Φ : Vec (d+1) → Matrix (Fin d) (Fin (d+1)) ℝ) (hΦ : Measurable Φ) :
    (columnsLaw S (d+1)).map
      (fun M => ((fun i => M i 0), (Φ (fun i => M i 0) * M).submatrix id Fin.succ)) =
    (normal S).bind (fun y => (columnsLaw (Φ y * S * (Φ y)ᵀ) d).map (fun M => (y,M))) := by
  -- the explicit joint map on (first column, remaining columns)
  set H : Vec (d+1) × (Fin d → Vec (d+1)) → Vec (d+1) × Mat d :=
    fun q => (q.1, fun a j => ∑ b, Φ q.1 a b * q.2 j b) with hH
  have hHm : Measurable H := by
    rw [hH]
    refine Measurable.prodMk measurable_fst ?_
    refine measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun j => ?_))
    have : ∀ b, Measurable (fun q : Vec (d+1) × (Fin d → Vec (d+1)) => Φ q.1 a b) := fun b =>
      (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hΦ.comp measurable_fst))
    show Measurable (fun q : Vec (d+1) × (Fin d → Vec (d+1)) => ∑ b, Φ q.1 a b * q.2 j b)
    have h2 : ∀ b, Measurable (fun q : Vec (d+1) × (Fin d → Vec (d+1)) => q.2 j b) := fun b =>
      by fun_prop
    exact Finset.measurable_sum _ (fun b _ => (this b).mul (h2 b))
  have hF : Measurable (fun M : Mat (d+1) =>
      ((fun i => M i 0), (Φ (fun i => M i 0) * M).submatrix id Fin.succ)) := by
    have h0 : Measurable (fun M : Mat (d+1) => (fun i => M i 0 : Vec (d+1))) := by
      refine measurable_pi_lambda _ (fun i => ?_)
      exact (measurable_pi_apply 0).comp (measurable_pi_apply i)
    refine Measurable.prodMk h0 ?_
    refine measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun j => ?_))
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
    have : ∀ b, Measurable (fun M : Mat (d+1) => Φ (fun i => M i 0) a b) := fun b =>
      (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hΦ.comp h0))
    have h1 : ∀ b, Measurable (fun M : Mat (d+1) => M b j.succ) := fun b =>
      (measurable_pi_apply j.succ).comp (measurable_pi_apply b)
    show Measurable (fun M : Mat (d+1) => ∑ b, Φ (fun i => M i 0) a b * M b j.succ)
    exact Finset.measurable_sum _ (fun b _ => (this b).mul (h1 b))
  have hT : ∀ r k, Measurable (fun z : Fin k → Vec r => (fun i j => z j i : Matrix (Fin r) (Fin k) ℝ)) := by
    intro r k
    exact measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)))
  have hpi : (Measure.pi (fun _ : Fin (d+1) => normal S)) =
      ((normal S).prod (Measure.pi (fun _ : Fin d => normal S))).map
        (MeasurableEquiv.piFinSuccAbove (fun _ => Vec (d+1)) 0).symm :=
    ((measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => normal S) 0).symm _).map_eq.symm
  have hL : (columnsLaw S (d+1)).map
      (fun M => ((fun i => M i 0), (Φ (fun i => M i 0) * M).submatrix id Fin.succ)) =
      ((normal S).prod (Measure.pi (fun _ : Fin d => normal S))).map H := by
    unfold columnsLaw
    rw [Measure.map_map hF (hT _ _), hpi, Measure.map_map (hF.comp (hT _ _)) (MeasurableEquiv.measurable _)]
    congr 1
  rw [hL, prod_map_eq_bind _ _ H hHm]
  congr 1
  funext y
  unfold columnsLaw
  rw [← normal_map_mulVec S hS (Φ y), ← Measure.pi_map_pi (fun _ => by fun_prop)]
  erw [Measure.map_map (hT _ _) (by fun_prop),
    Measure.map_map (by fun_prop) ((hT _ _).comp (by fun_prop))]
  congr 1

end GEPPProp31

open GEPPGrowth.Main in
theorem solution (d : ℕ) (S : Mat (d+1)) (hS : S.PosSemidef)
    (p : Vec (d+1) → Fin (d+1)) (hp : Measurable p)
    (hmax : ∀ y, IsMaxPivot y (p y)) :
    (columnsLaw S (d+1)).map
      (fun M => ((fun i => M i 0), residualStepWith p M)) =
    (normal S).bind (fun y => (columnsLaw (updateAt S y (p y)) d).map (fun M => (y,M))) := by
  have hΦ : Measurable (fun y : Vec (d+1) => compressionAt y (p y)) := by
    have h2 : Measurable (fun q : Vec (d+1) × Fin (d+1) => compressionAt q.1 q.2) := by
      refine measurable_from_prod_countable_left (fun i => ?_)
      refine measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun b => ?_))
      simp only [compressionAt, eliminationAt, ratiosAt, Matrix.mul_apply, Matrix.sub_apply,
        Matrix.vecMulVec_apply]
      fun_prop
    exact h2.comp (f := fun y => (y, p y)) (measurable_id.prodMk hp)
  unfold residualStepWith updateAt
  exact GEPPProp31.main_general S hS (fun y => compressionAt y (p y)) hΦ
