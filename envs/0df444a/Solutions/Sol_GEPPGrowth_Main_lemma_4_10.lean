-- Prove2me | solution 1 for GEPPGrowth.Main.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:41:59.531622+00:00
-- url     : https://prove2.me/submissions/6c241916-03f4-44d6-a837-fc35994db281

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_MuirheadMST_bartlett_decomposition

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPLemma410

open GEPPGrowth.Main

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

instance (k : ℕ) : SigmaFinite (stdGaussian (E k)) := IsFiniteMeasure.toSigmaFinite _

/-- GEPP's Wishart law with identity covariance is Muirhead's `W_p(n, I)`. -/
lemma wishart_eq (p n : ℕ) :
    (wishart (1 : Mat p) n : Measure (Fin p → Fin p → ℝ)) = MuirheadMST.wishart p n 1 := by
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => multivariateGaussian (0 : E p) 1)
    (f := fun _ (x : E p) (i : Fin p) => x i) (fun _ => by fun_prop)
  simp only at h
  have hG : Measurable (fun G : Matrix (Fin p) (Fin n) ℝ => G * G.transpose) := by
    change Measurable (fun G : Fin p → Fin n → ℝ => fun i j => ∑ k, G i k * G j k)
    fun_prop
  have hT : Measurable (fun z i j => z j i : (Fin n → Vec p) → Matrix (Fin p) (Fin n) ℝ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)
  unfold wishart columnsLaw normal MuirheadMST.wishart MuirheadMST.normalDataMatrix
  rw [Measure.map_map hG hT, ← h, Measure.map_map (hG.comp hT) (by fun_prop)]
  congr 1

/-- `‖g‖²` of a standard Gaussian vector in `ℝ^k` is `χ²_k`. -/
lemma stdGaussian_map_normSq (k : ℕ) :
    (stdGaussian (E k)).map (fun g => ‖g‖ ^ 2) = chiSquare k := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop), chiSquare]
  congr 1
  funext x
  simp [EuclideanSpace.real_norm_sq_eq]

/-- The determinant of `TᵀT` for Bartlett's factor is `∏ ‖g_i‖²`. -/
lemma det_bartlett {m n : ℕ} (ω : MuirheadMST.BartlettSample m n) :
    (Matrix.of fun j k => ∑ i, MuirheadMST.bartlettFactor ω i j *
        MuirheadMST.bartlettFactor ω i k).det = ∏ i, ‖ω.1 i‖ ^ 2 := by
  set T := Matrix.of (MuirheadMST.bartlettFactor ω)
  have hM : (Matrix.of fun j k => ∑ i, MuirheadMST.bartlettFactor ω i j *
      MuirheadMST.bartlettFactor ω i k) = Tᵀ * T := by
    ext j k; simp [T, Matrix.mul_apply]
  have hT : T.BlockTriangular id := by
    intro i j hji
    simp only [id] at hji
    simp only [T, Matrix.of_apply, MuirheadMST.bartlettFactor]
    rw [if_neg (ne_of_gt hji), if_neg (not_lt.2 hji.le)]
  rw [hM, Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hT, ← sq,
    ← Finset.prod_pow]
  simp [T, MuirheadMST.bartlettFactor]

/-- The statement on Muirhead's array types. -/
lemma main (p n : ℕ) (hpn : p ≤ n) :
    (MuirheadMST.wishart p n 1).map (fun A => (Matrix.of A).det) =
      (Measure.pi (fun i : Fin p => chiSquare (n-i.val))).map (fun x => ∏ i, x i) := by
  have hB : Measurable (fun ω : MuirheadMST.BartlettSample p n => MuirheadMST.bartlettFactor ω) := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    unfold MuirheadMST.bartlettFactor; split_ifs <;> fun_prop
  have hdet : Measurable (fun A : Fin p → Fin p → ℝ => (Matrix.of A).det) := by
    simp only [Matrix.det_apply, Matrix.of_apply]
    fun_prop
  rw [← MuirheadMST.bartlett_decomposition p n hpn,
    Measure.map_map hdet (by fun_prop)]
  have h1 : ((fun A : Fin p → Fin p → ℝ => (Matrix.of A).det) ∘ fun ω j k => ∑ i, MuirheadMST.bartlettFactor ω i j *
      MuirheadMST.bartlettFactor ω i k) =
      (fun g : (∀ i : Fin p, E (n - i)) => ∏ i, ‖g i‖ ^ 2) ∘ Prod.fst := by
    funext ω; exact det_bartlett ω
  rw [h1, ← Measure.map_map (by fun_prop) measurable_fst, MuirheadMST.bartlettLaw,
    Measure.map_fst_prod, measure_univ, one_smul]
  have h2 : (fun g : (∀ i : Fin p, E (n - i)) => ∏ i, ‖g i‖ ^ 2) =
      (fun x : Fin p → ℝ => ∏ i, x i) ∘ (fun g i => ‖g i‖ ^ 2) := rfl
  have h3 := Measure.pi_map_pi (μ := fun i : Fin p => stdGaussian (E (n - i)))
    (f := fun i (v : E (n - i)) => ‖v‖ ^ 2) (fun i => by fun_prop)
  simp only at h3
  rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), h3]
  simp_rw [stdGaussian_map_normSq]

end GEPPLemma410

open GEPPGrowth.Main GEPPLemma410 in
theorem solution (p n : ℕ) (hp : 0 < p) (hpn : p ≤ n) :
    (wishart (1 : Mat p) n).map Matrix.det =
      (Measure.pi (fun i : Fin p => chiSquare (n-i.val))).map (fun x => ∏ i, x i) := by
  rw [show wishart (1 : Mat p) n = MuirheadMST.wishart p n 1 from wishart_eq p n]
  exact main p n hpn
