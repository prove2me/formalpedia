-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_max_simplexEdgeMatrix_det_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:07:18.26823+00:00
-- url     : https://prove2.me/submissions/1351b616-eac2-45b1-bc10-5e37fc2cc10d

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Mathlib

noncomputable section
open Set Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **A compact convex body contains a simplex of maximal volume with positive volume** (weak Letwin
route, Caffarelli's argument, affine normalisation). -/
theorem solution {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hint : (interior K).Nonempty) :
    ∃ v : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, v i ∈ K) ∧
      0 < |(FunctionalInequalities.Analysis.simplexEdgeMatrix v).det| ∧
      ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
        |(FunctionalInequalities.Analysis.simplexEdgeMatrix w).det| ≤ |(FunctionalInequalities.Analysis.simplexEdgeMatrix v).det| := by
  have hcoord :
      ∀ i : Fin n, Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
    intro i
    exact PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i
  have hmatrix :
      Continuous
        (fun v : Fin (n + 1) → EuclideanSpace ℝ (Fin n) =>
          FunctionalInequalities.Analysis.simplexEdgeMatrix v) := by
    apply continuous_matrix
    intro i j
    change Continuous
      (fun v : Fin (n + 1) → EuclideanSpace ℝ (Fin n) => (v j.succ - v 0) i)
    exact (hcoord i).comp ((continuous_apply j.succ).sub (continuous_apply 0))
  have hvolume : Continuous (@FunctionalInequalities.Analysis.simplexVolume n) := by
    unfold FunctionalInequalities.Analysis.simplexVolume
    exact continuous_abs.comp hmatrix.matrix_det
  let S : Set (Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :=
    (Set.univ : Set (Fin (n + 1))).pi (fun _ => K)
  have hScompact : IsCompact S :=
    isCompact_univ_pi (fun _ => hK)
  obtain ⟨x₀, hx₀⟩ := hint
  have hx₀nhds : K ∈ nhds x₀ :=
    mem_interior_iff_mem_nhds.mp hx₀
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hx₀nhds
  have hhalf : 0 < δ / 2 :=
    div_pos hδ (by norm_num)
  have hSnonempty : S.Nonempty := by
    refine ⟨fun _ => x₀, ?_⟩
    exact Set.mem_univ_pi.mpr (fun _ => interior_subset hx₀)
  obtain ⟨v, hvS, hvmax⟩ :=
    hScompact.exists_isMaxOn hSnonempty hvolume.continuousOn
  have hmax :
      ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), w ∈ S →
        FunctionalInequalities.Analysis.simplexVolume w ≤ FunctionalInequalities.Analysis.simplexVolume v := by
    intro w hw
    have hev :
        ∀ᶠ z : Fin (n + 1) → EuclideanSpace ℝ (Fin n)
          in Filter.principal S, FunctionalInequalities.Analysis.simplexVolume z ≤ FunctionalInequalities.Analysis.simplexVolume v :=
      hvmax
    exact (Filter.mem_principal.mp (Filter.eventually_iff.mp hev)) hw
  let w : Fin (n + 1) → EuclideanSpace ℝ (Fin n) :=
    Fin.cases x₀
      (fun j => x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ))
  have hwS : w ∈ S := by
    apply Set.mem_univ_pi.mpr
    intro i
    refine Fin.cases ?_ ?_ i
    · change x₀ ∈ K
      exact interior_subset hx₀
    · intro j
      change x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ) ∈ K
      apply hball
      rw [Metric.mem_ball]
      calc
        dist (x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ)) x₀ =
            ‖(x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ)) - x₀‖ :=
          dist_eq_norm _ _
        _ = ‖(δ / 2) • EuclideanSpace.single j (1 : ℝ)‖ := by
          rw [add_sub_cancel_left]
        _ = ‖δ / 2‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := by
          exact norm_smul (δ / 2) (EuclideanSpace.single j (1 : ℝ))
        _ = δ / 2 := by
          rw [PiLp.norm_single 2 (fun _ : Fin n => ℝ) j (1 : ℝ),
            Real.norm_eq_abs, abs_of_pos hhalf, norm_one, mul_one]
        _ < δ := half_lt_self hδ
  have hmatrix_w :
      FunctionalInequalities.Analysis.simplexEdgeMatrix w =
        (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [FunctionalInequalities.Analysis.simplexEdgeMatrix, w, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hdet_w :
      (FunctionalInequalities.Analysis.simplexEdgeMatrix w).det = (δ / 2) ^ n := by
    rw [hmatrix_w, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hpos_w : 0 < FunctionalInequalities.Analysis.simplexVolume w := by
    unfold FunctionalInequalities.Analysis.simplexVolume
    rw [hdet_w, abs_of_pos (pow_pos hhalf n)]
    exact pow_pos hhalf n
  have hpos_v : 0 < FunctionalInequalities.Analysis.simplexVolume v :=
    lt_of_lt_of_le hpos_w (hmax w hwS)
  have hvK : ∀ i, v i ∈ K :=
    Set.mem_univ_pi.mp hvS
  refine ⟨v, hvK, ?_, ?_⟩
  · exact hpos_v
  · intro u hu
    exact hmax u (Set.mem_univ_pi.mpr hu)
