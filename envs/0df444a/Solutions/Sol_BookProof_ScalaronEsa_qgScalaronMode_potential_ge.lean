-- Prove2me | solution 1 for BookProof.ScalaronEsa.qgScalaronMode_potential_ge
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T03:22:02.467067+00:00
-- url     : https://prove2.me/submissions/92951738-ccf6-4199-a85e-653414865426

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.qgScalaronMode_potential_ge
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.ScalaronEsa


open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (halpha : 0 < alpha) (k : ℕ) :
    -(M ^ 4 / (16 * alpha)) ≤ qgScalaronModePotential M alpha Rc phi k := by
  have hne : alpha ≠ 0 := ne_of_gt halpha
  have h16 : (0 : ℝ) < 16 * alpha := by linarith
  -- `V₃(R_c) = α (R_c − M²/(4α))² − M⁴/(16α)` : the completed square.
  have hcs : BookProof.Starobinsky.confV M alpha (Rc k)
      = alpha * (Rc k - M ^ 2 / (4 * alpha)) ^ 2 - M ^ 4 / (16 * alpha) := by
    simp only [BookProof.Starobinsky.confV]
    first
      | (field_simp; ring)
      | field_simp
      | ring
  -- the regularized conformal-mode parabola is bounded below by `−M⁴/(16α)`
  have h1 : -(M ^ 4 / (16 * alpha)) ≤ BookProof.Starobinsky.confV M alpha (Rc k) := by
    rw [hcs]
    have hsq : 0 ≤ alpha * (Rc k - M ^ 2 / (4 * alpha)) ^ 2 :=
      mul_nonneg halpha.le (sq_nonneg _)
    linarith
  have hpos : 0 ≤ M ^ 4 / (16 * alpha) := div_nonneg (by positivity) h16.le
  -- the Einstein-frame scalaron potential is a positive constant times a square
  have h2 : 0 ≤ BookProof.Starobinsky.starobinskyV M alpha (phi k) := by
    simp only [BookProof.Starobinsky.starobinskyV]
    exact mul_nonneg hpos (sq_nonneg _)
  simp only [qgScalaronModePotential]
  linarith
