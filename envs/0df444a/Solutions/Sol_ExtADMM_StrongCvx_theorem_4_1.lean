-- Prove2me | solution 1 for ExtADMM.StrongCvx.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T14:29:34.997589+00:00
-- url     : https://prove2.me/submissions/3acad199-018a-4cb5-a0a5-a59a111dfbaa

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_ExtADMM_StrongCvx_Setting
import Definitions.Def_ExtADMM_StrongCvx_Example41
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Positivity

open Matrix

namespace Aux_EA_fm

open ExtADMM.StrongCvx

noncomputable def AL (y1 y2 y3 l0 l1 l2 : ℝ) : ℝ :=
  (1 / 20 : ℝ) * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)
    - (l0 * (y1 + y2 + y3) + l1 * (y1 + y2 + 2 * y3) + l2 * (y1 + 2 * y2 + 2 * y3))
    + 1 / 2 * ((y1 + y2 + y3) ^ 2 + (y1 + y2 + 2 * y3) ^ 2 + (y1 + 2 * y2 + 2 * y3) ^ 2)

lemma hAL (y1 y2 y3 : Fin 1 → ℝ) (l : Fin 3 → ℝ) :
    example41.augLag 1 y1 y2 y3 l = AL (y1 0) (y2 0) (y3 0) (l 0) (l 1) (l 2) := by
  simp only [Problem.augLag, Problem.objective, Problem.residual, example41,
    ExtADMM.Diverge.col, AL]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

lemma quad_stat (F : ℝ → ℝ) (u A g : ℝ) (hA : 0 < A)
    (hF : ∀ t, F (u + t) - F u = g * t + A * t ^ 2) (hmin : ∀ t, F u ≤ F (u + t)) : g = 0 := by
  have h1 := hmin (-g / (2 * A))
  have h2 := hF (-g / (2 * A))
  have h3 : g * (-g / (2 * A)) + A * (-g / (2 * A)) ^ 2 = -(g ^ 2 / (4 * A)) := by
    field_simp; ring
  have h4 : g ^ 2 / (4 * A) ≤ 0 := by linarith
  have h5 : g ^ 2 ≤ 0 := by
    have := div_nonpos_iff.mp h4
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · nlinarith
    · exact h
  nlinarith [sq_nonneg g]

end Aux_EA_fm

open ExtADMM.StrongCvx Aux_EA_fm in
theorem S13Mapping.fixed_matrix_mapping (x1 x2 x3 : ℕ → Fin 1 → ℝ)
    (lam : ℕ → Fin 3 → ℝ) (hrun : example41.IsRun15 1 x1 x2 x3 lam) (k : ℕ) :
    stateVec (x2 (k+1)) (x3 (k+1)) (lam (k+1)) = M41 *ᵥ stateVec (x2 k) (x3 k) (lam k) := by
  obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, h4⟩ := hrun k
  set u := x1 (k + 1) 0
  set w2 := x2 (k + 1) 0
  set w3 := x3 (k + 1) 0
  set v2 := x2 k 0
  set v3 := x3 k 0
  set l0 := lam k 0
  set l1 := lam k 1
  set l2 := lam k 2
  -- stationarity for x1
  have E1 : (1 / 10 : ℝ) * u - (l0 + l1 + l2) +
      ((u + v2 + v3) + (u + v2 + 2 * v3) + (u + 2 * v2 + 2 * v3)) = 0 := by
    apply quad_stat (fun t => AL t v2 v3 l0 l1 l2) u (1 / 20 + 3 / 2) _ (by norm_num)
    · intro t; simp only [AL]; ring
    · intro t
      have := h1 (fun _ => u + t) (Set.mem_univ _)
      rw [hAL, hAL] at this
      exact this
  have E2 : (1 / 10 : ℝ) * w2 - (l0 + l1 + 2 * l2) +
      ((u + w2 + v3) + (u + w2 + 2 * v3) + 2 * (u + 2 * w2 + 2 * v3)) = 0 := by
    apply quad_stat (fun t => AL u t v3 l0 l1 l2) w2 (1 / 20 + 3) _ (by norm_num)
    · intro t; simp only [AL]; ring
    · intro t
      have := h2 (fun _ => w2 + t) (Set.mem_univ _)
      rw [hAL, hAL] at this
      exact this
  have E3 : (1 / 10 : ℝ) * w3 - (l0 + 2 * l1 + 2 * l2) +
      ((u + w2 + w3) + 2 * (u + w2 + 2 * w3) + 2 * (u + 2 * w2 + 2 * w3)) = 0 := by
    apply quad_stat (fun t => AL u w2 t l0 l1 l2) w3 (1 / 20 + 9 / 2) _ (by norm_num)
    · intro t; simp only [AL]; ring
    · intro t
      have := h3 (fun _ => w3 + t) (Set.mem_univ _)
      rw [hAL, hAL] at this
      exact this
  have hl : ∀ i, lam (k + 1) i = lam k i - Problem.residual example41 (x1 (k + 1)) (x2 (k + 1))
      (x3 (k + 1)) i := by
    intro i; rw [h4]; simp
  have hres : ∀ i, Problem.residual example41 (x1 (k + 1)) (x2 (k + 1)) (x3 (k + 1)) i =
      ![u + w2 + w3, u + w2 + 2 * w3, u + 2 * w2 + 2 * w3] i := by
    intro i
    simp only [Problem.residual, example41, ExtADMM.Diverge.col]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, u, w2, w3] <;> ring
  have hl0 := hl 0
  have hl1 := hl 1
  have hl2 := hl 2
  rw [hres] at hl0 hl1 hl2
  simp at hl0 hl1 hl2
  funext i
  fin_cases i <;>
    simp [stateVec, M41, mulVec, dotProduct, Fin.sum_univ_succ] <;>
    linarith

set_option autoImplicit false

open Matrix ExtADMM.StrongCvx Aux_EA_fm

namespace S13Run

lemma norm_fin_one_sq (x : Fin 1 → ℝ) : ‖x‖ ^ 2 = (x 0) ^ 2 := by
  have hx : x = fun _ : Fin 1 => x 0 := by
    funext i
    fin_cases i
    rfl
  rw [hx, pi_norm_const, Real.norm_eq_abs, sq_abs]

lemma objective_strong :
    StrongConvexOn Set.univ (1 / 10 : ℝ) (fun x : Fin 1 → ℝ => (1 / 20 : ℝ) * x 0 ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  change (1 / 20 : ℝ) * (a * x 0 + b * y 0) ^ 2 ≤
    a * ((1 / 20 : ℝ) * x 0 ^ 2) + b * ((1 / 20 : ℝ) * y 0 ^ 2) -
      a * b * ((1 / 10 : ℝ) / 2 * ‖x - y‖ ^ 2)
  rw [norm_fin_one_sq]
  change (1 / 20 : ℝ) * (a * x 0 + b * y 0) ^ 2 ≤
    a * ((1 / 20 : ℝ) * x 0 ^ 2) + b * ((1 / 20 : ℝ) * y 0 ^ 2) -
      a * b * ((1 / 10 : ℝ) / 2 * (x 0 - y 0) ^ 2)
  have hba : b = 1 - a := by linarith
  rw [hba]
  ring_nf
  exact le_rfl

lemma objective_convex :
    ConvexOn ℝ Set.univ (fun x : Fin 1 → ℝ => (1 / 20 : ℝ) * x 0 ^ 2) := by
  exact strongConvexOn_zero.mp (objective_strong.mono (by norm_num))

lemma all_strong :
    StrongConvexOn Set.univ (1/10) example41.θ1 ∧
    StrongConvexOn Set.univ (1/10) example41.θ2 ∧
    StrongConvexOn Set.univ (1/10) example41.θ3 := by
  have h : StrongConvexOn Set.univ (1/10) example41.θ1 := by
    convert objective_strong using 1 <;> norm_num [example41]
  exact ⟨h, h, h⟩

lemma standing : example41.Standing := by
  have hc : ConvexOn ℝ Set.univ example41.θ1 := by
    convert objective_convex using 1 <;> norm_num [example41]
  refine ⟨convex_univ, isClosed_univ, convex_univ, isClosed_univ,
    convex_univ, isClosed_univ, hc, hc, hc,
    0, Set.mem_univ _, 0, Set.mem_univ _, 0, Set.mem_univ _, ?_, ?_⟩
  · simp [Problem.residual, example41]
  · intro y1 hy1 y2 hy2 y3 hy3 hfeas
    simp only [Problem.objective, example41, Pi.zero_apply]
    nlinarith [sq_nonneg (y1 0), sq_nonneg (y2 0), sq_nonneg (y3 0)]

noncomputable def first (v2 v3 l0 l1 l2 : ℝ) : ℝ :=
  (10 / 31 : ℝ) * (l0 + l1 + l2 - 4 * v2 - 5 * v3)

noncomputable def second (u v3 l0 l1 l2 : ℝ) : ℝ :=
  (10 / 61 : ℝ) * (l0 + l1 + 2 * l2 - 4 * u - 7 * v3)

noncomputable def third (u v2 l0 l1 l2 : ℝ) : ℝ :=
  (10 / 91 : ℝ) * (l0 + 2 * l1 + 2 * l2 - 5 * u - 7 * v2)

lemma first_min (v2 v3 l0 l1 l2 y : ℝ) :
    AL (first v2 v3 l0 l1 l2) v2 v3 l0 l1 l2 ≤ AL y v2 v3 l0 l1 l2 := by
  have heq : AL y v2 v3 l0 l1 l2 - AL (first v2 v3 l0 l1 l2) v2 v3 l0 l1 l2 =
      (31 / 20 : ℝ) * (y - first v2 v3 l0 l1 l2) ^ 2 := by
    unfold AL first
    ring
  have hp : 0 ≤ (31 / 20 : ℝ) * (y - first v2 v3 l0 l1 l2) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith

lemma second_min (u v3 l0 l1 l2 y : ℝ) :
    AL u (second u v3 l0 l1 l2) v3 l0 l1 l2 ≤ AL u y v3 l0 l1 l2 := by
  have heq : AL u y v3 l0 l1 l2 - AL u (second u v3 l0 l1 l2) v3 l0 l1 l2 =
      (61 / 20 : ℝ) * (y - second u v3 l0 l1 l2) ^ 2 := by
    unfold AL second
    ring
  have hp : 0 ≤ (61 / 20 : ℝ) * (y - second u v3 l0 l1 l2) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith

lemma third_min (u v2 l0 l1 l2 y : ℝ) :
    AL u v2 (third u v2 l0 l1 l2) l0 l1 l2 ≤ AL u v2 y l0 l1 l2 := by
  have heq : AL u v2 y l0 l1 l2 - AL u v2 (third u v2 l0 l1 l2) l0 l1 l2 =
      (91 / 20 : ℝ) * (y - third u v2 l0 l1 l2) ^ 2 := by
    unfold AL third
    ring
  have hp : 0 ≤ (91 / 20 : ℝ) * (y - third u v2 l0 l1 l2) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith

noncomputable def next1 (z : Fin 5 → ℝ) : ℝ := first (z 0) (z 1) (z 2) (z 3) (z 4)
noncomputable def next2 (z : Fin 5 → ℝ) : ℝ := second (next1 z) (z 1) (z 2) (z 3) (z 4)
noncomputable def next3 (z : Fin 5 → ℝ) : ℝ := third (next1 z) (next2 z) (z 2) (z 3) (z 4)

noncomputable def step (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![next2 z, next3 z,
    z 2 - (next1 z + next2 z + next3 z),
    z 3 - (next1 z + next2 z + 2 * next3 z),
    z 4 - (next1 z + 2 * next2 z + 2 * next3 z)]

noncomputable def trajectory : ℕ → Fin 5 → ℝ
  | 0 => ![1, 0, 0, 0, 0]
  | k + 1 => step (trajectory k)

noncomputable def run1 : ℕ → Fin 1 → ℝ
  | 0 => 0
  | k + 1 => fun _ => next1 (trajectory k)

noncomputable def run2 (k : ℕ) : Fin 1 → ℝ := fun _ => trajectory k 0
noncomputable def run3 (k : ℕ) : Fin 1 → ℝ := fun _ => trajectory k 1
noncomputable def runLam (k : ℕ) : Fin 3 → ℝ :=
  ![trajectory k 2, trajectory k 3, trajectory k 4]

lemma exists_run : example41.IsRun15 1 run1 run2 run3 runLam := by
  intro k
  refine ⟨⟨Set.mem_univ _, ?_⟩, ⟨Set.mem_univ _, ?_⟩, ⟨Set.mem_univ _, ?_⟩, ?_⟩
  · intro y hy
    rw [hAL, hAL]
    simpa only [run1, run2, run3, runLam, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, next1] using
      first_min (trajectory k 0) (trajectory k 1) (trajectory k 2)
        (trajectory k 3) (trajectory k 4) (y 0)
  · intro y hy
    rw [hAL, hAL]
    simpa [run1, run2, run3, runLam, trajectory, step, next2] using
      second_min (next1 (trajectory k)) (trajectory k 1) (trajectory k 2)
        (trajectory k 3) (trajectory k 4) (y 0)
  · intro y hy
    rw [hAL, hAL]
    simpa [run1, run2, run3, runLam, trajectory, step, next3] using
      third_min (next1 (trajectory k)) (next2 (trajectory k)) (trajectory k 2)
        (trajectory k 3) (trajectory k 4) (y 0)
  · funext i
    fin_cases i <;>
      simp [run1, run2, run3, runLam, trajectory, step, Problem.residual, example41,
        ExtADMM.Diverge.col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma initial : run2 0 = (fun _ => 1) ∧ run3 0 = 0 ∧ runLam 0 = 0 := by
  constructor
  · rfl
  constructor
  · rfl
  funext i
  fin_cases i <;> rfl

end S13Run

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

open Matrix Filter Topology

namespace S13Energy

/-- A rational Lyapunov certificate, with denominators cleared. This quadratic
form is indefinite; only its exact increment and its value at the initial state
are used. Its coefficients were found externally and are checked below. -/
noncomputable def energy (z : Fin 5 → ℝ) : ℝ :=
    10303129690095860 * z 0 ^ 2
  + 10478074248843260 * z 1 ^ 2
  + 804173264514760 * z 2 ^ 2
  + 371644006441551 * z 3 ^ 2
  + 836887622217026 * z 4 ^ 2
  + 2 * (7913481774108000 * z 0 * z 1
    - 1307198256974360 * z 0 * z 2
    + 2377624100932400 * z 0 * z 3
    - 811576171752720 * z 0 * z 4
    + 1048492885395750 * z 1 * z 2
    + 1993184283477490 * z 1 * z 3
    - 2843840124520540 * z 1 * z 4
    - 171368398231728 * z 2 * z 3
    - 716342020824331 * z 2 * z 4
    - 191692203803453 * z 3 * z 4)

/-- The exact Lyapunov identity. No spectral approximation is involved. -/
theorem energy_step (z : Fin 5 → ℝ) :
    energy (ExtADMM.StrongCvx.M41 *ᵥ z) = energy z +
      50857198116940 * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2) := by
  have h3 : (2 : Fin 4).succ = (3 : Fin 5) := rfl
  have h4 : (2 : Fin 3).succ.succ = (4 : Fin 5) := rfl
  norm_num [energy, ExtADMM.StrongCvx.M41, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.smul_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, h3, h4]
  <;> ring

/-- A fixed point has zero sum of squares, by the Lyapunov identity itself. -/
theorem fixed_eq_zero (z : Fin 5 → ℝ)
    (hz : ExtADMM.StrongCvx.M41 *ᵥ z = z) : z = 0 := by
  have h := energy_step z
  rw [hz] at h
  have hs : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2 = 0 := by
    linarith
  have h0 : z 0 ^ 2 = 0 := by
    nlinarith only [hs, sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3), sq_nonneg (z 4), sq_nonneg (z 0)]
  have h1 : z 1 ^ 2 = 0 := by
    nlinarith only [hs, sq_nonneg (z 0), sq_nonneg (z 2), sq_nonneg (z 3), sq_nonneg (z 4), sq_nonneg (z 1)]
  have h2 : z 2 ^ 2 = 0 := by
    nlinarith only [hs, sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 3), sq_nonneg (z 4), sq_nonneg (z 2)]
  have h3 : z 3 ^ 2 = 0 := by
    nlinarith only [hs, sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 4), sq_nonneg (z 3)]
  have h4 : z 4 ^ 2 = 0 := by
    nlinarith only [hs, sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3), sq_nonneg (z 4)]
  ext i
  fin_cases i
  · exact sq_eq_zero_iff.mp h0
  · exact sq_eq_zero_iff.mp h1
  · exact sq_eq_zero_iff.mp h2
  · exact sq_eq_zero_iff.mp h3
  · exact sq_eq_zero_iff.mp h4

theorem energy_continuous : Continuous energy := by
  unfold energy
  continuity

/-- Every orbit from the first basis vector retains a positive energy. -/
theorem energy_bound (z : ℕ → Fin 5 → ℝ)
    (hzero : z 0 = ![1, 0, 0, 0, 0])
    (hstep : ∀ k, z (k + 1) = ExtADMM.StrongCvx.M41 *ᵥ z k) :
    ∀ k, (10303129690095860 : ℝ) ≤ energy (z k) := by
  intro k
  induction k with
  | zero => rw [hzero]; norm_num [energy, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  | succ k ih =>
      rw [hstep k, energy_step]
      have hnonneg : 0 ≤ (50857198116940 : ℝ) *
          (z k 0 ^ 2 + z k 1 ^ 2 + z k 2 ^ 2 + z k 3 ^ 2 + z k 4 ^ 2) := by
        positivity
      linarith

/-- A matrix orbit from the first basis vector cannot converge. This is the
instability needed by the original ADMM root, without eigenvalue isolation. -/
theorem no_convergent_orbit (z : ℕ → Fin 5 → ℝ)
    (hzero : z 0 = ![1, 0, 0, 0, 0])
    (hstep : ∀ k, z (k + 1) = ExtADMM.StrongCvx.M41 *ᵥ z k) :
    ¬ ∃ w, Tendsto z atTop (𝓝 w) := by
  rintro ⟨w, hw⟩
  have hcont : Continuous (fun v : Fin 5 → ℝ => ExtADMM.StrongCvx.M41 *ᵥ v) :=
    by
      apply continuous_pi
      intro i
      fin_cases i <;>
        norm_num [ExtADMM.StrongCvx.M41, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, Matrix.smul_apply, Matrix.cons_val] <;> continuity
  have hnext : Tendsto (fun k => z (k + 1)) atTop (𝓝 w) :=
    hw.comp (tendsto_add_atTop_nat 1)
  have hmap : Tendsto (fun k => ExtADMM.StrongCvx.M41 *ᵥ z k) atTop
      (𝓝 (ExtADMM.StrongCvx.M41 *ᵥ w)) :=
    (hcont.tendsto w).comp hw
  have heq : (fun k => ExtADMM.StrongCvx.M41 *ᵥ z k) = fun k => z (k + 1) :=
    funext fun k => (hstep k).symm
  rw [heq] at hmap
  have hfixed : ExtADMM.StrongCvx.M41 *ᵥ w = w := tendsto_nhds_unique hmap hnext
  have hwzero : w = 0 := fixed_eq_zero w hfixed
  subst w
  have henergy : Tendsto (fun k => energy (z k)) atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def, energy] using (energy_continuous.tendsto 0).comp hw
  have hbound : (10303129690095860 : ℝ) ≤ 0 :=
    ge_of_tendsto' henergy (energy_bound z hzero hstep)
  norm_num at hbound


end S13Energy

set_option autoImplicit false
open Matrix Filter Topology ExtADMM.StrongCvx

theorem solution :
    example41.Standing ∧
    (StrongConvexOn Set.univ (1/10) example41.θ1 ∧ StrongConvexOn Set.univ (1/10) example41.θ2 ∧
      StrongConvexOn Set.univ (1/10) example41.θ3) ∧
    ∃ (x20 x30 : Fin 1 → ℝ) (lam0 : Fin 3 → ℝ),
      (∃ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
        example41.IsRun15 1 x1 x2 x3 lam ∧ x2 0 = x20 ∧ x3 0 = x30 ∧ lam 0 = lam0) ∧
      ∀ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
        example41.IsRun15 1 x1 x2 x3 lam → x2 0 = x20 → x3 0 = x30 → lam 0 = lam0 →
          ¬ ∃ w, Tendsto (fun k => (x1 k, x2 k, x3 k, lam k)) atTop (𝓝 w)  := by
  refine ⟨S13Run.standing, S13Run.all_strong, (fun _ => 1), 0, 0, ?_, ?_⟩
  · exact ⟨S13Run.run1, S13Run.run2, S13Run.run3, S13Run.runLam,
      S13Run.exists_run, S13Run.initial.1, S13Run.initial.2.1, S13Run.initial.2.2⟩
  · intro x1 x2 x3 lam hrun hx2 hx3 hlam
    rintro ⟨w, hw⟩
    have hzero : stateVec (x2 0) (x3 0) (lam 0) = ![1, 0, 0, 0, 0] := by
      rw [hx2, hx3, hlam]
      rfl
    have hstep (k : ℕ) :
        stateVec (x2 (k + 1)) (x3 (k + 1)) (lam (k + 1)) =
          M41 *ᵥ stateVec (x2 k) (x3 k) (lam k) :=
      S13Mapping.fixed_matrix_mapping x1 x2 x3 lam hrun k
    apply S13Energy.no_convergent_orbit
      (fun k => stateVec (x2 k) (x3 k) (lam k)) hzero hstep
    have hc : Continuous (fun v : (Fin 1 → ℝ) × (Fin 1 → ℝ) ×
        (Fin 1 → ℝ) × (Fin 3 → ℝ) => stateVec v.2.1 v.2.2.1 v.2.2.2) := by
      have h2 : Continuous (fun v : (Fin 1 → ℝ) × (Fin 1 → ℝ) ×
          (Fin 1 → ℝ) × (Fin 3 → ℝ) => v.2.1) := continuous_snd.fst
      have h3 : Continuous (fun v : (Fin 1 → ℝ) × (Fin 1 → ℝ) ×
          (Fin 1 → ℝ) × (Fin 3 → ℝ) => v.2.2.1) := continuous_snd.snd.fst
      have hl : Continuous (fun v : (Fin 1 → ℝ) × (Fin 1 → ℝ) ×
          (Fin 1 → ℝ) × (Fin 3 → ℝ) => v.2.2.2) := continuous_snd.snd.snd
      apply continuous_pi
      intro i
      fin_cases i
      · exact (continuous_apply (0 : Fin 1)).comp h2
      · exact (continuous_apply (0 : Fin 1)).comp h3
      · exact (continuous_apply (0 : Fin 3)).comp hl
      · exact (continuous_apply (1 : Fin 3)).comp hl
      · exact (continuous_apply (2 : Fin 3)).comp hl
    exact ⟨stateVec w.2.1 w.2.2.1 w.2.2.2, (hc.tendsto w).comp hw⟩

#print axioms solution
