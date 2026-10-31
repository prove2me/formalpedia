-- Prove2me | solution 1 for FoundationsML.Stability.svr_stability_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:01:49.319653+00:00
-- url     : https://prove2.me/submissions/23e07dfd-c032-418f-9bc7-1ebf46f1b870

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_IsRKHSOf
import Definitions.Def_FoundationsML_Stability_IsMinimizer
import Definitions.Def_FoundationsML_Stability_EpsilonInsensitiveLoss

open MeasureTheory FoundationsML.Stability

theorem solution
    {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace (X × ℝ)] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ) (_hRKHS : IsRKHSOf K Φ ev)
    (r : ℝ) (_hr : 0 ≤ r) (_hK : ∀ x : X, K x x ≤ r ^ 2)
    (ε : ℝ) (M : ℝ) (hM : 0 ≤ M)
    {m : ℕ} (_hm : 0 < m) (lam : ℝ) (_hlam : 0 < lam)
    (A : (Fin m → X × ℝ) → H)
    (_hmin : ∀ S : Fin m → X × ℝ,
      IsMinimizer (fun g : H => EmpiricalError (EpsilonInsensitiveLoss ε) S (ev g) +
        lam * ‖g‖ ^ 2) (A S))
    (hbound : ∀ S : Fin m → X × ℝ, ∀ z : X × ℝ,
      Loss (EpsilonInsensitiveLoss ε) (ev (A S)) z ≤ M)
    (_hAmeas : ∀ S : Fin m → X × ℝ, Measurable (Loss (EpsilonInsensitiveLoss ε) (ev (A S))))
    (δ : ℝ) (_hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | GeneralizationError D (EpsilonInsensitiveLoss ε) (ev (A S)) ≤
        EmpiricalError (EpsilonInsensitiveLoss ε) S (ev (A S)) +
          r ^ 2 / (m * lam) +
          (2 * r ^ 2 / lam + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by
  have hne : Nonempty (X × ℝ) := Measure.nonempty_of_neZero D
  obtain ⟨⟨x₀, _⟩⟩ := hne
  let S₀ : Fin m → X × ℝ := fun _ => (x₀, 0)
  let c : ℝ := ev (A S₀) x₀
  let y : ℝ := c - (|ε| + M + 1)
  have h1 : Loss (EpsilonInsensitiveLoss ε) (ev (A S₀)) (x₀, y) ≤ M := hbound S₀ (x₀, y)
  unfold Loss EpsilonInsensitiveLoss at h1
  dsimp only at h1
  have hdiff : c - y = |ε| + M + 1 := by dsimp [y]; ring
  have habs : |c - y| = |ε| + M + 1 := by
    rw [hdiff, abs_of_pos]
    have := abs_nonneg ε
    linarith
  have hε_le : ε ≤ |ε| := le_abs_self ε
  have hnot : ¬ (|c - y| ≤ ε) := by
    rw [habs]
    linarith
  rw [if_neg hnot, habs] at h1
  linarith
