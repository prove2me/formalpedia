-- Prove2me | solution 1 for BanditAlgorithm.mdp_optimistic_bias_span_le_diameter
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-03T03:04:21.995048+00:00
-- url     : https://prove2.me/submissions/e698ca6e-369f-4b36-824a-edcfc3f6b848

import Definitions.Def_UCRL2Algorithm
import Theorems.Thm_BanditAlgorithm_mdp_span_le_gain_mul_diameter

open MeasureTheory ProbabilityTheory BanditAlgorithm

/-!
The bias of the optimistic plan committed to for a phase has span at most the
diameter of the true MDP, as soon as the true transition rows are among the rows
the plan is optimistic against.

The optimistic plan satisfies the average-reward Bellman inequality against
every row allowed by `C`, in particular against the true rows, so its bias
satisfies the Bellman inequality of `M` itself with gain `ρ ≤ 1`; the span of
any such bias is at most `ρ` times the diameter of `M`.
-/

theorem solution {S A : ℕ} [NeZero A] (hS : 0 < S) (M : FiniteMDP S A)
    (r : Fin S → Fin A → ℝ) (hMr : M.r = r) (hD : 1 ≤ mdpDiameter M)
    (C : Fin S → Fin A → Set (Fin S → ℝ))
    (hmem : ∀ s a, (fun s' ↦ ((M.P s a s' : ℝ))) ∈ C s a)
    (hex : ∃ (ρ : ℝ) (v : Fin S → ℝ) (f : Fin S → Fin A) (q : Fin S → Fin S → ℝ),
      IsOptimisticPlan r C ρ v f q)
    (x y : Fin S) :
    mdpOptimisticBias r C x - mdpOptimisticBias r C y ≤ mdpDiameter M := by
  classical
  haveI : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
  obtain ⟨hρ0, hρ1, hbell, -, -⟩ := isOptimisticPlan_mdpOptimisticPlan r C hex
  set ρ := mdpOptimisticGain r C
  set v := mdpOptimisticBias r C with hvdef
  -- the diameter is finite, since otherwise its real value would be `0`
  have hDne : mdpDiameterENN M ≠ ⊤ := by
    intro htop
    rw [mdpDiameter, htop, ENNReal.toReal_top] at hD
    linarith
  -- the bias is bounded, `Fin S` being finite and nonempty
  have hv : ∀ s, v s ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty v)
      (Finset.univ.sup' Finset.univ_nonempty v) := fun s ↦
    ⟨Finset.inf'_le _ (Finset.mem_univ s), Finset.le_sup' _ (Finset.mem_univ s)⟩
  -- the plan is optimistic against the true rows in particular
  have hbellM : ∀ s a, M.r s a + ∑ s', ((M.P s a s' : ℝ)) * v s' ≤ ρ + v s := by
    intro s a
    have := hbell s a _ (hmem s a)
    rw [hMr]
    exact this
  have hspan := BanditAlgorithm.mdp_span_le_gain_mul_diameter M ρ hρ0 v _ _ hv hbellM
    hDne x y
  have hD0 : (0 : ℝ) ≤ mdpDiameter M := by linarith
  calc v x - v y ≤ ρ * mdpDiameter M := hspan
    _ ≤ 1 * mdpDiameter M := by gcongr
    _ = mdpDiameter M := one_mul _
