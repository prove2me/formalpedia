-- Prove2me | solution 1 for ComputableDistributionsWaveMission.derivative_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T16:57:58.554911+00:00
-- url     : https://prove2.me/submissions/b7da5d17-aee7-444b-a3bd-0ab4a640cd67

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_MissionTargets

open ComputableAnalysis ComputableDistributions

theorem solution : ComputableDistributions.TestDerivativeUniquenessTarget := by
  intro dimension φ ψ h
  -- one increment step: agreement at `alpha` gives agreement at `alpha + e_i`
  have step : ∀ (alpha : MultiIndex dimension) (i : Fin dimension),
      (∀ x, (φ.derivative alpha x).Equiv (ψ.derivative alpha x)) →
      ∀ x, (φ.derivative (incrementIndex alpha i) x).Equiv
        (ψ.derivative (incrementIndex alpha i) x) := by
    intro alpha i hα x
    have hφ := φ.partialDerivative alpha i x
    have hψ := ψ.partialDerivative alpha i x
    have hφ' := BracketDerivative.congr_function hφ
      (fun r _ => ψ.derivative_valid alpha (replaceCoordinate x i r))
      (fun r _ => hα (replaceCoordinate x i r))
    exact BracketDerivative.unique hφ' hψ
  -- agreement for every index vanishing in the coordinates `≥ m`
  have main : ∀ m : Nat, ∀ alpha : MultiIndex dimension,
      (∀ j : Fin dimension, m ≤ j.val → alpha j = 0) →
      ∀ x, (φ.derivative alpha x).Equiv (ψ.derivative alpha x) := by
    intro m
    induction m with
    | zero =>
      intro alpha hz x
      have : alpha = zeroIndex dimension := by
        funext j
        exact hz j (Nat.zero_le _)
      subst this
      exact h x
    | succ m ih =>
      by_cases hm : m < dimension
      · let c : Fin dimension := ⟨m, hm⟩
        have inner : ∀ t : Nat, ∀ beta : MultiIndex dimension,
            (∀ j : Fin dimension, m + 1 ≤ j.val → beta j = 0) → beta c = t →
            ∀ x, (φ.derivative beta x).Equiv (ψ.derivative beta x) := by
          intro t
          induction t with
          | zero =>
            intro beta hb hc
            apply ih
            intro j hj
            by_cases hjc : j.val = m
            · have : j = c := Fin.ext hjc
              rw [this]; exact hc
            · exact hb j (by omega)
          | succ t iht =>
            intro beta hb hc x
            let beta' : MultiIndex dimension := fun j => if j = c then t else beta j
            have hinc : incrementIndex beta' c = beta := by
              funext j
              by_cases hj : j = c
              · subst hj; simp [incrementIndex, beta', hc]
              · simp [incrementIndex, beta', hj]
            rw [← hinc]
            refine step beta' c (iht beta' ?_ ?_) x
            · intro j hj
              have hjc : j ≠ c := by
                intro e; rw [e] at hj; simp [c] at hj; omega
              simp [beta', hjc, hb j hj]
            · simp [beta']
        intro alpha hz
        exact inner (alpha c) alpha hz rfl
      · intro alpha hz
        apply ih
        intro j hj
        exact hz j (by omega)
  intro alpha x
  exact main dimension alpha (fun j hj => absurd j.isLt (by omega)) x
