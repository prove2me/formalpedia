-- Prove2me | solution 1 for FoundationsRL.FuncApprox.optimism_and_elliptic_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:21:14.390498+00:00
-- url     : https://prove2.me/submissions/34dd2da4-0953-4764-9584-addead560e26

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB

open FoundationsRL.RLBasics FoundationsRL.FuncApprox

/-- Counterexample: the constant `C'` is chosen before the confidence-radius constant `C`, so it
cannot absorb `C`. Given `C' > 0`, take one state, one action, `H = 1`, zero reward, the
class `Qc = Bool` with `true ↦ Q⋆` and `false ↦` the constant `C' + 1`, the rank-one
factorization `X ≡ 1`, `W(Q) = E_0(π, Q)` (the residual does not depend on the policy here), the
empty history, `n = 1`, `β = 1`, `k = 1` and `C` larger than both squared residuals. With no
data every `Q` is retained, both hypotheses hold, but the elliptic norm of `W(false)` is
`(C' + 1)² > C' · β`. -/
theorem solution : ¬ (∃ C' : ℝ, 0 < C' ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
        (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
        (d : ℕ) (X : Policy S A H → ℕ → Fin d → ℝ) (W : (ℕ → S → A → ℝ) → ℕ → Fin d → ℝ)
        (_hfact : ∀ π, IsPolicy H π → ∀ Qf : Qc, ∀ h : ℕ, h < H →
            bellmanResidual M π h (qeval Qf) = ∑ j : Fin d, X π h j * W (qeval Qf) h j)
        (hist : List (Trajectory S A H)) (n : ℕ) (β C : ℝ) (k : ℕ),
        (∀ Qf ∈ confSet M qeval hist n β k, ∀ h : Fin H,
            ∑ i ∈ Finset.range k,
              (bellmanResidual M (iterPolicy M qeval hist n β i) h.1 (qeval Qf)) ^ 2 ≤ C * β) →
        q0 ∈ confSet M qeval hist n β k →
        (∀ Qf ∈ confSet M qeval hist n β k, ∀ h : Fin H,
            elliptNormSq
              ((List.range k).map (fun i => X (iterPolicy M qeval hist n β i) h.1))
              (W (qeval Qf) h.1) ≤ C' * β)
        ∧ initValue M qeval (bestQ M qeval hist n β k) ≥ ∑ s : S, M.d1 s * Vstar M 0 s) := by
  rintro ⟨C', hC', H⟩
  let M : EpisodicMDP Unit Unit 1 :=
    { P := fun _ _ _ _ => 1, R := fun _ _ _ => 0, d1 := fun _ => 1,
      P_nonneg := fun _ _ _ _ => zero_le_one, P_sum_one := fun _ _ _ => by simp,
      d1_nonneg := fun _ => zero_le_one, d1_sum_one := by simp }
  let c : ℝ := C' + 1
  let qeval : Bool → ℕ → Unit → Unit → ℝ := fun b =>
    if b then (fun h s a => if h < 1 then Qstar M h s a else 0) else (fun _ _ _ => c)
  let π0 : Policy Unit Unit 1 := fun _ _ _ => 1
  -- on one state and one action the layer-0 residual does not depend on the policy
  have hres : ∀ π : Policy Unit Unit 1, IsPolicy 1 π → ∀ Q : ℕ → Unit → Unit → ℝ,
      bellmanResidual M π 0 Q = bellmanResidual M π0 0 Q := by
    intro π hπ Q
    have h1 : π 0 () () = 1 := by simpa using (hπ 0 zero_lt_one ()).2
    simp [bellmanResidual, layerStateActionExp, stateDist, h1, π0]
  let X : Policy Unit Unit 1 → ℕ → Fin 1 → ℝ := fun _ _ _ => 1
  let W : (ℕ → Unit → Unit → ℝ) → ℕ → Fin 1 → ℝ := fun Q h _ => bellmanResidual M π0 h Q
  have hfact : ∀ π, IsPolicy 1 π → ∀ Qf : Bool, ∀ h : ℕ, h < 1 →
      bellmanResidual M π h (qeval Qf) = ∑ j : Fin 1, X π h j * W (qeval Qf) h j := by
    intro π hπ Qf h hh
    obtain rfl : h = 0 := by omega
    simp [X, W, hres π hπ]
  let r : Bool → ℝ := fun b =>
    bellmanResidual M (iterPolicy M qeval [] 1 1 0) 0 (qeval b)
  have hmem : ∀ b : Bool, b ∈ confSet M qeval [] 1 1 1 := by
    intro b
    simp [confSet, residualEst, batch]
  have key := H (M := M) qeval true (by funext h s a; simp [qeval]) 1 X W hfact [] 1 1
    (r true ^ 2 + r false ^ 2 + 1) 1
    (by
      intro Qf _ h
      have hh : h.1 = 0 := by omega
      simp only [Finset.range_one, Finset.sum_singleton, hh, mul_one]
      cases Qf
      · change r false ^ 2 ≤ _; nlinarith [sq_nonneg (r true)]
      · change r true ^ 2 ≤ _; nlinarith [sq_nonneg (r false)])
    (hmem true)
  have h2 := key.1 false (hmem false) ⟨0, zero_lt_one⟩
  have hW : ∀ j : Fin 1, W (qeval false) 0 j = c := by
    intro j
    simp [W, qeval, bellmanResidual, layerStateActionExp, stateDist, π0, M]
  have hE : elliptNormSq ((List.range 1).map
      (fun i => X (iterPolicy M qeval [] 1 1 i) (⟨0, zero_lt_one⟩ : Fin 1).1))
      (W (qeval false) (⟨0, zero_lt_one⟩ : Fin 1).1) = c ^ 2 := by
    simp only [elliptNormSq, List.range_one, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, Fin.sum_univ_one, X, one_mul]
    exact congrArg (· ^ 2) (hW 0)
  rw [hE] at h2
  simp only [c] at h2
  nlinarith
