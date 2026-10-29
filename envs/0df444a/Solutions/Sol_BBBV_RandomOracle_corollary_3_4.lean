-- Prove2me | solution 1 for BBBV.RandomOracle.corollary_3_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T04:03:31.099591+00:00
-- url     : https://prove2.me/submissions/c9007353-5e3f-43a9-8c97-349740a1bcbf

import Theorems.Thm_BBBV_RandomOracle_theorem_3_3

open BBBV.RandomOracle

private theorem state_norm_one {X R W : Type} [Fintype X] [DecidableEq X]
    [Fintype R] [DecidableEq R] [AddCommGroup R] [Fintype W] [DecidableEq W]
    {T : ℕ} (M : QueryAlg X R W T) (g : Fin T → X → R) (n : ℕ) :
    ‖state M g n‖ = 1 := by
  induction n with
  | zero => exact M.init_norm
  | succ n ih =>
    simp only [state]
    split
    · simp only [LinearIsometryEquiv.norm_map, ih]
    · exact ih

private theorem query_magnitude_sum_le_one {X R W : Type} [Fintype X] [DecidableEq X]
    [Fintype R] [DecidableEq R] [AddCommGroup R] [Fintype W] [DecidableEq W]
    {T : ℕ} (M : QueryAlg X R W T) (g : Fin T → X → R) (n : ℕ) :
    (∑ y, queryMag y (state M g n)) ≤ 1 := by
  have hsq := EuclideanSpace.norm_sq_eq (state M g n)
  rw [state_norm_one M g n] at hsq
  simp only [one_pow, Config, Fintype.sum_prod_type, Fintype.sum_option] at hsq
  have hnon : 0 ≤ ∑ z : R, ∑ w : W, ‖state M g n (none, z, w)‖ ^ 2 := by positivity
  simp only [queryMag]
  linarith

theorem solution {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    [AddCommGroup R] [Fintype W] [DecidableEq W] {T : ℕ} (M : QueryAlg X R W T)
    (A : X → R) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset X, (S.card : ℝ) ≤ 4 * (T : ℝ) ^ 2 / ε ^ 2 ∧
      ∀ y ∉ S, ∀ Ay : X → R, (∀ x, x ≠ y → Ay x = A x) →
        ‖final M (fun _ => A) - final M (fun _ => Ay)‖ ≤ ε := by
  classical
  by_cases hT : T = 0
  · subst T
    refine ⟨∅, by simp, ?_⟩
    intro y hy Ay hAy
    simpa [final, state] using hε.le
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (Nat.pos_of_ne_zero hT)
  let q : X → ℝ := fun y => ∑ i : Fin T, queryMag y (state M (fun _ => A) i)
  have hqnon : ∀ y, 0 ≤ q y := by
    intro y
    dsimp [q, queryMag]
    positivity
  have hqtotal : (∑ y, q y) ≤ T := by
    dsimp [q]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i : Fin T, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        query_magnitude_sum_le_one M (fun _ => A) i
      _ = T := by simp
  let θ : ℝ := ε ^ 2 / (4 * T)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let S : Finset X := Finset.univ.filter (fun y => θ < q y)
  refine ⟨S, ?_, ?_⟩
  · have hbound : (S.card : ℝ) * θ ≤ ∑ y ∈ S, q y := by
      calc
        _ = ∑ _y ∈ S, θ := by simp
        _ ≤ _ := Finset.sum_le_sum fun y hy => (Finset.mem_filter.mp hy).2.le
    have hsub : (∑ y ∈ S, q y) ≤ ∑ y, q y :=
      Finset.sum_le_univ_sum_of_nonneg fun y => hqnon y
    have hh : (S.card : ℝ) * (ε ^ 2 / (4 * T)) ≤ T := by
      exact le_trans (by simpa [θ] using hbound) (le_trans hsub hqtotal)
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    have hh' : ((S.card : ℝ) * ε ^ 2) / (4 * T) ≤ T := by
      simpa [mul_div_assoc] using hh
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * T)).1 hh'
    nlinarith
  · intro y hy Ay hAy
    have hyq : q y ≤ θ := by
      have := hy
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
      exact this
    let F : Finset (Fin T × X) := Finset.univ ×ˢ {y}
    have ha : ∀ i z, (i, z) ∉ F → Ay z = A z := by
      intro i z h
      apply hAy z
      intro hz
      apply h
      simp [F, hz]
    have hF : ∑ p ∈ F, queryMag p.2 (state M (fun _ => A) p.1) ≤
        (ε / 2) ^ 2 / (T : ℝ) := by
      have heq : (∑ p ∈ F, queryMag p.2 (state M (fun _ => A) p.1)) = q y := by
        simp [F, q, Finset.sum_product]
      rw [heq]
      have : θ = (ε / 2) ^ 2 / (T : ℝ) := by dsimp [θ]; ring
      simpa [this] using hyq
    have h := BBBV.RandomOracle.theorem_3_3 M A F (fun _ => Ay) ha (ε / 2)
      (by positivity) hF
    convert h using 1 <;> ring
