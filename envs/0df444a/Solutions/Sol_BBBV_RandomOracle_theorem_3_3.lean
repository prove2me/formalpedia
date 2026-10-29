-- Prove2me | solution 1 for BBBV.RandomOracle.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T03:21:57.030992+00:00
-- url     : https://prove2.me/submissions/b331b8a7-71dd-45cf-a15f-893c8dfb0864

import Definitions.Def_BBBV_RandomOracle_QueryModel

open BBBV.RandomOracle

namespace BBBVHybridAttempt

variable {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
  [AddCommGroup R] [Fintype W] [DecidableEq W]

/-- Restrict a query state to the configurations whose query register belongs to `S`. -/
noncomputable def badPart (S : Finset X) (v : State X R W) : State X R W :=
  WithLp.toLp 2 fun c =>
    match c.1 with
    | none => 0
    | some y => if y ∈ S then v c else 0

/-- The norm of the restricted state is exactly the accumulated query magnitude. -/
theorem badPart_norm_sq (S : Finset X) (v : State X R W) :
    ‖badPart S v‖ ^ 2 = ∑ y ∈ S, queryMag y v := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp [badPart, queryMag, Fintype.sum_prod_type, Fintype.sum_option,
    Finset.sum_filter, Finset.sum_ite]
  calc
    _ = ∑ y : X, if y ∈ S then ∑ z : R, ∑ w : W, ‖v (some y, z, w)‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : y ∈ S <;> simp [h]
    _ = _ := by simp [Finset.sum_ite_mem]

/-- If the two oracles agree away from `S`, they act identically on its complement. -/
theorem oracle_agree_on_good (S : Finset X) (f g : X → R)
    (h : ∀ y ∉ S, f y = g y) (v : State X R W) :
    oracleOp f (v - badPart S v) = oracleOp g (v - badPart S v) := by
  classical
  ext ⟨o, z, w⟩
  cases o with
  | none => simp [oracleOp, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft', oracleEquiv, badPart]
  | some y =>
    by_cases hy : y ∈ S
    · simp [oracleOp, LinearIsometryEquiv.piLpCongrLeft_apply,
        Equiv.piCongrLeft', oracleEquiv, badPart, hy]
    · simp [oracleOp, LinearIsometryEquiv.piLpCongrLeft_apply,
        Equiv.piCongrLeft', oracleEquiv, badPart, hy, h y hy]

/-- Changing an oracle only at positions `S` moves a state by at most twice the square
root of its total query magnitude on `S`. -/
theorem oracle_difference_bound (S : Finset X) (f g : X → R)
    (h : ∀ y ∉ S, f y = g y) (v : State X R W) :
    ‖oracleOp f v - oracleOp g v‖ ≤ 2 * Real.sqrt (∑ y ∈ S, queryMag y v) := by
  have hgood := oracle_agree_on_good S f g h v
  have heq : oracleOp f v - oracleOp g v =
      oracleOp f (badPart S v) - oracleOp g (badPart S v) := by
    have hf : oracleOp f v = oracleOp f (v - badPart S v) + oracleOp f (badPart S v) := by
      rw [← map_add, sub_add_cancel]
    have hg : oracleOp g v = oracleOp g (v - badPart S v) + oracleOp g (badPart S v) := by
      rw [← map_add, sub_add_cancel]
    rw [hf, hg, hgood]
    abel
  rw [heq]
  calc
    _ ≤ ‖oracleOp f (badPart S v)‖ + ‖oracleOp g (badPart S v)‖ := norm_sub_le _ _
    _ = 2 * ‖badPart S v‖ := by simp [LinearIsometryEquiv.norm_map]; ring
    _ = _ := by rw [← Real.sqrt_sq (norm_nonneg (badPart S v)), badPart_norm_sq]

/-- The one-step error accumulated by the hybrid argument, indexed by query time. -/
noncomputable def hybridMagnitude {T : ℕ} (M : QueryAlg X R W T) (A : X → R)
    (F : Finset (Fin T × X)) (i : Fin T) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y => (i, y) ∈ F),
    queryMag y (state M (fun _ => A) i)

/-- The norm difference between the original and modified computations is at most the
sum of the oracle differences at the successive original states. -/
theorem hybrid_telescope {T : ℕ} (M : QueryAlg X R W T) (A : X → R)
    (F : Finset (Fin T × X)) (a : Fin T → X → R)
    (ha : ∀ i y, (i, y) ∉ F → a i y = A y) :
    ‖final M (fun _ => A) - final M a‖ ≤
      ∑ i : Fin T, 2 * Real.sqrt (hybridMagnitude M A F i) := by
  classical
  let d : ℕ → ℝ := fun n => ‖state M (fun _ => A) n - state M a n‖
  let q : Fin T → ℝ := hybridMagnitude M A F
  have hstep : ∀ i : Fin T, d (i + 1) ≤ d i + 2 * Real.sqrt (q i) := by
    intro i
    let S : Finset X := Finset.univ.filter (fun y => (i, y) ∈ F)
    have hgood : ∀ y ∉ S, A y = a i y := by
      intro y hy
      have hnot : (i, y) ∉ F := by simpa [S] using hy
      exact (ha i y hnot).symm
    have hdiff := oracle_difference_bound S A (a i) hgood (state M (fun _ => A) i)
    have horacle : ‖oracleOp (a i) (state M (fun _ => A) i) -
        oracleOp (a i) (state M a i)‖ = d i := by
      rw [← map_sub, LinearIsometryEquiv.norm_map]
    have htriangle := norm_sub_le_norm_sub_add_norm_sub (oracleOp A (state M (fun _ => A) i))
      (oracleOp (a i) (state M (fun _ => A) i)) (oracleOp (a i) (state M a i))
    have hnext : d (i + 1) = ‖oracleOp A (state M (fun _ => A) i) -
        oracleOp (a i) (state M a i)‖ := by
      simp [d, state, i.isLt, ← map_sub, LinearIsometryEquiv.norm_map]
    rw [hnext]
    change ‖oracleOp A (state M (fun _ => A) i) -
      oracleOp (a i) (state M a i)‖ ≤ d i + 2 * Real.sqrt (q i)
    dsimp [q, hybridMagnitude] at hdiff ⊢
    dsimp [S] at hdiff
    linarith
  let r : ℕ → ℝ := fun n => if h : n < T then 2 * Real.sqrt (q ⟨n, h⟩) else 0
  have hacc : ∀ n ≤ T, d n ≤ ∑ k ∈ Finset.range n, r k := by
    intro n hn
    induction n with
    | zero => simp [d, state]
    | succ n ih =>
      have hnlt : n < T := by omega
      have hprev := ih (by omega)
      have hnext := hstep ⟨n, hnlt⟩
      rw [Finset.sum_range_succ]
      have hprev' : d n + 2 * Real.sqrt (q ⟨n, hnlt⟩) ≤
          (∑ k ∈ Finset.range n, r k) + 2 * Real.sqrt (q ⟨n, hnlt⟩) := by linarith
      simpa only [r, dif_pos hnlt] using (le_trans hnext hprev')
  have hrange : (∑ k ∈ Finset.range T, r k) =
      ∑ i : Fin T, 2 * Real.sqrt (q i) := by
    rw [Finset.sum_fin_eq_sum_range]
  have h := hacc T le_rfl
  rw [hrange] at h
  simpa [d, q, final] using h

end BBBVHybridAttempt

open BBBVHybridAttempt

/-- The BBBV hybrid estimate with the factor two made explicit. -/
theorem solution {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    [AddCommGroup R] [Fintype W] [DecidableEq W] {T : ℕ} (M : QueryAlg X R W T) (A : X → R)
    (F : Finset (Fin T × X)) (a : Fin T → X → R)
    (ha : ∀ i y, (i, y) ∉ F → a i y = A y) (ε : ℝ) (hε : 0 < ε)
    (hF : ∑ p ∈ F, queryMag p.2 (state M (fun _ => A) p.1) ≤ ε ^ 2 / (T : ℝ)) :
    ‖final M (fun _ => A) - final M a‖ ≤ 2 * ε := by
  classical
  by_cases hT : T = 0
  · subst T
    simpa [final, state] using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε.le)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (Nat.pos_of_ne_zero hT)
  let q : Fin T → ℝ := hybridMagnitude M A F
  have hqnon : ∀ i, 0 ≤ q i := by
    intro i
    dsimp [q, hybridMagnitude, queryMag]
    positivity
  have hqsum : ∑ i, q i = ∑ p ∈ F, queryMag p.2 (state M (fun _ => A) p.1) := by
    dsimp [q, hybridMagnitude]
    simp only [Finset.sum_filter]
    rw [← Fintype.sum_prod_type']
    simp [Finset.sum_ite_mem]
  have hmass : (T : ℝ) * (∑ i, q i) ≤ ε ^ 2 := by
    rw [hqsum]
    simpa [mul_comm] using (le_div_iff₀ hTpos).1 hF
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin T => (1 : ℝ)) (fun i => Real.sqrt (q i))
  have hcs : (∑ i, Real.sqrt (q i)) ^ 2 ≤ (T : ℝ) * ∑ i, q i := by
    simpa [Real.sq_sqrt, hqnon] using hcauchy
  have hroot : 0 ≤ ∑ i, Real.sqrt (q i) := by positivity
  have hbound : (∑ i, Real.sqrt (q i)) ≤ ε := by nlinarith
  have h := hybrid_telescope M A F a ha
  dsimp [q] at hbound
  calc
    _ ≤ ∑ i : Fin T, 2 * Real.sqrt (hybridMagnitude M A F i) := h
    _ = 2 * ∑ i : Fin T, Real.sqrt (hybridMagnitude M A F i) := by rw [Finset.mul_sum]
    _ ≤ 2 * ε := by linarith

