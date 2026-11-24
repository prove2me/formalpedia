-- Prove2me | solution 1 for DelaunayStretch.Supplement.theorem_B_4_exactness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:59:40.67534+00:00
-- url     : https://prove2.me/submissions/984dc3c5-09ec-44d8-8d4b-e0e95c8b01de

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality
import Definitions.Def_DelaunayStretch_IsFeasiblePotential
import Definitions.Def_DelaunayStretch_Supplement_valueFunction
import Theorems.Thm_DelaunayStretch_theorem_3_9_potential_criterion
import Theorems.Thm_DelaunayStretch_lemma_3_6_chains_are_moves
import Theorems.Thm_DelaunayStretch_lemma_4_4_pencil

open DelaunayStretch DelaunayStretch.Supplement

namespace DelaunayStretch.Supplement.SolB4

/-! ## Elementary facts -/

theorem dist_sq_eq (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

theorem abs_clip_le (h t : ℝ) (hh : 0 ≤ h) : |clip h t| ≤ h := by
  unfold clip
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem radius_pos_of_two {O : Disk} {p q : ℂ} (hp : p ∈ O.boundary) (hq : q ∈ O.boundary)
    (hpq : p ≠ q) : 0 < O.radius := by
  have h1 : dist p O.center = O.radius := hp
  have h2 : dist q O.center = O.radius := hq
  by_contra h
  push Not at h
  have h0 : O.radius = 0 := le_antisymm h (h1 ▸ dist_nonneg)
  rw [h0, dist_eq_zero] at h1 h2
  exact hpq (h1.trans h2.symm)

theorem axisCrossing_im {a b : ℂ} (ha : 0 < a.im) (hb : b.im < 0) :
    (axisCrossing a b).im = 0 := by
  unfold axisCrossing
  have hne : a.im - b.im ≠ 0 := by linarith
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.sub_re, zero_mul, add_zero]
  field_simp
  ring

/-- The axis crossing of a chord is strictly inside the disk. -/
theorem crossing_inside {O : Disk} {a b : ℂ} (ha : 0 < a.im) (hb : b.im < 0)
    (hao : a ∈ O.boundary) (hbo : b ∈ O.boundary) :
    ((axisCrossing a b).re - O.center.re) ^ 2 + O.center.im ^ 2 < O.radius ^ 2 := by
  have h1 := dist_sq_eq a O.center
  have h2 := dist_sq_eq b O.center
  rw [show dist a O.center = O.radius from hao] at h1
  rw [show dist b O.center = O.radius from hbo] at h2
  have hd : 0 < a.im - b.im := by linarith
  set t := a.im / (a.im - b.im) with ht
  have ht0 : 0 < t := div_pos ha hd
  have ht1 : t < 1 := (div_lt_one hd).mpr (by linarith)
  have hre : (axisCrossing a b).re = a.re + t * (b.re - a.re) := by
    unfold axisCrossing; rw [← ht]; simp
  have him : (axisCrossing a b).im = a.im + t * (b.im - a.im) := by
    unfold axisCrossing; rw [← ht]; simp
  have hc0 : (axisCrossing a b).im = 0 := axisCrossing_im ha hb
  have key : ((axisCrossing a b).re - O.center.re) ^ 2 +
      ((axisCrossing a b).im - O.center.im) ^ 2
      = O.radius ^ 2 - t * (1 - t) * ((a.re - b.re) ^ 2 + (a.im - b.im) ^ 2) := by
    rw [hre, him]; linear_combination (t - 1) * h1 - t * h2
  rw [hc0] at key
  have hpos : 0 < t * (1 - t) * ((a.re - b.re) ^ 2 + (a.im - b.im) ^ 2) := by
    apply mul_pos (mul_pos ht0 (by linarith)); nlinarith
  nlinarith

theorem crossing_between {O : Disk} {a b : ℂ} (ha : 0 < a.im) (hb : b.im < 0)
    (hao : a ∈ O.boundary) (hbo : b ∈ O.boundary) :
    O.wMinus.re < (axisCrossing a b).re ∧ (axisCrossing a b).re < O.wPlus.re := by
  have h := crossing_inside ha hb hao hbo
  have hlt : |(axisCrossing a b).re - O.center.re| < O.axisHalfChord := by
    unfold Disk.axisHalfChord
    rw [Real.lt_sqrt (abs_nonneg _), sq_abs]; linarith
  rw [abs_lt] at hlt
  simp only [Disk.wMinus, Disk.wPlus]
  constructor <;> linarith

theorem wMinus_mem {O : Disk} {a b : ℂ} (ha : 0 < a.im) (hb : b.im < 0)
    (hao : a ∈ O.boundary) (hbo : b ∈ O.boundary) : O.wMinus ∈ O.boundary := by
  have h := crossing_inside ha hb hao hbo
  have hr : 0 < O.radius :=
    radius_pos_of_two hao hbo (by intro e; rw [e] at ha; linarith)
  have hs : O.axisHalfChord ^ 2 = O.radius ^ 2 - O.center.im ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg ((axisCrossing a b).re - O.center.re)])
  show dist O.wMinus O.center = O.radius
  rw [Complex.dist_eq_re_im]
  have e : (O.wMinus.re - O.center.re) ^ 2 + (O.wMinus.im - O.center.im) ^ 2 =
      O.radius ^ 2 := by
    simp only [Disk.wMinus]; nlinarith [hs]
  rw [e, Real.sqrt_sq hr.le]

theorem wPlus_mem {O : Disk} {a b : ℂ} (ha : 0 < a.im) (hb : b.im < 0)
    (hao : a ∈ O.boundary) (hbo : b ∈ O.boundary) : O.wPlus ∈ O.boundary := by
  have h := crossing_inside ha hb hao hbo
  have hr : 0 < O.radius :=
    radius_pos_of_two hao hbo (by intro e; rw [e] at ha; linarith)
  have hs : O.axisHalfChord ^ 2 = O.radius ^ 2 - O.center.im ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg ((axisCrossing a b).re - O.center.re)])
  show dist O.wPlus O.center = O.radius
  rw [Complex.dist_eq_re_im]
  have e : (O.wPlus.re - O.center.re) ^ 2 + (O.wPlus.im - O.center.im) ^ 2 =
      O.radius ^ 2 := by
    simp only [Disk.wPlus]; nlinarith [hs]
  rw [e, Real.sqrt_sq hr.le]

/-! ## Gate states along steps -/

theorem stepState_gate {s : GateState} (hs : s.IsGateState) {O' : Disk} {a' b' : ℂ}
    (hN : IsNextDisk s O' a' b') : (stepState s O' a' b').IsGateState := by
  obtain ⟨hset, ha, hb, -⟩ := hN
  have hA : a' ∈ s.O.boundary ∩ O'.boundary := by rw [hset]; simp
  have hB : b' ∈ s.O.boundary ∩ O'.boundary := by rw [hset]; simp
  refine ⟨radius_pos_of_two hA.2 hB.2 (by intro e; rw [e] at ha; linarith), hA.2, hB.2, ha, hb,
    abs_clip_le _ _ dist_nonneg⟩

theorem initialState_gate {O₁ O₂ : Disk} {a₁ b₁ : ℂ} (hip : IsInitialPair O₁ O₂ a₁ b₁) :
    (initialState O₁ O₂ a₁ b₁).IsGateState := by
  obtain ⟨hset, ha, hb, -⟩ := hip
  have hA : a₁ ∈ O₁.boundary ∩ O₂.boundary := by rw [hset]; simp
  have hB : b₁ ∈ O₁.boundary ∩ O₂.boundary := by rw [hset]; simp
  refine ⟨radius_pos_of_two hA.2 hB.2 (by intro e; rw [e] at ha; linarith), hA.2, hB.2, ha, hb,
    abs_clip_le _ _ dist_nonneg⟩

/-! ## Lemma B.2(1): the payoff is ½-Lipschitz in δ -/

theorem step_identity (μ δ α β h : ℝ) (hh : 0 ≤ h) :
    μ + (α + β - max (|δ + α - β| - h) 0) / 2 + clip h (δ + α - β) / 2 =
      min (μ + δ / 2 + α) (μ - δ / 2 + β + h) := by
  unfold clip
  rcases abs_cases (δ + α - β) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
    simp only [min_def, max_def] <;> split_ifs <;> linarith

theorem step_identity' (μ δ α β h : ℝ) (hh : 0 ≤ h) :
    μ + (α + β - max (|δ + α - β| - h) 0) / 2 - clip h (δ + α - β) / 2 =
      min (μ - δ / 2 + β) (μ + δ / 2 + α + h) := by
  unfold clip
  rcases abs_cases (δ + α - β) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
    simp only [min_def, max_def] <;> split_ifs <;> linarith

theorem payoff_lip_aux (U : ℝ) : ∀ (L : List (Disk × ℂ × ℂ)) (s t : GateState),
    s.O = t.O → s.aG = t.aG → s.bG = t.bG → ∀ μ ν : ℝ,
    |(μ + payoff U s L) - (ν + payoff U t L)| ≤
      max |(μ + s.δ / 2) - (ν + t.δ / 2)| |(μ - s.δ / 2) - (ν - t.δ / 2)| := by
  intro L
  induction L with
  | nil =>
    intro s t hO ha hb μ ν
    obtain ⟨O, aG, bG, δ⟩ := s
    obtain ⟨O', aG', bG', δ'⟩ := t
    simp only at hO ha hb
    subst hO ha hb
    simp only [payoff, finalCost, finalProgress, GateState.crossing]
    generalize O.upperArcLength aG O.wPlus = α
    generalize O.lowerArcLength bG O.wPlus = β
    generalize U * (O.wPlus.re - (axisCrossing aG bG).re) = P
    have m := abs_min_sub_min_le_max (μ + δ / 2 + α) (μ - δ / 2 + β) (ν + δ' / 2 + α)
      (ν - δ' / 2 + β)
    calc _ = |min (μ + δ / 2 + α) (μ - δ / 2 + β) - min (ν + δ' / 2 + α) (ν - δ' / 2 + β)| := by
          congr 1; simp only [min_def]; split_ifs <;> linarith
      _ ≤ _ := m.trans (le_of_eq (by congr 1 <;> congr 1 <;> ring))
  | cons x L ih =>
    intro s t hO ha hb μ ν
    obtain ⟨O', a', b'⟩ := x
    obtain ⟨O, aG, bG, δ⟩ := s
    obtain ⟨O₀, aG₀, bG₀, δ'⟩ := t
    simp only at hO ha hb
    subst hO ha hb
    have key := ih (stepState ⟨O, aG, bG, δ⟩ O' a' b') (stepState ⟨O, aG, bG, δ'⟩ O' a' b')
      rfl rfl rfl (μ + stepCost ⟨O, aG, bG, δ⟩ a' b' - U * stepProgress ⟨O, aG, bG, δ⟩ a' b')
      (ν + stepCost ⟨O, aG, bG, δ'⟩ a' b' - U * stepProgress ⟨O, aG, bG, δ⟩ a' b')
    simp only [payoff]
    have hP : stepProgress ⟨O, aG, bG, δ'⟩ a' b' = stepProgress ⟨O, aG, bG, δ⟩ a' b' := rfl
    rw [hP]
    refine (le_of_eq ?_).trans (key.trans ?_)
    · congr 1; ring
    · simp only [stepState, stepDiff, stepCost, moveNewDiff, moveCost]
      have hh : 0 ≤ dist a' b' := dist_nonneg
      generalize O.upperArcLength aG a' = α
      generalize O.lowerArcLength bG b' = β
      generalize dist a' b' = h at hh ⊢
      generalize U * stepProgress ⟨O, aG, bG, δ⟩ a' b' = P
      have i1 := step_identity μ δ α β h hh
      have i2 := step_identity' μ δ α β h hh
      have j1 := step_identity ν δ' α β h hh
      have j2 := step_identity' ν δ' α β h hh
      have m1 := abs_min_sub_min_le_max (μ + δ / 2 + α) (μ - δ / 2 + β + h)
        (ν + δ' / 2 + α) (ν - δ' / 2 + β + h)
      have m2 := abs_min_sub_min_le_max (μ - δ / 2 + β) (μ + δ / 2 + α + h)
        (ν - δ' / 2 + β) (ν + δ' / 2 + α + h)
      have q1 : |μ + δ / 2 + α - (ν + δ' / 2 + α)| = |μ + δ / 2 - (ν + δ' / 2)| := by ring_nf
      have q2 : |μ - δ / 2 + β + h - (ν - δ' / 2 + β + h)| = |μ - δ / 2 - (ν - δ' / 2)| := by
        ring_nf
      have q3 : |μ - δ / 2 + β - (ν - δ' / 2 + β)| = |μ - δ / 2 - (ν - δ' / 2)| := by ring_nf
      have q4 : |μ + δ / 2 + α + h - (ν + δ' / 2 + α + h)| = |μ + δ / 2 - (ν + δ' / 2)| := by
        ring_nf
      rw [q1, q2] at m1
      rw [q3, q4, max_comm] at m2
      apply max_le
      · calc _ = |min (μ + δ / 2 + α) (μ - δ / 2 + β + h) -
              min (ν + δ' / 2 + α) (ν - δ' / 2 + β + h)| := by
              congr 1; linarith
          _ ≤ _ := m1
      · calc _ = |min (μ - δ / 2 + β) (μ + δ / 2 + α + h) -
              min (ν - δ' / 2 + β) (ν + δ' / 2 + α + h)| := by
              congr 1; linarith
          _ ≤ _ := m2

theorem payoff_lip (U : ℝ) (L : List (Disk × ℂ × ℂ)) (s t : GateState)
    (hO : s.O = t.O) (ha : s.aG = t.aG) (hb : s.bG = t.bG) :
    payoff U s L ≤ payoff U t L + |s.δ - t.δ| / 2 := by
  have := payoff_lip_aux U L s t hO ha hb 0 0
  have e1 : |0 + s.δ / 2 - (0 + t.δ / 2)| = |s.δ - t.δ| / 2 := by
    rw [show (0 : ℝ) + s.δ / 2 - (0 + t.δ / 2) = (s.δ - t.δ) / 2 by ring, abs_div]; norm_num
  have e2 : |0 - s.δ / 2 - (0 - t.δ / 2)| = |s.δ - t.δ| / 2 := by
    rw [show (0 : ℝ) - s.δ / 2 - (0 - t.δ / 2) = -((s.δ - t.δ) / 2) by ring, abs_neg, abs_div]
    norm_num
  rw [e1, e2, max_self, zero_add, zero_add] at this
  linarith [le_abs_self (payoff U s L - payoff U t L)]

theorem isContinuation_congr : ∀ (L : List (Disk × ℂ × ℂ)) (s t : GateState),
    s.O = t.O → s.aG = t.aG → s.bG = t.bG → IsContinuation s L → IsContinuation t L := by
  intro L
  induction L with
  | nil => intros; trivial
  | cons x L ih =>
    intro s t hO ha hb h
    obtain ⟨O', a', b'⟩ := x
    obtain ⟨O, aG, bG, δ⟩ := s
    obtain ⟨O₀, aG₀, bG₀, δ'⟩ := t
    simp only at hO ha hb
    subst hO ha hb
    exact ⟨h.1, ih (stepState ⟨O, aG, bG, δ⟩ O' a' b') _ rfl rfl rfl h.2⟩

/-! ## Gate states of a continuation -/

/-- The `k`-th gate state of the continuation `L` from `s`. -/
noncomputable def gs : GateState → List (Disk × ℂ × ℂ) → ℕ → GateState
  | s, _, 0 => s
  | s, [], _ + 1 => s
  | s, (O', a', b') :: L, k + 1 => gs (stepState s O' a' b') L k

@[simp] theorem gs_zero (s : GateState) (L : List (Disk × ℂ × ℂ)) : gs s L 0 = s := by
  cases L <;> rfl

theorem gs_cons (s : GateState) (O' : Disk) (a' b' : ℂ) (L : List (Disk × ℂ × ℂ)) (k : ℕ) :
    gs s ((O', a', b') :: L) (k + 1) = gs (stepState s O' a' b') L k := rfl

theorem gs_step : ∀ (L : List (Disk × ℂ × ℂ)) (s : GateState) (k : ℕ), k < L.length →
    gs s L (k + 1) =
      stepState (gs s L k) (gs s L (k + 1)).O (gs s L (k + 1)).aG (gs s L (k + 1)).bG := by
  intro L
  induction L with
  | nil => intro s k hk; simp at hk
  | cons x L ih =>
    intro s k hk
    obtain ⟨O', a', b'⟩ := x
    cases k with
    | zero => rw [gs_cons, gs_zero, gs_zero]; rfl
    | succ k =>
      rw [gs_cons, gs_cons]
      exact ih _ k (by simpa using hk)

theorem gs_next : ∀ (L : List (Disk × ℂ × ℂ)) (s : GateState), IsContinuation s L →
    ∀ k, k < L.length →
    IsNextDisk (gs s L k) (gs s L (k + 1)).O (gs s L (k + 1)).aG (gs s L (k + 1)).bG := by
  intro L
  induction L with
  | nil => intro s _ k hk; simp at hk
  | cons x L ih =>
    intro s hL k hk
    obtain ⟨O', a', b'⟩ := x
    cases k with
    | zero => rw [gs_cons, gs_zero, gs_zero]; exact hL.1
    | succ k =>
      rw [gs_cons, gs_cons]
      exact ih _ hL.2 k (by simpa using hk)

theorem gs_gate : ∀ (L : List (Disk × ℂ × ℂ)) (s : GateState), s.IsGateState →
    IsContinuation s L → ∀ k, k ≤ L.length → (gs s L k).IsGateState := by
  intro L
  induction L with
  | nil => intro s hs _ k hk; simp at hk; subst hk; simpa using hs
  | cons x L ih =>
    intro s hs hL k hk
    obtain ⟨O', a', b'⟩ := x
    cases k with
    | zero => simpa using hs
    | succ k =>
      rw [gs_cons]
      exact ih _ (stepState_gate hs hL.1) hL.2 k (by simpa using hk)

theorem payoff_eq_sum (U : ℝ) : ∀ (L : List (Disk × ℂ × ℂ)) (s : GateState),
    payoff U s L = ∑ k ∈ Finset.range L.length,
      (stepCost (gs s L k) (gs s L (k + 1)).aG (gs s L (k + 1)).bG -
        U * stepProgress (gs s L k) (gs s L (k + 1)).aG (gs s L (k + 1)).bG) +
      (finalCost (gs s L L.length) - U * finalProgress (gs s L L.length)) := by
  intro L
  induction L with
  | nil => intro s; simp [payoff]
  | cons x L ih =>
    intro s
    obtain ⟨O', a', b'⟩ := x
    rw [payoff, ih, List.length_cons, Finset.sum_range_succ']
    simp only [gs_cons, gs_zero]
    simp only [stepState]
    ring

/-! ## Lemma B.3(2): an initial pair followed by a continuation is a disk chain -/

/-- The chain `(O₁, s₁.O, O⁽¹⁾, …, O⁽ᵐ⁾; w₋(O₁), w₊(Oₙ))`. -/
noncomputable def mkChain (O₁ : Disk) (s₁ : GateState) (L : List (Disk × ℂ × ℂ)) : DiskChain where
  n := L.length + 2
  O := fun i => if i = 1 then O₁ else (gs s₁ L (i - 2)).O
  u := O₁.wMinus
  v := (gs s₁ L L.length).O.wPlus
  a := fun i => (gs s₁ L (i - 1)).aG
  b := fun i => (gs s₁ L (i - 1)).bG

section mk
variable (O₁ : Disk) (s₁ : GateState) (L : List (Disk × ℂ × ℂ))

theorem mk_n : (mkChain O₁ s₁ L).n = L.length + 2 := rfl
theorem mk_O1 : (mkChain O₁ s₁ L).O 1 = O₁ := by simp [mkChain]
theorem mk_O (k : ℕ) : (mkChain O₁ s₁ L).O (k + 2) = (gs s₁ L k).O := by simp [mkChain]
theorem mk_a (k : ℕ) : (mkChain O₁ s₁ L).a (k + 1) = (gs s₁ L k).aG := by simp [mkChain]
theorem mk_b (k : ℕ) : (mkChain O₁ s₁ L).b (k + 1) = (gs s₁ L k).bG := by simp [mkChain]
theorem mk_u : (mkChain O₁ s₁ L).u = O₁.wMinus := rfl
theorem mk_v : (mkChain O₁ s₁ L).v = (gs s₁ L L.length).O.wPlus := rfl
theorem mk_c0 : (mkChain O₁ s₁ L).c 0 = O₁.wMinus := by simp [DiskChain.c, mkChain]
theorem mk_cn : (mkChain O₁ s₁ L).c (L.length + 2) = (gs s₁ L L.length).O.wPlus := by
  simp [DiskChain.c, mkChain]
theorem mk_c (k : ℕ) (hk : k ≤ L.length) :
    (mkChain O₁ s₁ L).c (k + 1) = (gs s₁ L k).crossing := by
  unfold DiskChain.c
  rw [if_neg (by omega), mk_n, if_neg (by omega), mk_a, mk_b]
  rfl

end mk

theorem lt_of_chain (f : ℕ → ℝ) (n : ℕ) (h : ∀ i, i + 1 ≤ n → f i < f (i + 1)) :
    ∀ k, 1 ≤ k → k ≤ n → f 0 < f k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro hn; exact h 0 hn
  | succ k hk ih => intro hn; exact (ih (by omega)).trans (h k hn)

theorem mk_isDiskChain (O₁ : Disk) (s₁ : GateState) (L : List (Disk × ℂ × ℂ))
    (hip : IsInitialPair O₁ s₁.O s₁.aG s₁.bG) (hs₁ : s₁.IsGateState)
    (hL : IsContinuation s₁ L) : (mkChain O₁ s₁ L).IsDiskChain := by
  have hG := gs_gate L s₁ hs₁ hL
  have hN := gs_next L s₁ hL
  obtain ⟨hset, ha1, hb1, hc1⟩ := hip
  have hA : s₁.aG ∈ O₁.boundary ∩ s₁.O.boundary := by rw [hset]; simp
  have hB : s₁.bG ∈ O₁.boundary ∩ s₁.O.boundary := by rw [hset]; simp
  have hC3 : ∀ i, i + 1 ≤ (mkChain O₁ s₁ L).n →
      ((mkChain O₁ s₁ L).c i).re < ((mkChain O₁ s₁ L).c (i + 1)).re := by
    intro i hi
    rw [mk_n] at hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [mk_c0, mk_c _ _ _ 0 (by omega), gs_zero]
      exact (crossing_between ha1 hb1 hA.1 hB.1).1
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rcases (show k = L.length ∨ k < L.length by omega) with rfl | hk
    · rw [mk_c _ _ _ _ le_rfl, show L.length + 1 + 1 = L.length + 2 by ring, mk_cn]
      obtain ⟨-, h1, h2, h3, h4, -⟩ := hG L.length le_rfl
      exact (crossing_between h3 h4 h1 h2).2
    · rw [mk_c _ _ _ _ hk.le, mk_c _ _ _ (k + 1) hk]
      exact (hN k hk).2.2.2.2.1
  refine ⟨by rw [mk_n]; omega, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, hC3, ?_⟩
  · intro i h1 h2
    rw [mk_n] at h2
    rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi
    · rw [mk_O1]; exact radius_pos_of_two hA.1 hB.1 (by intro e; rw [e] at ha1; linarith)
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      rw [mk_O]; exact (hG k (by omega)).1
  · rw [mk_O1, mk_u]; exact wMinus_mem ha1 hb1 hA.1 hB.1
  · rw [mk_n, mk_O, mk_v]
    obtain ⟨-, h1, h2, h3, h4, -⟩ := hG L.length le_rfl
    exact wPlus_mem h3 h4 h1 h2
  · have := lt_of_chain (fun i => ((mkChain O₁ s₁ L).c i).re) _ hC3 (L.length + 2)
      (by omega) (by rw [mk_n])
    rwa [mk_c0, mk_cn, ← mk_u O₁ s₁ L, ← mk_v O₁ s₁ L] at this
  · intro i h1 h2
    rw [mk_n] at h2
    rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi
    · rw [mk_O1, show (1 : ℕ) + 1 = 0 + 2 from rfl, mk_O, gs_zero,
        show (1 : ℕ) = 0 + 1 from rfl, mk_a, mk_b, gs_zero]
      exact ⟨hset, ha1, hb1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      rw [mk_O, show k + 2 + 1 = (k + 1) + 2 by ring, mk_O, show k + 2 = (k + 1) + 1 by ring,
        mk_a, mk_b]
      obtain ⟨h1, h2, h3, -⟩ := hN k (by omega)
      exact ⟨h1, h2, h3⟩
  · intro i h1 h2
    rw [mk_n] at h2
    rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi
    · rw [mk_O1, show (1 : ℕ) + 1 = 0 + 2 from rfl, mk_O, gs_zero]
      exact hc1
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      rw [mk_O, show k + 2 + 1 = (k + 1) + 2 by ring, mk_O]
      exact (hN k (by omega)).2.2.2.1
  · intro i h1 h2
    rw [mk_n] at h2
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    rw [mk_O, show k + 2 - 1 = k + 1 by omega, mk_a, mk_b, show k + 2 = (k + 1) + 1 by ring,
      mk_a, mk_b]
    have := hN k (by omega)
    exact ⟨this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩

theorem chain_bound' (U : ℝ) (hCI : ChainInequality U) (O₁ : Disk) (s₁ : GateState)
    (hip : IsInitialPair O₁ s₁.O s₁.aG s₁.bG) (hs₁e : initialState O₁ s₁.O s₁.aG s₁.bG = s₁)
    (L : List (Disk × ℂ × ℂ)) (hL : IsContinuation s₁ L) :
    initialCost O₁ s₁.aG s₁.bG - U * initialProgress O₁ s₁.aG s₁.bG + payoff U s₁ L ≤ 0 := by
  have hs₁ : s₁.IsGateState := hs₁e ▸ initialState_gate hip
  have hC := mk_isDiskChain O₁ s₁ L hip hs₁ hL
  have hn : 2 ≤ (mkChain O₁ s₁ L).n := by rw [mk_n]; omega
  have h36 := lemma_3_6_chains_are_moves (mkChain O₁ s₁ L) hC hn
  dsimp only at h36
  obtain ⟨⟨-, -, hinit, hstep, -⟩, -, hP⟩ := h36
  have eO1 : (mkChain O₁ s₁ L).O 1 = O₁ := mk_O1 O₁ s₁ L
  have eO2 : (mkChain O₁ s₁ L).O 2 = s₁.O := (mk_O O₁ s₁ L 0).trans (by rw [gs_zero])
  have ea1 : (mkChain O₁ s₁ L).a 1 = s₁.aG := (mk_a O₁ s₁ L 0).trans (by rw [gs_zero])
  have eb1 : (mkChain O₁ s₁ L).b 1 = s₁.bG := (mk_b O₁ s₁ L 0).trans (by rw [gs_zero])
  have hid : ∀ j, j ≤ L.length →
      (⟨(mkChain O₁ s₁ L).O (j + 1 + 1), (mkChain O₁ s₁ L).a (j + 1),
        (mkChain O₁ s₁ L).b (j + 1), (mkChain O₁ s₁ L).delta (j + 1)⟩ : GateState) =
        gs s₁ L j := by
    intro j hj
    induction j with
    | zero =>
      rw [gs_zero]
      have h : initialState ((mkChain O₁ s₁ L).O 1) ((mkChain O₁ s₁ L).O 2)
          ((mkChain O₁ s₁ L).a 1) ((mkChain O₁ s₁ L).b 1) =
          ⟨(mkChain O₁ s₁ L).O 2, (mkChain O₁ s₁ L).a 1, (mkChain O₁ s₁ L).b 1,
            (mkChain O₁ s₁ L).delta 1⟩ := hinit
      show (⟨(mkChain O₁ s₁ L).O 2, (mkChain O₁ s₁ L).a 1, (mkChain O₁ s₁ L).b 1,
            (mkChain O₁ s₁ L).delta 1⟩ : GateState) = s₁
      rw [← h, eO1, eO2, ea1, eb1, hs₁e]
    | succ j ih =>
      have h : stepState ⟨(mkChain O₁ s₁ L).O (j + 1 + 1), (mkChain O₁ s₁ L).a (j + 1),
          (mkChain O₁ s₁ L).b (j + 1), (mkChain O₁ s₁ L).delta (j + 1)⟩
          ((mkChain O₁ s₁ L).O (j + 1 + 2)) ((mkChain O₁ s₁ L).a (j + 1 + 1))
          ((mkChain O₁ s₁ L).b (j + 1 + 1)) =
          ⟨(mkChain O₁ s₁ L).O (j + 1 + 1 + 1), (mkChain O₁ s₁ L).a (j + 1 + 1),
            (mkChain O₁ s₁ L).b (j + 1 + 1), (mkChain O₁ s₁ L).delta (j + 1 + 1)⟩ :=
        (hstep (j + 1) (by omega) (by rw [mk_n]; omega)).2
      rw [ih (by omega), mk_O, mk_a, mk_b] at h
      rw [mk_O, mk_a, mk_b, ← h]
      exact (gs_step L s₁ j (by omega)).symm
  have hsum := hP U
  rw [mk_n, show L.length + 2 - 1 = L.length + 1 by omega, Finset.sum_Ico_eq_sum_range,
    show L.length + 1 - 1 = L.length by omega, hid L.length le_rfl, eO1, ea1, eb1] at hsum
  have hsum2 : ∑ k ∈ Finset.range L.length,
      (stepCost ⟨(mkChain O₁ s₁ L).O (1 + k + 1), (mkChain O₁ s₁ L).a (1 + k),
        (mkChain O₁ s₁ L).b (1 + k), (mkChain O₁ s₁ L).delta (1 + k)⟩
        ((mkChain O₁ s₁ L).a (1 + k + 1)) ((mkChain O₁ s₁ L).b (1 + k + 1)) -
       U * stepProgress ⟨(mkChain O₁ s₁ L).O (1 + k + 1), (mkChain O₁ s₁ L).a (1 + k),
        (mkChain O₁ s₁ L).b (1 + k), (mkChain O₁ s₁ L).delta (1 + k)⟩
        ((mkChain O₁ s₁ L).a (1 + k + 1)) ((mkChain O₁ s₁ L).b (1 + k + 1))) =
      ∑ k ∈ Finset.range L.length,
      (stepCost (gs s₁ L k) (gs s₁ L (k + 1)).aG (gs s₁ L (k + 1)).bG -
        U * stepProgress (gs s₁ L k) (gs s₁ L (k + 1)).aG (gs s₁ L (k + 1)).bG) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show 1 + k = k + 1 by ring, hid k hk.le, mk_a, mk_b]
  rw [hsum2, add_assoc, ← payoff_eq_sum] at hsum
  have hci := hCI _ hC
  linarith

theorem chain_bound (U : ℝ) (hCI : ChainInequality U) (O₁ O₂ : Disk) (a₁ b₁ : ℂ)
    (hip : IsInitialPair O₁ O₂ a₁ b₁) (L : List (Disk × ℂ × ℂ))
    (hL : IsContinuation (initialState O₁ O₂ a₁ b₁) L) :
    initialCost O₁ a₁ b₁ - U * initialProgress O₁ a₁ b₁ +
      payoff U (initialState O₁ O₂ a₁ b₁) L ≤ 0 :=
  chain_bound' U hCI O₁ (initialState O₁ O₂ a₁ b₁) hip rfl L hL

/-! ## The value function -/

theorem V_ge (U : ℝ) {s : GateState} {L : List (Disk × ℂ × ℂ)} (h : IsContinuation s L) :
    ((payoff U s L : ℝ) : EReal) ≤ valueFunction U s :=
  le_iSup (fun Γ : {Γ : List (Disk × ℂ × ℂ) // IsContinuation s Γ} =>
    ((payoff U s Γ.1 : ℝ) : EReal)) ⟨L, h⟩

theorem V_le (U : ℝ) {s : GateState} {K : ℝ}
    (h : ∀ L, IsContinuation s L → payoff U s L ≤ K) : valueFunction U s ≤ (K : EReal) :=
  iSup_le fun Γ => EReal.coe_le_coe_iff.mpr (h Γ.1 Γ.2)

theorem V_fin (U : ℝ) {s : GateState} {K : ℝ}
    (h : ∀ L, IsContinuation s L → payoff U s L ≤ K) :
    valueFunction U s = ((valueFunction U s).toReal : EReal) ∧
      (valueFunction U s).toReal ≤ K := by
  have h1 := V_le U h
  have h2 : ((payoff U s [] : ℝ) : EReal) ≤ valueFunction U s := V_ge U (s := s) (L := []) trivial
  have ht : valueFunction U s ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top K) h1
  have hb : valueFunction U s ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h2
  refine ⟨(EReal.coe_toReal ht hb).symm, ?_⟩
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal ht hb]; exact h1

theorem payoff_le_toReal (U : ℝ) {s : GateState} {K : ℝ}
    (h : ∀ L, IsContinuation s L → payoff U s L ≤ K) {L : List (Disk × ℂ × ℂ)}
    (hL : IsContinuation s L) : payoff U s L ≤ (valueFunction U s).toReal := by
  have := V_ge U hL
  rw [(V_fin U h).1] at this
  exact EReal.coe_le_coe_iff.mp this

theorem step_bound (U : ℝ) {s : GateState} {K : ℝ}
    (hK : ∀ L, IsContinuation s L → payoff U s L ≤ K) {O' : Disk} {a' b' : ℂ}
    (hN : IsNextDisk s O' a' b') : ∀ L, IsContinuation (stepState s O' a' b') L →
      payoff U (stepState s O' a' b') L ≤
        (valueFunction U s).toReal - (stepCost s a' b' - U * stepProgress s a' b') := by
  intro L hL
  have := payoff_le_toReal U hK (L := (O', a', b') :: L) ⟨hN, hL⟩
  simp only [payoff] at this
  linarith

theorem bounded (U : ℝ) (hCI : ChainInequality U) {s : GateState} (hs : s.IsGateState) :
    ∃ K : ℝ, ∀ L, IsContinuation s L → payoff U s L ≤ K := by
  obtain ⟨-, haG, hbG, ha, hb, -⟩ := hs
  have P := lemma_4_4_pencil s.aG s.bG ha hb
  obtain ⟨X, hX⟩ := (P.1 s.O).mp ⟨haG, hbG⟩
  obtain ⟨hI, hc⟩ := P.2.1 (X - 1) X (by linarith)
  have hip : IsInitialPair (pencilDisk s.aG s.bG (X - 1)) s.O s.aG s.bG := by
    rw [hX]; exact ⟨hI, ha, hb, hc.mpr (by linarith)⟩
  refine ⟨-(initialCost (pencilDisk s.aG s.bG (X - 1)) s.aG s.bG -
      U * initialProgress (pencilDisk s.aG s.bG (X - 1)) s.aG s.bG) +
      |s.δ - (initialState (pencilDisk s.aG s.bG (X - 1)) s.O s.aG s.bG).δ| / 2, ?_⟩
  intro L hL
  have hL' := isContinuation_congr L s
    (initialState (pencilDisk s.aG s.bG (X - 1)) s.O s.aG s.bG) rfl rfl rfl hL
  have h1 := chain_bound U hCI _ s.O s.aG s.bG hip L hL'
  have h2 := payoff_lip U L s (initialState (pencilDisk s.aG s.bG (X - 1)) s.O s.aG s.bG)
    rfl rfl rfl
  linarith

theorem feasible (U : ℝ) (hCI : ChainInequality U) :
    IsFeasiblePotential U (fun s => (valueFunction U s).toReal) := by
  refine ⟨?_, ?_, ?_⟩
  · intro O₁ O₂ a₁ b₁ hip
    have hb : ∀ L, IsContinuation (initialState O₁ O₂ a₁ b₁) L →
        payoff U (initialState O₁ O₂ a₁ b₁) L ≤
          -(initialCost O₁ a₁ b₁ - U * initialProgress O₁ a₁ b₁) := by
      intro L hL; have := chain_bound U hCI O₁ O₂ a₁ b₁ hip L hL; linarith
    have := (V_fin U hb).2
    simp only; linarith
  · intro s hs O' a' b' hN
    obtain ⟨K, hK⟩ := bounded U hCI hs
    have := (V_fin U (step_bound U hK hN)).2
    simp only; linarith
  · intro s hs
    obtain ⟨K, hK⟩ := bounded U hCI hs
    have := payoff_le_toReal U hK (L := []) trivial
    simpa [payoff] using this

theorem value_eq (U : ℝ) (hCI : ChainInequality U) {s : GateState} (hs : s.IsGateState) :
    valueFunction U s =
      max ((finalCost s - U * finalProgress s : ℝ) : EReal)
        (⨆ (O' : Disk) (a' : ℂ) (b' : ℂ) (_ : IsNextDisk s O' a' b'),
          ((stepCost s a' b' - U * stepProgress s a' b' : ℝ) : EReal) +
            valueFunction U (stepState s O' a' b')) := by
  obtain ⟨K, hK⟩ := bounded U hCI hs
  apply le_antisymm
  · apply iSup_le
    rintro ⟨L, hL⟩
    cases L with
    | nil => exact le_max_left _ _
    | cons x L =>
      obtain ⟨O', a', b'⟩ := x
      obtain ⟨hN, hL'⟩ := hL
      refine le_trans ?_ (le_max_right _ _)
      refine le_trans ?_ (le_iSup_of_le O' (le_iSup_of_le a' (le_iSup_of_le b'
        (le_iSup_of_le hN le_rfl))))
      show (((stepCost s a' b' - U * stepProgress s a' b') +
        payoff U (stepState s O' a' b') L : ℝ) : EReal) ≤ _
      rw [EReal.coe_add]
      exact add_le_add_right (V_ge U hL') _
  · apply max_le
    · exact V_ge U (s := s) (L := []) trivial
    · apply iSup_le; intro O'; apply iSup_le; intro a'; apply iSup_le; intro b'
      apply iSup_le; intro hN
      obtain ⟨e, hle⟩ := V_fin U (step_bound U hK hN)
      rw [e, (V_fin U hK).1, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith

theorem payoff_le_W (U : ℝ) (W : GateState → ℝ) (hW : IsFeasiblePotential U W) :
    ∀ (L : List (Disk × ℂ × ℂ)) (s : GateState), s.IsGateState → IsContinuation s L →
      payoff U s L ≤ W s := by
  intro L
  induction L with
  | nil => intro s hs _; exact hW.2.2 s hs
  | cons x L ih =>
    intro s hs hL
    obtain ⟨O', a', b'⟩ := x
    have h1 := hW.2.1 s hs O' a' b' hL.1
    have h2 := ih _ (stepState_gate hs hL.1) hL.2
    simp only [payoff]
    linarith

end DelaunayStretch.Supplement.SolB4

open DelaunayStretch.Supplement.SolB4 in
theorem solution (U : ℝ) (hU : Real.pi / 2 ≤ U) :
    (ChainInequality U ↔ ∃ W : GateState → ℝ, IsFeasiblePotential U W) ∧
    (ChainInequality U →
      (∀ s : GateState, s.IsGateState → ∃ r : ℝ, valueFunction U s = (r : EReal)) ∧
      (∀ s : GateState, s.IsGateState →
        valueFunction U s =
          max ((finalCost s - U * finalProgress s : ℝ) : EReal)
            (⨆ (O' : Disk) (a' : ℂ) (b' : ℂ) (_ : IsNextDisk s O' a' b'),
              ((stepCost s a' b' - U * stepProgress s a' b' : ℝ) : EReal) +
                valueFunction U (stepState s O' a' b'))) ∧
      IsFeasiblePotential U (fun s => (valueFunction U s).toReal) ∧
      (∀ W : GateState → ℝ, IsFeasiblePotential U W →
        ∀ s : GateState, s.IsGateState → valueFunction U s ≤ (W s : EReal))) := by
  refine ⟨⟨fun h => ⟨_, feasible U h⟩, theorem_3_9_potential_criterion U hU⟩,
    fun hCI => ⟨?_, fun s hs => value_eq U hCI hs, feasible U hCI, ?_⟩⟩
  · intro s hs
    obtain ⟨K, hK⟩ := bounded U hCI hs
    exact ⟨_, (V_fin U hK).1⟩
  · intro W hW s hs
    exact V_le U (fun L hL => payoff_le_W U W hW L s hs hL)
