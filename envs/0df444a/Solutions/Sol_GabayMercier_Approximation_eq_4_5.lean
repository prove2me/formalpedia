-- Prove2me | solution 1 for GabayMercier.Approximation.eq_4_5
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:53:46.068559+00:00
-- url     : https://prove2.me/submissions/decd1469-9617-48d8-90e7-1d5a9e9503b5

import Mathlib
import Definitions.Def_GabayMercier_Approximation_Model
open InertialFB.IFB GabayMercier.Approximation
set_option maxHeartbeats 800000

private lemma quadratic_expand {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (B : X →L[ℝ] Y) (b : X →L[ℝ] ℝ) (w u : X) (t : ℝ) :
    halfSq (B (w + t • (u - w))) - b (w + t • (u - w)) =
    halfSq (B w) - b w + t * (inner ℝ (B w) (B (u - w)) - b (u - w)) +
      t ^ 2 * (1 / 2 * ‖B (u - w)‖ ^ 2) := by
  simp only [halfSq, map_add, map_smul, norm_add_sq_real, inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, smul_eq_mul]
  ring

private lemma min_variational {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (B : X →L[ℝ] Y) (f : Y → EReal) (b : X →L[ℝ] ℝ)
    (hp : IsProperFn f) (hc : IsConvexFn f) (w : X)
    (hw : ((halfSq (B w) - b w : ℝ) : EReal) + f (B w) ≠ ⊤)
    (hm : ∀ u, ((halfSq (B w) - b w : ℝ) : EReal) + f (B w) ≤
      ((halfSq (B u) - b u : ℝ) : EReal) + f (B u)) :
    f (B w) ≠ ⊤ ∧ ∀ u, f (B w) +
      ((b (u - w) - inner ℝ (B w) (B (u - w)) : ℝ) : EReal) ≤ f (B u) := by
  have hfw : f (B w) ≠ ⊤ := by
    intro h
    rw [h, EReal.coe_add_top] at hw
    exact hw rfl
  have ew := EReal.coe_toReal hfw (hp.1 (B w))
  refine ⟨hfw, ?_⟩
  intro u
  by_cases hfu : f (B u) = ⊤
  · rw [hfu]; exact le_top
  have eu := EReal.coe_toReal hfu (hp.1 (B u))
  have hseg : ∀ t : ℝ, 0 < t → t ≤ 1 →
      halfSq (B w) - b w + (f (B w)).toReal ≤
      halfSq (B (w + t • (u - w))) - b (w + t • (u - w)) +
        ((1 - t) * (f (B w)).toReal + t * (f (B u)).toReal) := by
    intro t ht ht1
    have hepi := hc
      (show (B w, (f (B w)).toReal) ∈ {p : Y × ℝ | f p.1 ≤ (p.2 : EReal)} by
        simp only [Set.mem_setOf_eq]; rw [ew])
      (show (B u, (f (B u)).toReal) ∈ {p : Y × ℝ | f p.1 ≤ (p.2 : EReal)} by
        simp only [Set.mem_setOf_eq]; rw [eu])
      (by linarith : 0 ≤ 1 - t) (le_of_lt ht) (by ring : (1 - t) + t = 1)
    change f ((1 - t) • B w + t • B u) ≤
      (((1 - t) * (f (B w)).toReal + t * (f (B u)).toReal : ℝ) : EReal) at hepi
    have hz : (1 - t) • B w + t • B u = B (w + t • (u - w)) := by
      simp only [map_add, map_smul, map_sub]
      module
    rw [hz] at hepi
    have hh := (hm (w + t • (u - w))).trans (add_le_add_right hepi _)
    rw [← ew, ← EReal.coe_add, ← EReal.coe_add] at hh
    exact EReal.coe_le_coe_iff.mp hh
  let c : ℝ := (f (B w)).toReal + b (u - w) - inner ℝ (B w) (B (u - w)) -
    (f (B u)).toReal
  let K : ℝ := 1 / 2 * ‖B (u - w)‖ ^ 2
  have hsmall : ∀ t : ℝ, 0 < t → t ≤ 1 → c ≤ t * K := by
    intro t ht ht1
    have hh := hseg t ht ht1
    rw [quadratic_expand] at hh
    dsimp [c, K]
    nlinarith
  have hcle : c ≤ 0 := by
    by_contra hn
    have hcpos : 0 < c := lt_of_not_ge hn
    have hk : 0 ≤ K := by dsimp [K]; positivity
    let t := min (1 : ℝ) (c / (2 * (K + 1)))
    have ht : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htc : t ≤ c / (2 * (K + 1)) := min_le_right _ _
    have hprod : t * (2 * (K + 1)) ≤ c := (le_div_iff₀ (by positivity)).mp htc
    have hh := hsmall t ht ht1
    nlinarith
  rw [← ew, ← eu, ← EReal.coe_add, EReal.coe_le_coe_iff]
  dsimp [c] at hcle
  linarith



variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (4.5), with the sign corrected by setting the competitor in (4.4) to zero. -/
theorem solution (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) (hzero : f₂ 0 ≠ ⊤)
    (k : ℕ) (w : Vh k) (hw : IsSolutionH (Ah k) f₂ b w) :
    (((‖Ah k w‖ ^ 2 - b w : ℝ) : EReal) + f₂ (Ah k w)) ≤ f₂ 0 := by
  let bk : Vh k →L[ℝ] ℝ := b.comp (Vh k).subtypeL
  have hh := (min_variational (Ah k) f₂ bk h.f₂_proper h.f₂_convex w hw.1 hw.2).2 0
  change f₂ (Ah k w) +
    ((b ((0 : Vh k) - w) - inner ℝ (Ah k w) (Ah k ((0 : Vh k) - w)) : ℝ) : EReal) ≤
    f₂ (Ah k 0) at hh
  have he : b ((0 : Vh k) - w) - inner ℝ (Ah k w) (Ah k ((0 : Vh k) - w)) =
      ‖Ah k w‖ ^ 2 - b w := by
    simp only [Submodule.coe_zero, zero_sub, Submodule.coe_neg, map_neg, inner_neg_right, real_inner_self_eq_norm_sq]
    ring
  rw [he, map_zero] at hh
  simpa only [add_comm] using hh



#print axioms solution
