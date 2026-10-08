-- Prove2me | solution 1 for GabayMercier.Approximation.eq_4_4
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:52:28.619659+00:00
-- url     : https://prove2.me/submissions/2898b34d-e707-4a0b-8cbf-8955ead948cc

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

/-- (4.4), with the extended-real difference rearranged. -/
theorem solution (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) (k : ℕ) (w : Vh k) :
    IsSolutionH (Ah k) f₂ b w ↔ f₂ (Ah k w) ≠ ⊤ ∧ ∀ u : Vh k,
      f₂ (Ah k w) + ((b (u - w) - inner ℝ (Ah k w) (Ah k (u - w)) : ℝ) : EReal) ≤
        f₂ (Ah k u) := by
  let bk : Vh k →L[ℝ] ℝ := b.comp (Vh k).subtypeL
  constructor
  · intro hw
    exact min_variational (Ah k) f₂ bk h.f₂_proper h.f₂_convex w hw.1 hw.2
  · rintro ⟨hw, hv⟩
    have ew := EReal.coe_toReal hw (h.f₂_proper.1 (Ah k w))
    constructor
    · unfold objectiveH
      rw [← ew, ← EReal.coe_add]
      exact EReal.coe_ne_top _
    · intro u
      by_cases hu : f₂ (Ah k u) = ⊤
      · unfold objectiveH
        rw [hu, EReal.coe_add_top]
        exact le_top
      have eu := EReal.coe_toReal hu (h.f₂_proper.1 (Ah k u))
      have hh := hv u
      rw [← ew, ← eu, ← EReal.coe_add, EReal.coe_le_coe_iff] at hh
      unfold objectiveH
      rw [← ew, ← eu, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hex := quadratic_expand (Ah k) bk w u 1
      simp only [one_smul, add_sub_cancel, one_mul, one_pow] at hex
      change halfSq (Ah k u) - b u =
        halfSq (Ah k w) - b w + (inner ℝ (Ah k w) (Ah k (u - w)) - b (u - w)) +
        1 / 2 * ‖Ah k (u - w)‖ ^ 2 at hex
      nlinarith [sq_nonneg ‖Ah k (u - w)‖]



#print axioms solution
