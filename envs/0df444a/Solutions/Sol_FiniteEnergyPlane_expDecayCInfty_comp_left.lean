-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInfty_comp_left
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T21:45:29.184848+00:00
-- url     : https://prove2.me/submissions/dd6308f2-f242-457b-a83d-a56dc0a3b607

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib



/-!
# B decay calculus: `ExpDecayCInfty` under composition.

* `bt_expDecay_comp_left`: `G ∘ a` decays when `a` decays and `G` is smooth near `0`, `G 0 = 0`.
* `bt_expDecay_comp_right`: `F (p + c + E p)` decays like `F` when `E` decays.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Nat

noncomputable section

/-- The Faà di Bruno trick: if all derivatives of order `1..m` of `f` at `x` are at most `C' η`,
with `η ∈ (0, 1]`, then they are at most `D ^ i` with `D = c η^{1/m}`, `c = max 1 C'`. -/
lemma bt_pow_bound {m : ℕ} (hm : 0 < m) {η C' : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {i : ℕ}
    (hi1 : 1 ≤ i) (him : i ≤ m) :
    C' * η ≤ (max 1 C' * η ^ ((1 : ℝ) / m)) ^ i := by
  have hc1 : (1 : ℝ) ≤ max 1 C' := le_max_left _ _
  have hc0 : (0 : ℝ) ≤ max 1 C' := zero_le_one.trans hc1
  rw [mul_pow, ← Real.rpow_natCast (η ^ ((1 : ℝ) / m)), ← Real.rpow_mul hη0.le]
  have hexp : (1 : ℝ) / m * i ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by exact_mod_cast hm)]
    exact_mod_cast him
  have h1 : η ≤ η ^ ((1 : ℝ) / m * i) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hη0 hη1 hexp
  have h2 : max 1 C' ≤ max 1 C' ^ i := le_self_pow₀ hc1 (by omega)
  calc C' * η ≤ max 1 C' * η := mul_le_mul_of_nonneg_right (le_max_right _ _) hη0.le
    _ ≤ max 1 C' ^ i * η ^ ((1 : ℝ) / m * i) :=
        mul_le_mul h2 h1 hη0.le (pow_nonneg hc0 _)

lemma bt_pow_m {m : ℕ} (hm : 0 < m) {η c : ℝ} (hη0 : 0 < η) :
    (c * η ^ ((1 : ℝ) / m)) ^ m = c ^ m * η := by
  rw [mul_pow, ← Real.rpow_natCast (η ^ ((1 : ℝ) / m)), ← Real.rpow_mul hη0.le]
  rw [div_mul_cancel₀ (1 : ℝ) (by exact_mod_cast hm.ne'), Real.rpow_one]

/-- Uniform bounds of the derivatives of a smooth map on a compact subset of an open set. -/
lemma bt_exists_bound_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : E → F} {U K : Set E} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ m, ∀ y ∈ K, ‖iteratedFDeriv ℝ i G y‖ ≤ B := by
  have hc : ∀ i : ℕ, ContinuousOn (fun y => ‖iteratedFDeriv ℝ i G y‖) K := by
    intro i
    have h1 := hG.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top)
      hU.uniqueDiffOn
    have h2 : ContinuousOn (iteratedFDeriv ℝ i G) U :=
      h1.congr fun y hy => (iteratedFDerivWithin_of_isOpen i hU hy).symm
    exact (h2.mono hKU).norm
  choose B hB using fun i => (hK.image_of_continuousOn (hc i)).bddAbove
  refine ⟨∑ i ∈ Finset.range (m + 1), |B i|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun i hi y hy => ?_⟩
  have h := hB i ⟨y, hy, rfl⟩
  exact h.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |B i|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))

/-- Composition on the left with a map smooth near `0` and vanishing at `0`. -/
theorem bt_expDecay_comp_left {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E → F) (r : ℝ) (hr : 0 < r) (hG : ContDiffOn ℝ ∞ G (ball 0 r)) (hG0 : G 0 = 0)
    (a : ℝ × ℝ → E) (b : ℝ) (hb : 0 < b) (ha : ExpDecayCInfty a b) :
    ExpDecayCInfty (fun p => G (a p)) b := by
  obtain ⟨⟨s₀, hs⟩, hl⟩ := ha
  obtain ⟨C₀, s₁, hC₀⟩ := hl 0
  -- eventually `‖a‖ ≤ r / 2`
  have htend : Tendsto (fun s : ℝ => |C₀| * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.exp (-(b * s))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)
    simpa using h1.const_mul |C₀|
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 (htend.eventually (ge_mem_nhds (half_pos hr)))
  set S := max (max s₀ s₁) (max s₂ 0) with hS
  have hSs₀ : s₀ ≤ S := le_trans (le_max_left _ _) (le_max_left _ _)
  have hSs₁ : s₁ ≤ S := le_trans (le_max_right _ _) (le_max_left _ _)
  have hSs₂ : s₂ ≤ S := le_trans (le_max_left _ _) (le_max_right _ _)
  have hS0 : 0 ≤ S := le_trans (le_max_right _ _) (le_max_right _ _)
  set U : Set (ℝ × ℝ) := Ioi S ×ˢ univ with hU
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have haU : ContDiffOn ℝ ∞ a U := hs.mono (prod_mono (Ioi_subset_Ioi hSs₀) subset_rfl)
  have hsmall : ∀ p : ℝ × ℝ, S ≤ p.1 → ‖a p‖ ≤ r / 2 := by
    intro p hp
    have h0 := hC₀ p.1 (hSs₁.trans hp) p.2
    rw [norm_iteratedFDeriv_zero] at h0
    exact (h0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)).trans
      (hs₂ _ (hSs₂.trans hp))
  have hmaps : MapsTo a U (ball 0 r) := fun p hp => by
    rw [mem_ball_zero_iff]
    exact (hsmall p (le_of_lt hp.1)).trans_lt (half_lt_self hr)
  have hK : IsCompact (closedBall (0 : E) (r / 2)) := isCompact_closedBall _ _
  have hKU : closedBall (0 : E) (r / 2) ⊆ ball 0 r := closedBall_subset_ball (half_lt_self hr)
  refine ⟨⟨S, hG.comp haU hmaps⟩, fun m => ?_⟩
  obtain ⟨B, hB0, hB⟩ := bt_exists_bound_iteratedFDeriv isOpen_ball hG hK hKU (max m 1)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- Lipschitz bound near `0`
    refine ⟨B * |C₀|, max S (s₁ + 1), fun s hs t => ?_⟩
    have hsS : S ≤ s := (le_max_left _ _).trans hs
    rw [norm_iteratedFDeriv_zero]
    have hdiff : ∀ y ∈ closedBall (0 : E) (r / 2), DifferentiableAt ℝ G y := fun y hy =>
      ((hG.contDiffAt (isOpen_ball.mem_nhds (hKU hy))).differentiableAt (by simp))
    have hder : ∀ y ∈ closedBall (0 : E) (r / 2), ‖fderiv ℝ G y‖ ≤ B := by
      intro y hy
      have := hB 1 (le_max_right _ _) y hy
      rwa [norm_iteratedFDeriv_one] at this
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hder
      (convex_closedBall (0 : E) (r / 2)) (mem_closedBall_self (half_pos hr).le) (mem_closedBall_zero_iff.2 (hsmall (s, t) hsS))
    rw [hG0, sub_zero, sub_zero] at hmv
    have h0 := hC₀ s (hSs₁.trans hsS) t
    rw [norm_iteratedFDeriv_zero] at h0
    calc ‖G (a (s, t))‖ ≤ B * ‖a (s, t)‖ := hmv
      _ ≤ B * (|C₀| * Real.exp (-(b * s))) :=
          mul_le_mul_of_nonneg_left
            (h0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)) hB0
      _ = B * |C₀| * Real.exp (-(b * s)) := by ring
  · -- derivatives of order `1..m` of `a` are at most `C' e^{-bs}`
    choose Ci si hCi using hl
    set C' : ℝ := ∑ i ∈ Finset.range (m + 1), |Ci i| with hC'
    set T : ℝ := max S (∑ i ∈ Finset.range (m + 1), |si i|) with hT
    have hsiT : ∀ i ≤ m, si i ≤ T := fun i hi =>
      (le_abs_self _).trans ((Finset.single_le_sum (f := fun i => |si i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))).trans (le_max_right _ _))
    have hCiC : ∀ i ≤ m, Ci i ≤ C' := fun i hi =>
      (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Ci i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
    refine ⟨m ! * B * max 1 C' ^ m, max T (S + 1), fun s hs t => ?_⟩
    have hsT : T ≤ s := (le_max_left _ _).trans hs
    have hsS : S < s := by linarith [le_max_right T (S + 1)]
    have hpU : (s, t) ∈ U := ⟨hsS, trivial⟩
    set η := Real.exp (-(b * s)) with hη
    have hη0 : 0 < η := Real.exp_pos _
    have hη1 : η ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := m) (N := ∞) hG haU
      (by exact_mod_cast le_top) isOpen_ball.uniqueDiffOn hUo.uniqueDiffOn hmaps hpU
      (C := B) (D := max 1 C' * η ^ ((1 : ℝ) / m)) (fun i hi => ?_) (fun i hi1 hi => ?_)
    · rw [iteratedFDerivWithin_of_isOpen m hUo hpU] at key
      have e : (G ∘ a) = fun p => G (a p) := rfl
      rw [e, bt_pow_m hm hη0] at key
      calc _ ≤ _ := key
        _ = m ! * B * max 1 C' ^ m * η := by ring
    · rw [iteratedFDerivWithin_of_isOpen i isOpen_ball (hmaps hpU)]
      exact hB i (hi.trans (le_max_left _ _)) _
        (mem_closedBall_zero_iff.2 (hsmall _ hsS.le))
    · rw [iteratedFDerivWithin_of_isOpen i hUo hpU]
      refine (hCi i s ((hsiT i hi).trans hsT) t).trans ?_
      refine le_trans ?_ (bt_pow_bound hm hη0 hη1 hi1 hi (C' := C'))
      exact mul_le_mul_of_nonneg_right (hCiC i hi) hη0.le

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff Real

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E → F) (r : ℝ) (hr : 0 < r) (hG : ContDiffOn ℝ ∞ G (ball 0 r)) (hG0 : G 0 = 0)
    (a : ℝ × ℝ → E) (b : ℝ) (hb : 0 < b) (ha : ExpDecayCInfty a b) :
    ExpDecayCInfty (fun p => G (a p)) b :=
  bt_expDecay_comp_left G r hr hG hG0 a b hb ha
