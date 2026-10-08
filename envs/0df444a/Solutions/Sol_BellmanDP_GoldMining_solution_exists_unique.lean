-- Prove2me | solution 1 for BellmanDP.GoldMining.solution_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:54:22.484792+00:00
-- url     : https://prove2.me/submissions/5afc12fc-6c46-43d7-bc31-ad498c7bd4ee

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model



namespace BellmanDP.GoldMining

open Filter Topology

lemma ge_geo_le {a b C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (h : ∀ N : ℕ, a ≤ b + C * q ^ N) :
    a ≤ b := by
  have ht : Tendsto (fun N : ℕ => b + C * q ^ N) atTop (𝓝 (b + C * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1))
  simp only [mul_zero, add_zero] at ht
  exact ge_of_tendsto' ht h

section Ex
variable (p₁ p₂ r₁ r₂ : ℝ) (hp₁ : |p₁| < 1) (hp₂ : |p₂| < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)

lemma ge_goldA_diff (u v : ℝ → ℝ → ℝ) (x y : ℝ) :
    |goldA p₁ r₁ u x y - goldA p₁ r₁ v x y| = |p₁| * |u ((1 - r₁) * x) y - v ((1 - r₁) * x) y| := by
  rw [← abs_mul]; unfold goldA; ring_nf

lemma ge_goldB_diff (u v : ℝ → ℝ → ℝ) (x y : ℝ) :
    |goldB p₂ r₂ u x y - goldB p₂ r₂ v x y| = |p₂| * |u x ((1 - r₂) * y) - v x ((1 - r₂) * y)| := by
  rw [← abs_mul]; unfold goldB; ring_nf

include hp₁ hp₂ hr₁0 hr₁1 hr₂0 hr₂1 in
lemma ge_cauchy : ∀ N : ℕ, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
    |goldIter p₁ p₂ r₁ r₂ (N + 1) x y - goldIter p₁ p₂ r₁ r₂ N x y| ≤
      (max |p₁| |p₂|) ^ N * (x + y) := by
  intro N
  induction N with
  | zero =>
    intro x y hx hy
    simp only [goldIter, goldA, goldB, add_zero, sub_zero, pow_zero, one_mul]
    have h1 : |p₁ * (r₁ * x)| ≤ x + y := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr₁0, abs_of_nonneg hx]
      have : r₁ * x ≤ x := by nlinarith
      have : |p₁| * (r₁ * x) ≤ r₁ * x := by nlinarith [abs_nonneg p₁, mul_nonneg hr₁0 hx]
      linarith
    have h2 : |p₂ * (r₂ * y)| ≤ x + y := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr₂0, abs_of_nonneg hy]
      have : r₂ * y ≤ y := by nlinarith
      have : |p₂| * (r₂ * y) ≤ r₂ * y := by nlinarith [abs_nonneg p₂, mul_nonneg hr₂0 hy]
      linarith
    have := abs_max_sub_max_le_max (p₁ * (r₁ * x)) (p₂ * (r₂ * y)) 0 0
    simp only [sub_zero, max_self] at this
    exact this.trans (max_le h1 h2)
  | succ N ih =>
    intro x y hx hy
    set q := max |p₁| |p₂|
    have hq0 : 0 ≤ q := le_max_of_le_left (abs_nonneg _)
    have hx' : 0 ≤ (1 - r₁) * x := mul_nonneg (by linarith) hx
    have hy' : 0 ≤ (1 - r₂) * y := mul_nonneg (by linarith) hy
    have hA : |goldA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ (N + 1)) x y - goldA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) x y|
        ≤ q ^ (N + 1) * (x + y) := by
      rw [ge_goldA_diff]
      have h1 := ih _ _ hx' hy
      have h2 : q ^ N * ((1 - r₁) * x + y) ≤ q ^ N * (x + y) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (pow_nonneg hq0 _)
      have h3 : |p₁| ≤ q := le_max_left _ _
      rw [pow_succ]
      calc |p₁| * |goldIter p₁ p₂ r₁ r₂ (N + 1) ((1 - r₁) * x) y - goldIter p₁ p₂ r₁ r₂ N ((1 - r₁) * x) y|
          ≤ |p₁| * (q ^ N * (x + y)) := mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
        _ ≤ q * (q ^ N * (x + y)) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = _ := by ring
    have hB : |goldB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ (N + 1)) x y - goldB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) x y|
        ≤ q ^ (N + 1) * (x + y) := by
      rw [ge_goldB_diff]
      have h1 := ih _ _ hx hy'
      have h2 : q ^ N * (x + (1 - r₂) * y) ≤ q ^ N * (x + y) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (pow_nonneg hq0 _)
      have h3 : |p₂| ≤ q := le_max_right _ _
      rw [pow_succ]
      calc |p₂| * |goldIter p₁ p₂ r₁ r₂ (N + 1) x ((1 - r₂) * y) - goldIter p₁ p₂ r₁ r₂ N x ((1 - r₂) * y)|
          ≤ |p₂| * (q ^ N * (x + y)) := mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
        _ ≤ q * (q ^ N * (x + y)) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = _ := by ring
    show |max (goldA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ (N + 1)) x y) (goldB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ (N + 1)) x y)
      - max (goldA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) x y) (goldB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) x y)| ≤ _
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le hA hB)

noncomputable def geLim (x y : ℝ) : ℝ := limUnder atTop (fun N => goldIter p₁ p₂ r₁ r₂ N x y)

include hp₁ hp₂ hr₁0 hr₁1 hr₂0 hr₂1 in
lemma ge_err (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (N : ℕ) :
    |goldIter p₁ p₂ r₁ r₂ N x y - geLim p₁ p₂ r₁ r₂ x y| ≤
      (x + y) / (1 - max |p₁| |p₂|) * (max |p₁| |p₂|) ^ N := by
  have hq1 : max |p₁| |p₂| < 1 := max_lt hp₁ hp₂
  have hu : ∀ N, dist (goldIter p₁ p₂ r₁ r₂ N x y) (goldIter p₁ p₂ r₁ r₂ (N + 1) x y) ≤
      (x + y) * (max |p₁| |p₂|) ^ N := by
    intro N
    rw [Real.dist_eq, abs_sub_comm, mul_comm]
    exact ge_cauchy p₁ p₂ r₁ r₂ hp₁ hp₂ hr₁0 hr₁1 hr₂0 hr₂1 N x y hx hy
  have hcs := cauchySeq_of_le_geometric _ _ hq1 hu
  have ht := hcs.tendsto_limUnder
  have := dist_le_of_le_geometric_of_tendsto _ _ hq1 hu ht N
  rw [Real.dist_eq] at this
  rw [div_mul_eq_mul_div]
  exact this

lemma ge_cont : ∀ N : ℕ, Continuous (Function.uncurry (goldIter p₁ p₂ r₁ r₂ N)) := by
  intro N
  induction N with
  | zero => simp only [goldIter]; exact continuous_const
  | succ N ih =>
    have e : Function.uncurry (goldIter p₁ p₂ r₁ r₂ (N + 1)) = fun z : ℝ × ℝ =>
        max (p₁ * (r₁ * z.1 + Function.uncurry (goldIter p₁ p₂ r₁ r₂ N) ((1 - r₁) * z.1, z.2)))
          (p₂ * (r₂ * z.2 + Function.uncurry (goldIter p₁ p₂ r₁ r₂ N) (z.1, (1 - r₂) * z.2))) := by
      funext z; simp [goldIter, goldA, goldB, Function.uncurry]
    rw [e]
    have c1 := ih.comp (by fun_prop : Continuous fun z : ℝ × ℝ => ((1 - r₁) * z.1, z.2))
    have c2 := ih.comp (by fun_prop : Continuous fun z : ℝ × ℝ => (z.1, (1 - r₂) * z.2))
    exact Continuous.max (continuous_const.mul ((continuous_const.mul continuous_fst).add c1))
      (continuous_const.mul ((continuous_const.mul continuous_snd).add c2))

end Ex

theorem exist_core (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁ : |p₁| < 1) (hp₂ : |p₂| < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ < 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ < 1) :
    ∃ f : ℝ → ℝ → ℝ, IsGoldMiningSolution p₁ p₂ r₁ r₂ f ∧ BoundedOnRectangles f ∧
      ContinuousOn (Function.uncurry f) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) ∧
      ∀ g : ℝ → ℝ → ℝ, IsGoldMiningSolution p₁ p₂ r₁ r₂ g → BoundedOnRectangles g →
        ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g x y = f x y := by
  have hr₁1' : r₁ ≤ 1 := hr₁1.le
  have hr₂1' : r₂ ≤ 1 := hr₂1.le
  have herr := ge_err p₁ p₂ r₁ r₂ hp₁ hp₂ hr₁0 hr₁1' hr₂0 hr₂1'
  set q := max |p₁| |p₂| with hqdef
  have hq0 : 0 ≤ q := le_max_of_le_left (abs_nonneg _)
  have hq1 : q < 1 := max_lt hp₁ hp₂
  have h1q : 0 < 1 - q := by linarith
  set F := geLim p₁ p₂ r₁ r₂ with hF
  have hpow : ∀ N : ℕ, q ^ (N + 1) = q ^ N * q := fun N => pow_succ q N
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    set E := (x + y) / (1 - q)
    have hE0 : 0 ≤ E := div_nonneg (by linarith) h1q.le
    have hx' : 0 ≤ (1 - r₁) * x := mul_nonneg (by linarith) hx
    have hy' : 0 ≤ (1 - r₂) * y := mul_nonneg (by linarith) hy
    have hA : ∀ N : ℕ, |goldA p₁ r₁ F x y - goldA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) x y| ≤ q * (E * q ^ N) := by
      intro N
      rw [ge_goldA_diff, abs_sub_comm]
      have h1 := herr _ _ hx' hy N
      have h2 : ((1 - r₁) * x + y) / (1 - q) * q ^ N ≤ E * q ^ N :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by nlinarith) h1q.le) (pow_nonneg hq0 _)
      exact mul_le_mul (le_max_left _ _) (h1.trans h2) (abs_nonneg _) hq0
    have hB : ∀ N : ℕ, |goldB p₂ r₂ F x y - goldB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) x y| ≤ q * (E * q ^ N) := by
      intro N
      rw [ge_goldB_diff, abs_sub_comm]
      have h1 := herr _ _ hx hy' N
      have h2 : (x + (1 - r₂) * y) / (1 - q) * q ^ N ≤ E * q ^ N :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by nlinarith) h1q.le) (pow_nonneg hq0 _)
      exact mul_le_mul (le_max_right _ _) (h1.trans h2) (abs_nonneg _) hq0
    have hM : ∀ N : ℕ, |max (goldA p₁ r₁ F x y) (goldB p₂ r₂ F x y) - goldIter p₁ p₂ r₁ r₂ (N + 1) x y|
        ≤ q * (E * q ^ N) := fun N => (abs_max_sub_max_le_max _ _ _ _).trans (max_le (hA N) (hB N))
    have hI : ∀ N : ℕ, |goldIter p₁ p₂ r₁ r₂ (N + 1) x y - F x y| ≤ E * q ^ N * q := by
      intro N; have h := herr x y hx hy (N + 1); rw [hpow, ← mul_assoc] at h; exact h
    have hqE : ∀ N : ℕ, 0 ≤ E * q ^ N := fun N => mul_nonneg hE0 (pow_nonneg hq0 _)
    apply le_antisymm
    · apply ge_geo_le hq0 hq1 (C := 2 * E)
      intro N
      have := (abs_sub_le_iff.1 (hM N)).2
      have := (abs_sub_le_iff.1 (hI N)).2
      have : q * (E * q ^ N) ≤ E * q ^ N := by nlinarith [hqE N]
      nlinarith [hqE N]
    · apply ge_geo_le hq0 hq1 (C := 2 * E)
      intro N
      have := (abs_sub_le_iff.1 (hM N)).1
      have := (abs_sub_le_iff.1 (hI N)).1
      have : q * (E * q ^ N) ≤ E * q ^ N := by nlinarith [hqE N]
      nlinarith [hqE N]
  · intro X Y
    refine ⟨(X + Y) / (1 - q), fun x y hx hxX hy hyY => ?_⟩
    have := herr x y hx hy 0
    simp only [goldIter, zero_sub, abs_neg, pow_zero, mul_one] at this
    exact this.trans (div_le_div_of_nonneg_right (by linarith) h1q.le)
  · have hcont := ge_cont p₁ p₂ r₁ r₂
    refine TendstoLocallyUniformlyOn.continuousOn (F := fun N => Function.uncurry (goldIter p₁ p₂ r₁ r₂ N))
      (p := atTop) ?_ (Eventually.of_forall fun N => (hcont N).continuousOn).frequently
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε z hz
    set U : Set (ℝ × ℝ) := {w | w.1 < z.1 + 1 ∧ w.2 < z.2 + 1}
    have hU : U ∈ 𝓝 z := by
      apply IsOpen.mem_nhds
      · exact (isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_snd continuous_const)
      · exact ⟨by linarith, by linarith⟩
    refine ⟨(Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) ∩ U, inter_mem_nhdsWithin _ hU, ?_⟩
    set C := (z.1 + 1 + (z.2 + 1)) / (1 - q)
    have ht : Tendsto (fun N : ℕ => C * q ^ N) atTop (𝓝 (C * 0)) :=
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [mul_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with N hN
    rintro w ⟨⟨hw1, hw2⟩, hw3, hw4⟩
    simp only [Set.mem_Ici] at hw1 hw2
    rw [Real.dist_eq, abs_sub_comm]
    have := herr w.1 w.2 hw1 hw2 N
    refine lt_of_le_of_lt (this.trans ?_) hN
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq0 _)
    exact div_le_div_of_nonneg_right (by linarith) h1q.le
  · intro g hg hgb x0 y0 hx0 hy0
    obtain ⟨M, hM⟩ := hgb x0 y0
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x0 y0 hx0 le_rfl hy0 le_rfl)
    have claim : ∀ N : ℕ, ∀ x y : ℝ, 0 ≤ x → x ≤ x0 → 0 ≤ y → y ≤ y0 →
        |g x y - goldIter p₁ p₂ r₁ r₂ N x y| ≤ q ^ N * M := by
      intro N
      induction N with
      | zero => intro x y hx hxX hy hyY; simpa [goldIter] using hM x y hx hxX hy hyY
      | succ N ih =>
        intro x y hx hxX hy hyY
        have hx' : 0 ≤ (1 - r₁) * x := mul_nonneg (by linarith) hx
        have hx'' : (1 - r₁) * x ≤ x0 := by nlinarith
        have hy' : 0 ≤ (1 - r₂) * y := mul_nonneg (by linarith) hy
        have hy'' : (1 - r₂) * y ≤ y0 := by nlinarith
        have hA : |goldA p₁ r₁ g x y - goldA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) x y| ≤ q ^ (N + 1) * M := by
          rw [ge_goldA_diff, pow_succ, mul_comm (q ^ N) q, mul_assoc]
          exact mul_le_mul (le_max_left _ _) (ih _ _ hx' hx'' hy hyY) (abs_nonneg _) hq0
        have hB : |goldB p₂ r₂ g x y - goldB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) x y| ≤ q ^ (N + 1) * M := by
          rw [ge_goldB_diff, pow_succ, mul_comm (q ^ N) q, mul_assoc]
          exact mul_le_mul (le_max_right _ _) (ih _ _ hx hxX hy' hy'') (abs_nonneg _) hq0
        rw [hg x y hx hy]
        exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le hA hB)
    have h1 := claim
    apply le_antisymm
    · apply ge_geo_le hq0 hq1 (C := M + (x0 + y0) / (1 - q))
      intro N
      have := (abs_sub_le_iff.1 (claim N x0 y0 hx0 le_rfl hy0 le_rfl)).1
      have := (abs_sub_le_iff.1 (herr x0 y0 hx0 hy0 N)).1
      nlinarith
    · apply ge_geo_le hq0 hq1 (C := M + (x0 + y0) / (1 - q))
      intro N
      have := (abs_sub_le_iff.1 (claim N x0 y0 hx0 le_rfl hy0 le_rfl)).2
      have := (abs_sub_le_iff.1 (herr x0 y0 hx0 hy0 N)).2
      nlinarith

end BellmanDP.GoldMining

open BellmanDP.GoldMining


theorem solution (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁ : |p₁| < 1) (hp₂ : |p₂| < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ < 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ < 1) :
    ∃ f : ℝ → ℝ → ℝ, IsGoldMiningSolution p₁ p₂ r₁ r₂ f ∧ BoundedOnRectangles f ∧
      ContinuousOn (Function.uncurry f) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) ∧
      ∀ g : ℝ → ℝ → ℝ, IsGoldMiningSolution p₁ p₂ r₁ r₂ g → BoundedOnRectangles g →
        ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g x y = f x y := by
  exact exist_core p₁ p₂ r₁ r₂ hp₁ hp₂ hr₁0 hr₁1 hr₂0 hr₂1
