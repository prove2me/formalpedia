-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:30:22.515068+00:00
-- url     : https://prove2.me/submissions/a3f21d98-ee50-4ac8-94b6-128b18b80c87

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting


open BoundedEntropyGames.ConvRate

section L16
variable {𝒜 ℬ : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜] [Fintype ℬ] [Nonempty ℬ]

theorem BGE16_U_cont (u : 𝒜 → ℬ → ℝ) : Continuous (U u) := by
  unfold U
  refine continuous_iff_continuousAt.mpr fun p => ?_
  exact ContinuousAt.finset_inf'_apply (f := fun b (q : 𝒜 → ℝ) => ∑ a, q a * u a b)
    Finset.univ_nonempty (fun b _ =>
      (continuous_finset_sum _ fun a _ => (continuous_apply a).mul continuous_const).continuousAt)

theorem BGE16_shannon_eq (p : 𝒜 → ℝ) :
    shannon p = ∑ t, -(p t * Real.log (p t)) / Real.log 2 := by
  unfold shannon
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Real.logb]; ring

theorem BGE16_H_cont : Continuous (fun p : 𝒜 → ℝ => shannon p) := by
  have : (fun p : 𝒜 → ℝ => shannon p) =
      fun p => ∑ t, -(p t * Real.log (p t)) / Real.log 2 := funext BGE16_shannon_eq
  rw [this]
  refine continuous_finset_sum _ fun t _ => ?_
  exact ((Real.continuous_mul_log.comp (continuous_apply t)).neg).div_const _

theorem BGE16_le_one {p : 𝒜 → ℝ} (hp : p ∈ stdSimplex ℝ 𝒜) (a : 𝒜) : p a ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (f := p) (fun b _ => hp.1 b) (Finset.mem_univ a)

theorem BGE16_H_nonneg {p : 𝒜 → ℝ} (hp : p ∈ stdSimplex ℝ 𝒜) : 0 ≤ shannon p := by
  rw [BGE16_shannon_eq]
  refine Finset.sum_nonneg fun t _ => div_nonneg ?_ (Real.log_pos (by norm_num)).le
  have := Real.mul_log_nonpos (hp.1 t) (BGE16_le_one hp t)
  linarith

theorem BGE16_H_le {p : 𝒜 → ℝ} (hp : p ∈ stdSimplex ℝ 𝒜) :
    shannon p ≤ Fintype.card 𝒜 / Real.log 2 := by
  rw [BGE16_shannon_eq, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
  calc ∑ t, -(p t * Real.log (p t)) ≤ ∑ _t : 𝒜, (1 : ℝ) := by
        refine Finset.sum_le_sum fun t _ => ?_
        have := Real.negMulLog_le_one_sub_self (hp.1 t)
        simp only [Real.negMulLog] at this
        linarith [hp.1 t]
    _ = Fintype.card 𝒜 := by simp

theorem BGE16_single_mem (a : 𝒜) : (Pi.single a (1 : ℝ) : 𝒜 → ℝ) ∈ stdSimplex ℝ 𝒜 := by
  refine ⟨fun b => ?_, ?_⟩
  · by_cases h : b = a
    · subst h; simp
    · simp [Pi.single_apply, h]
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp

theorem BGE16_H_single (a : 𝒜) : shannon (Pi.single a (1 : ℝ) : 𝒜 → ℝ) = 0 := by
  unfold shannon
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h : b = a
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem BGE16_abs_le (u : 𝒜 → ℬ → ℝ) (a : 𝒜) (b : ℬ) : |u a b| ≤ maxAbsPayoff u :=
  Finset.le_sup' (fun ab : 𝒜 × ℬ => |u ab.1 ab.2|) (Finset.mem_univ (a, b))

theorem BGE16_U_le_M (u : 𝒜 → ℬ → ℝ) {p : 𝒜 → ℝ} (hp : p ∈ stdSimplex ℝ 𝒜) :
    U u p ≤ maxAbsPayoff u := by
  refine le_trans (Finset.inf'_le _ (Finset.mem_univ (Classical.arbitrary ℬ))) ?_
  calc ∑ a, p a * u a (Classical.arbitrary ℬ) ≤ ∑ a, p a * maxAbsPayoff u :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (le_trans (le_abs_self _) (BGE16_abs_le u _ _)) (hp.1 a)
    _ = maxAbsPayoff u := by rw [← Finset.sum_mul, hp.2, one_mul]

theorem BGE16_U_ge_M (u : 𝒜 → ℬ → ℝ) {p : 𝒜 → ℝ} (hp : p ∈ stdSimplex ℝ 𝒜) :
    -maxAbsPayoff u ≤ U u p := by
  unfold U
  refine Finset.le_inf' _ _ fun b _ => ?_
  calc -maxAbsPayoff u = ∑ a, p a * (-maxAbsPayoff u) := by
        rw [← Finset.sum_mul, hp.2, one_mul]
    _ ≤ ∑ a, p a * u a b := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (neg_le_of_abs_le (BGE16_abs_le u _ _)) (hp.1 a)

/-- Linear bound: `U(p) ≤ U(δ_a) + 2M H(p)` for an action `a` of maximal mass. -/
theorem BGE16_linear (u : 𝒜 → ℬ → ℝ) {p : 𝒜 → ℝ} (hp : p ∈ stdSimplex ℝ 𝒜) :
    ∃ a, U u p ≤ U u (Pi.single a (1 : ℝ)) + 2 * maxAbsPayoff u * shannon p := by
  set M := maxAbsPayoff u
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _)
    (BGE16_abs_le u (Classical.arbitrary 𝒜) (Classical.arbitrary ℬ))
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  refine ⟨a, ?_⟩
  -- the best reply `b` to `δ_a`
  obtain ⟨b, -, hb⟩ := Finset.exists_min_image Finset.univ (fun b => u a b) Finset.univ_nonempty
  have hUa : U u (Pi.single a (1 : ℝ)) = u a b := by
    unfold U
    apply le_antisymm
    · refine le_trans (Finset.inf'_le _ (Finset.mem_univ b)) (le_of_eq ?_)
      rw [Finset.sum_eq_single a]
      · simp
      · intro c _ hc; simp [Pi.single_apply, hc]
      · simp
    · refine Finset.le_inf' _ _ fun b' _ => ?_
      rw [Finset.sum_eq_single a]
      · simpa using hb b' (Finset.mem_univ _)
      · intro c _ hc; simp [Pi.single_apply, hc]
      · simp
  have hpa1 : p a ≤ 1 := BGE16_le_one hp a
  -- `U(p) ≤ U(δ_a) + 2M(1 - p_a)`
  have h1 : U u p ≤ u a b + 2 * M * (1 - p a) := by
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ b)) ?_
    have : ∑ c, p c * u c b = p a * u a b + ∑ c ∈ Finset.univ.erase a, p c * u c b := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    rw [this]
    have hrest : ∑ c ∈ Finset.univ.erase a, p c * u c b ≤
        ∑ c ∈ Finset.univ.erase a, p c * M :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self _) (BGE16_abs_le u _ _)) (hp.1 c)
    have hsum : ∑ c ∈ Finset.univ.erase a, p c = 1 - p a := by
      rw [← hp.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]; ring
    rw [← Finset.sum_mul, hsum] at hrest
    have : -M ≤ u a b := neg_le_of_abs_le (BGE16_abs_le u _ _)
    nlinarith
  -- `1 - p_a ≤ H(p)`
  have h2 : 1 - p a ≤ shannon p := by
    rcases (hp.1 a).eq_or_lt with h0 | hpos
    · -- then p = 0, impossible since the sum is 1
      exfalso
      have : ∑ c, p c ≤ 0 := Finset.sum_nonpos fun c _ => by
        have := ha c (Finset.mem_univ c); linarith
      linarith [hp.2]
    rw [BGE16_shannon_eq]
    have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have key : ∀ c, p c * (-Real.log (p a)) ≤ -(p c * Real.log (p c)) := by
      intro c
      rcases (hp.1 c).eq_or_lt with hc0 | hcpos
      · rw [← hc0]; simp
      · have : Real.log (p c) ≤ Real.log (p a) :=
          Real.log_le_log hcpos (ha c (Finset.mem_univ c))
        nlinarith
    have hsum : -Real.log (p a) ≤ ∑ c, -(p c * Real.log (p c)) := by
      calc -Real.log (p a) = ∑ c, p c * (-Real.log (p a)) := by
            rw [← Finset.sum_mul, hp.2, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun c _ => key c
    have hlog : 1 - p a ≤ -Real.log (p a) := by
      have := Real.log_le_sub_one_of_pos hpos; linarith
    have hL1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    rw [← Finset.sum_div, le_div_iff₀ hL]
    have : 0 ≤ 1 - p a := by linarith
    nlinarith
  rw [hUa]
  nlinarith

end L16

theorem BGE16_condEntropy_nonneg {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ)
    (hp : IsPMF pXY) : 0 ≤ condEntropy pXY := by
  unfold condEntropy
  refine Finset.sum_nonneg fun xy _ => ?_
  have h0 := hp.1 xy
  have hle : pXY xy ≤ marginalY pXY xy.2 := by
    unfold marginalY
    exact Finset.single_le_sum (f := fun x => pXY (x, xy.2)) (fun x _ => hp.1 _)
      (Finset.mem_univ xy.1)
  rcases h0.eq_or_lt with h | hpos
  · rw [← h]; simp
  · have hm : 0 < marginalY pXY xy.2 := lt_of_lt_of_le hpos hle
    have : Real.logb 2 (pXY xy / marginalY pXY xy.2) ≤ 0 :=
      Real.logb_nonpos (by norm_num) (div_nonneg h0 hm.le) ((div_le_one hm).mpr hle)
    nlinarith


open BoundedEntropyGames.ConvRate

section L16B
variable {𝒜 ℬ : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜] [Fintype ℬ] [Nonempty ℬ]

theorem BGE16_J_ge (u : 𝒜 → ℬ → ℝ) {p : 𝒜 → ℝ} (hp : p ∈ stdSimplex ℝ 𝒜) {h : ℝ}
    (hh : shannon p ≤ h) : U u p ≤ J u h := by
  unfold J
  refine le_csSup ⟨maxAbsPayoff u, ?_⟩ ⟨p, ⟨hp, hh⟩, rfl⟩
  rintro _ ⟨q, hq, rfl⟩
  exact BGE16_U_le_M u hq.1

theorem BGE16_J_le_M (u : 𝒜 → ℬ → ℝ) (h : ℝ) : J u h ≤ maxAbsPayoff u := by
  unfold J
  have hM0 : 0 ≤ maxAbsPayoff u := le_trans (abs_nonneg _)
    (BGE16_abs_le u (Classical.arbitrary 𝒜) (Classical.arbitrary ℬ))
  apply Real.sSup_le _ hM0
  rintro _ ⟨q, hq, rfl⟩
  exact BGE16_U_le_M u hq.1

theorem BGE16_J_ge_M (u : 𝒜 → ℬ → ℝ) {h : ℝ} (hh : 0 ≤ h) : -maxAbsPayoff u ≤ J u h := by
  set a := Classical.arbitrary 𝒜
  refine le_trans (BGE16_U_ge_M u (BGE16_single_mem a)) (BGE16_J_ge u (BGE16_single_mem a) ?_)
  rw [BGE16_H_single]; exact hh

/-- concave majorants of `J` on `[0, ∞)` are nondecreasing -/
theorem BGE16_mono (u : 𝒜 → ℬ → ℝ) (g : ℝ → ℝ) (hg : ConcaveOn ℝ (Set.Ici 0) g)
    (hJ : ∀ h' ≥ 0, J u h' ≤ g h') {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : g x ≤ g y := by
  by_contra hlt
  push Not at hlt
  set M := maxAbsPayoff u
  set d := g x - g y with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hxy' : x < y := by
    rcases hxy.eq_or_lt with h | h
    · rw [h] at hlt; linarith
    · exact h
  set T := (|g y| + M + 1) / d with hT
  have hT0 : 0 < T := by
    have : 0 ≤ M := le_trans (abs_nonneg _)
      (BGE16_abs_le u (Classical.arbitrary 𝒜) (Classical.arbitrary ℬ))
    positivity
  set z := y + T * (y - x) with hz
  have hz0 : 0 ≤ z := by rw [hz]; nlinarith
  have hconc := hg.2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hz0)
    (show (0 : ℝ) ≤ T / (1 + T) by positivity) (show (0 : ℝ) ≤ 1 / (1 + T) by positivity)
    (by field_simp; try ring)
  simp only [smul_eq_mul] at hconc
  have hmid : T / (1 + T) * x + 1 / (1 + T) * z = y := by
    rw [hz]; field_simp; ring
  rw [hmid] at hconc
  have hgz : g z ≤ g y - T * d := by
    have h1 : 0 < 1 + T := by linarith
    have : T * g x + g z ≤ (1 + T) * g y := by
      have := mul_le_mul_of_nonneg_left hconc h1.le
      rw [mul_add, ← mul_assoc, ← mul_assoc, mul_div_cancel₀ _ h1.ne',
        mul_one_div_cancel h1.ne', one_mul] at this
      linarith
    rw [hd]; linarith
  have hTd : T * d = |g y| + M + 1 := by rw [hT]; field_simp
  have := hJ z hz0
  have := BGE16_J_ge_M u hz0
  have := le_abs_self (g y)
  linarith

theorem BGE16_Jcav_ge (u : 𝒜 → ℬ → ℝ) {h0 r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {p₁ p₂ : 𝒜 → ℝ} (hp₁ : p₁ ∈ stdSimplex ℝ 𝒜) (hp₂ : p₂ ∈ stdSimplex ℝ 𝒜)
    (hH : r * shannon p₁ + (1 - r) * shannon p₂ ≤ h0) :
    r * U u p₁ + (1 - r) * U u p₂ ≤ Jcav u h0 := by
  unfold Jcav
  refine le_csInf ⟨maxAbsPayoff u, ⟨fun _ => maxAbsPayoff u,
    concaveOn_const _ (convex_Ici 0), fun h' _ => BGE16_J_le_M u h', rfl⟩⟩ ?_
  rintro _ ⟨g, hg, hJ, rfl⟩
  have hH1 := BGE16_H_nonneg hp₁
  have hH2 := BGE16_H_nonneg hp₂
  have hm0 : 0 ≤ r * shannon p₁ + (1 - r) * shannon p₂ := by
    have : 0 ≤ 1 - r := by linarith
    positivity
  have h1 := BGE16_mono u g hg hJ hm0 hH
  have h2 := hg.2 (Set.mem_Ici.mpr hH1) (Set.mem_Ici.mpr hH2) hr0 (by linarith : 0 ≤ 1 - r)
    (by ring)
  simp only [smul_eq_mul] at h2
  have h3 := hJ _ hH1
  have h4 := hJ _ hH2
  have h5 := BGE16_J_ge u hp₁ (le_refl (shannon p₁))
  have h6 := BGE16_J_ge u hp₂ (le_refl (shannon p₂))
  have : r * U u p₁ + (1 - r) * U u p₂ ≤ r * g (shannon p₁) + (1 - r) * g (shannon p₂) := by
    have a1 := mul_le_mul_of_nonneg_left (le_trans h5 h3) hr0
    have a2 := mul_le_mul_of_nonneg_left (le_trans h6 h4) (by linarith : 0 ≤ 1 - r)
    linarith
  linarith

theorem BGE16_Jcav_le (u : 𝒜 → ℬ → ℝ) {h0 : ℝ} (hh0 : 0 ≤ h0) (c0 lam : ℝ) (hlam : 0 ≤ lam)
    (hmaj : ∀ p ∈ stdSimplex ℝ 𝒜, U u p ≤ c0 + lam * shannon p) :
    Jcav u h0 ≤ c0 + lam * h0 := by
  unfold Jcav
  apply csInf_le
  · refine ⟨-maxAbsPayoff u, ?_⟩
    rintro _ ⟨g, hg, hJ, rfl⟩
    exact le_trans (BGE16_J_ge_M u hh0) (hJ h0 hh0)
  · refine ⟨fun h => c0 + lam * h, ⟨convex_Ici 0, ?_⟩, ?_, rfl⟩
    · intro x _ y _ a b _ _ hab
      simp only [smul_eq_mul]
      have : a * (c0 + lam * x) + b * (c0 + lam * y) = (a + b) * c0 + lam * (a * x + b * y) := by
        ring
      rw [this, hab, one_mul]
    · intro h' hh'
      unfold J
      apply csSup_le
      · exact ⟨_, ⟨Pi.single (Classical.arbitrary 𝒜) 1,
          ⟨BGE16_single_mem _, by rw [BGE16_H_single]; exact hh'⟩, rfl⟩⟩
      · rintro _ ⟨q, hq, rfl⟩
        have := hmaj q hq.1
        have := mul_le_mul_of_nonneg_left hq.2 hlam
        linarith

end L16B


open BoundedEntropyGames.ConvRate Filter Topology

theorem BGE16_single {𝒜 ℬ : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜] [Fintype ℬ]
    [Nonempty ℬ] (u : 𝒜 → ℬ → ℝ) (h0 : ℝ) {p : 𝒜 → ℝ} (hp : p ∈ stdSimplex ℝ 𝒜)
    (hH : shannon p ≤ h0) (hJ : Jcav u h0 = U u p) :
    (∃ a : 𝒜, Jcav u h0 ≤ U u (Pi.single a (1 : ℝ))) ∨
    ∃ r ∈ Set.Ioc (0 : ℝ) 1, ∃ p₁ ∈ stdSimplex ℝ 𝒜, ∃ p₂ ∈ stdSimplex ℝ 𝒜,
      r * U u p₁ + (1 - r) * U u p₂ = Jcav u h0 ∧
      r * shannon p₁ + (1 - r) * shannon p₂ ≤ h0 ∧
      shannon p₂ < shannon p₁ := by
  rcases (BGE16_H_nonneg hp).eq_or_lt with h0' | hpos
  · left
    obtain ⟨a, ha⟩ := BGE16_linear u hp
    refine ⟨a, ?_⟩
    rw [hJ, ← h0'] at *
    simpa using ha
  · right
    set a0 := Classical.arbitrary 𝒜
    refine ⟨1, ⟨one_pos, le_rfl⟩, p, hp, Pi.single a0 1, BGE16_single_mem a0, ?_, ?_, ?_⟩
    · rw [hJ]; ring
    · simpa using hH
    · rw [BGE16_H_single]; exact hpos

theorem solution {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜]
    [Fintype ℬ] [Nonempty ℬ] [Fintype 𝒳] [Fintype 𝒴]
    (u : 𝒜 → ℬ → ℝ) (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) :
    (∃ a : 𝒜, Jcav u (condEntropy pXY) ≤ U u (Pi.single a (1 : ℝ))) ∨
    ∃ r ∈ Set.Ioc (0 : ℝ) 1, ∃ p₁ ∈ stdSimplex ℝ 𝒜, ∃ p₂ ∈ stdSimplex ℝ 𝒜,
      r * U u p₁ + (1 - r) * U u p₂ = Jcav u (condEntropy pXY) ∧
      r * shannon p₁ + (1 - r) * shannon p₂ ≤ condEntropy pXY ∧
      shannon p₂ < shannon p₁ := by
  set h0 := condEntropy pXY with hh0
  have hh00 : 0 ≤ h0 := BGE16_condEntropy_nonneg pXY hp
  set M := maxAbsPayoff u with hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _)
    (BGE16_abs_le u (Classical.arbitrary 𝒜) (Classical.arbitrary ℬ))
  set Δ := stdSimplex ℝ 𝒜 with hΔ
  -- the best pure action
  obtain ⟨astar, -, hastar⟩ := Finset.exists_max_image Finset.univ
    (fun a => U u (Pi.single a (1 : ℝ))) Finset.univ_nonempty
  rcases hh00.eq_or_lt with hzero | hpos
  · -- `H(X|Y) = 0`
    left
    refine ⟨astar, ?_⟩
    have := BGE16_Jcav_le u hh00 (U u (Pi.single astar (1 : ℝ))) (2 * M) (by positivity)
      (fun p hp => by
        obtain ⟨a, ha⟩ := BGE16_linear u hp
        have := hastar a (Finset.mem_univ a)
        linarith)
    have h2 : 2 * M * h0 = 0 := by rw [← hzero]; ring
    linarith
  -- `H(X|Y) > 0`: Lagrangian duality
  have hcont : ∀ lam : ℝ, Continuous (fun p : 𝒜 → ℝ => U u p - lam * shannon p) :=
    fun lam => (BGE16_U_cont u).sub (continuous_const.mul BGE16_H_cont)
  have hne : Δ.Nonempty := ⟨_, BGE16_single_mem astar⟩
  have hmax : ∀ lam : ℝ, ∃ p ∈ Δ, ∀ q ∈ Δ, U u q - lam * shannon q ≤ U u p - lam * shannon p := by
    intro lam
    obtain ⟨p, hp, hpm⟩ := (isCompact_stdSimplex ℝ 𝒜).exists_isMaxOn hne (hcont lam).continuousOn
    exact ⟨p, hp, fun q hq => hpm hq⟩
  choose pm hpmΔ hpmmax using hmax
  set Φ : ℝ → ℝ := fun lam => U u (pm lam) - lam * shannon (pm lam) with hΦ
  set B : ℝ := Fintype.card 𝒜 / Real.log 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hHB : ∀ p ∈ Δ, shannon p ≤ B := fun p hp => BGE16_H_le hp
  have hΦge : ∀ lam, ∀ q ∈ Δ, U u q - lam * shannon q ≤ Φ lam := fun lam q hq => hpmmax lam q hq
  have hLip : ∀ l l' : ℝ, Φ l' - Φ l ≤ B * |l - l'| := by
    intro l l'
    have h1 := hΦge l (pm l') (hpmΔ l')
    have h2 := BGE16_H_nonneg (hpmΔ l')
    have h3 := hHB _ (hpmΔ l')
    have : (l - l') * shannon (pm l') ≤ |l - l'| * B := by
      calc (l - l') * shannon (pm l') ≤ |l - l'| * shannon (pm l') :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h2
        _ ≤ |l - l'| * B := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    simp only [hΦ] at h1 ⊢
    nlinarith
  set D : ℝ → ℝ := fun lam => Φ lam + lam * h0 with hD
  have hDkey : ∀ l l' : ℝ, |D l - D l'| ≤ (B + h0) * |l - l'| := by
    intro l l'
    have a1 := hLip l l'
    have a2 := hLip l' l
    rw [abs_sub_comm] at a2
    have a3 : (l - l') * h0 ≤ |l - l'| * h0 := mul_le_mul_of_nonneg_right (le_abs_self _) hh00
    have a4 : -(|l - l'| * h0) ≤ (l - l') * h0 := by
      have := mul_le_mul_of_nonneg_right (neg_abs_le (l - l')) hh00
      linarith
    show |Φ l + l * h0 - (Φ l' + l' * h0)| ≤ (B + h0) * |l - l'|
    rw [abs_le]
    constructor <;> linarith
  have hDcont : Continuous D := by
    have : LipschitzWith ⟨B + h0, by positivity⟩ D := by
      apply LipschitzWith.of_dist_le_mul
      intro l l'
      rw [Real.dist_eq, Real.dist_eq]
      exact hDkey l l'
    exact this.continuous
  set c := (2 * M + 1) / h0 with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨ls, hlsI, hlsmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := c)).exists_isMinOn
    ⟨0, ⟨le_rfl, hc0.le⟩⟩ hDcont.continuousOn
  have hlsmin' : ∀ l ∈ Set.Icc (0 : ℝ) c, D ls ≤ D l := fun l hl => hlsmin hl
  obtain ⟨hls0, hlsc⟩ := hlsI
  -- `ls < c`
  have hDc : M + 1 ≤ D c := by
    have h1 := hΦge c _ (BGE16_single_mem astar)
    rw [BGE16_H_single] at h1
    have h2 := BGE16_U_ge_M u (BGE16_single_mem astar)
    simp only [hD]
    have : c * h0 = 2 * M + 1 := by rw [hc]; field_simp
    linarith
  have hD0 : D 0 ≤ M := by
    simp only [hD, hΦ]
    have := BGE16_U_le_M u (hpmΔ 0)
    linarith
  have hlsc' : ls < c := by
    rcases hlsc.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hlsmin' 0 ⟨le_rfl, hc0.le⟩
      rw [h] at this
      linarith
  -- right sequence
  set lk : ℕ → ℝ := fun k => ls + (c - ls) / ((k : ℝ) + 2) with hlk
  have hlk_gt : ∀ k, ls < lk k := fun k => by
    simp only [hlk]
    have : 0 < (c - ls) / ((k : ℝ) + 2) := div_pos (by linarith) (by positivity)
    linarith
  have hlk_le : ∀ k, lk k ≤ c := fun k => by
    simp only [hlk]
    have : (c - ls) / ((k : ℝ) + 2) ≤ c - ls := by
      apply div_le_self (by linarith)
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    linarith
  have hlk_lim : Tendsto lk atTop (𝓝 ls) := by
    have : Tendsto (fun k : ℕ => (c - ls) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := ls)).add this
  have hHk : ∀ k, shannon (pm (lk k)) ≤ h0 := by
    intro k
    have h1 := hlsmin' (lk k) ⟨le_trans hls0 (hlk_gt k).le, hlk_le k⟩
    have h2 := hΦge ls (pm (lk k)) (hpmΔ _)
    simp only [hD, hΦ] at h1 h2
    have hpos' : 0 < lk k - ls := by linarith [hlk_gt k]
    by_contra hcon
    push Not at hcon
    have : (lk k - ls) * h0 < (lk k - ls) * shannon (pm (lk k)) :=
      mul_lt_mul_of_pos_left hcon hpos'
    nlinarith
  obtain ⟨p2, hp2Δ, φ, hφ, hlim⟩ := (isCompact_stdSimplex ℝ 𝒜).tendsto_subseq
    (fun k => hpmΔ (lk k))
  have hlkφ : Tendsto (lk ∘ φ) atTop (𝓝 ls) := hlk_lim.comp hφ.tendsto_atTop
  have hp2H : shannon p2 ≤ h0 :=
    le_of_tendsto' ((BGE16_H_cont.tendsto p2).comp hlim) (fun k => hHk (φ k))
  have hp2max : ∀ q ∈ Δ, U u q - ls * shannon q ≤ U u p2 - ls * shannon p2 := by
    intro q hq
    have hL : Tendsto (fun k => U u q - (lk ∘ φ) k * shannon q) atTop
        (𝓝 (U u q - ls * shannon q)) :=
      tendsto_const_nhds.sub (hlkφ.mul tendsto_const_nhds)
    have hR : Tendsto (fun k => U u (((fun k => pm (lk k)) ∘ φ) k) - (lk ∘ φ) k *
        shannon (((fun k => pm (lk k)) ∘ φ) k)) atTop (𝓝 (U u p2 - ls * shannon p2)) :=
      (((BGE16_U_cont u).tendsto p2).comp hlim).sub
        (hlkφ.mul ((BGE16_H_cont.tendsto p2).comp hlim))
    exact le_of_tendsto_of_tendsto' hL hR (fun k => hpmmax _ q hq)
  set Φs := U u p2 - ls * shannon p2 with hΦs
  have hmaj : ∀ q ∈ Δ, U u q ≤ Φs + ls * shannon q := fun q hq => by
    have := hp2max q hq; linarith
  have hJle : Jcav u h0 ≤ Φs + ls * h0 := BGE16_Jcav_le u hh00 Φs ls hls0 hmaj
  by_cases hcase : ls = 0 ∨ shannon p2 = h0
  · -- a single maximizer achieves the value
    have hval : Φs + ls * h0 = U u p2 := by
      rcases hcase with h | h
      · rw [hΦs, h]; ring
      · rw [hΦs, h]; ring
    have hJge : U u p2 ≤ Jcav u h0 := by
      have := BGE16_Jcav_ge u (r := 1) zero_le_one le_rfl hp2Δ hp2Δ (h0 := h0) (by simpa using hp2H)
      simpa using this
    exact BGE16_single u h0 hp2Δ hp2H (le_antisymm (hval ▸ hJle) hJge)
  push Not at hcase
  obtain ⟨hls_ne, hH2ne⟩ := hcase
  have hlspos : 0 < ls := lt_of_le_of_ne hls0 (Ne.symm hls_ne)
  have hH2lt : shannon p2 < h0 := lt_of_le_of_ne hp2H hH2ne
  -- left sequence
  set mk : ℕ → ℝ := fun k => ls * (1 - 1 / ((k : ℝ) + 2)) with hmk
  have hmk_lt : ∀ k, mk k < ls := fun k => by
    simp only [hmk]
    have : 0 < 1 / ((k : ℝ) + 2) := by positivity
    nlinarith
  have hmk_ge : ∀ k, 0 ≤ mk k := fun k => by
    simp only [hmk]
    have : 1 / ((k : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    nlinarith
  have hmk_lim : Tendsto mk atTop (𝓝 ls) := by
    have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h := (tendsto_const_nhds (x := ls)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub this)
    rw [sub_zero, mul_one] at h
    exact h
  have hHk' : ∀ k, h0 ≤ shannon (pm (mk k)) := by
    intro k
    have h1 := hlsmin' (mk k) ⟨hmk_ge k, le_trans (hmk_lt k).le hlsc⟩
    have h2 := hΦge ls (pm (mk k)) (hpmΔ _)
    simp only [hD, hΦ] at h1 h2
    have hpos' : 0 < ls - mk k := by linarith [hmk_lt k]
    by_contra hcon
    push Not at hcon
    have : (ls - mk k) * shannon (pm (mk k)) < (ls - mk k) * h0 :=
      mul_lt_mul_of_pos_left hcon hpos'
    nlinarith
  obtain ⟨p1, hp1Δ, ψ, hψ, hlim1⟩ := (isCompact_stdSimplex ℝ 𝒜).tendsto_subseq
    (fun k => hpmΔ (mk k))
  have hmkψ : Tendsto (mk ∘ ψ) atTop (𝓝 ls) := hmk_lim.comp hψ.tendsto_atTop
  have hp1H : h0 ≤ shannon p1 :=
    ge_of_tendsto' ((BGE16_H_cont.tendsto p1).comp hlim1) (fun k => hHk' (ψ k))
  have hp1max : ∀ q ∈ Δ, U u q - ls * shannon q ≤ U u p1 - ls * shannon p1 := by
    intro q hq
    have hL : Tendsto (fun k => U u q - (mk ∘ ψ) k * shannon q) atTop
        (𝓝 (U u q - ls * shannon q)) :=
      tendsto_const_nhds.sub (hmkψ.mul tendsto_const_nhds)
    have hR : Tendsto (fun k => U u (((fun k => pm (mk k)) ∘ ψ) k) - (mk ∘ ψ) k *
        shannon (((fun k => pm (mk k)) ∘ ψ) k)) atTop (𝓝 (U u p1 - ls * shannon p1)) :=
      (((BGE16_U_cont u).tendsto p1).comp hlim1).sub
        (hmkψ.mul ((BGE16_H_cont.tendsto p1).comp hlim1))
    exact le_of_tendsto_of_tendsto' hL hR (fun k => hpmmax _ q hq)
  have hΦ1 : U u p1 - ls * shannon p1 = Φs := by
    apply le_antisymm (hp2max p1 hp1Δ) (hp1max p2 hp2Δ)
  -- the two-point mixture
  have hgap : 0 < shannon p1 - shannon p2 := by linarith
  set r := (h0 - shannon p2) / (shannon p1 - shannon p2) with hr
  have hr0 : 0 < r := div_pos (by linarith) hgap
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hgap]; linarith
  have hrH : r * shannon p1 + (1 - r) * shannon p2 = h0 := by
    rw [hr]; field_simp; ring
  have hval : r * U u p1 + (1 - r) * U u p2 = Φs + ls * h0 := by
    have e1 : U u p1 = Φs + ls * shannon p1 := by linarith
    have e2 : U u p2 = Φs + ls * shannon p2 := by rw [hΦs]; ring
    rw [e1, e2, ← hrH]; ring
  have hJge := BGE16_Jcav_ge u hr0.le hr1 hp1Δ hp2Δ (h0 := h0) hrH.le
  right
  refine ⟨r, ⟨hr0, hr1⟩, p1, hp1Δ, p2, hp2Δ, ?_, hrH.le, by linarith⟩
  rw [hval] at hJge ⊢
  exact le_antisymm hJge hJle
