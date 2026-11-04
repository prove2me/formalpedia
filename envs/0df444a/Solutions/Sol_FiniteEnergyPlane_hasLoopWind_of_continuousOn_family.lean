-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_of_continuousOn_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T11:08:53.769224+00:00
-- url     : https://prove2.me/submissions/99f8f15d-e279-4108-bd68-375bbc091087

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_re_conj_mul_pos



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

/-- `‖f - g‖ < ‖g‖` forces `Re(conj g · f) > 0`. -/
lemma wph_re_conj_mul_pos {f g : ℂ} (h : ‖f - g‖ < ‖g‖) : 0 < (starRingEnd ℂ g * f).re := by
  have hg : 0 < ‖g‖ := lt_of_le_of_lt (norm_nonneg _) h
  have e : (starRingEnd ℂ g * f).re = ‖g‖ ^ 2 + (starRingEnd ℂ g * (f - g)).re := by
    rw [mul_sub, Complex.sub_re, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  have h1 : |(starRingEnd ℂ g * (f - g)).re| ≤ ‖g‖ * ‖f - g‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : ‖g‖ * ‖f - g‖ < ‖g‖ ^ 2 := by
    rw [sq]; exact mul_lt_mul_of_pos_left h hg
  have := (abs_le.1 h1).1
  linarith

theorem hasLoopWind_of_continuousOn_family_aux {a b : ℝ} (F : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hper : ∀ l ∈ Set.Icc a b, Function.Periodic (F l) 1)
    (h0 : ∀ l ∈ Set.Icc a b, ∀ t, F l t ≠ 0) {k : ℤ} (hk : HasLoopWind (F a) k) :
    ∀ l ∈ Set.Icc a b, HasLoopWind (F l) k := by
  rcases lt_or_ge b a with hba | hab
  · intro l hl; exact absurd (hl.1.trans hl.2) (not_le.2 hba)
  set G : ℝ × ℝ → ℂ := fun p => F p.1 p.2 with hG
  set K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKs : K ⊆ Set.Icc a b ×ˢ Set.univ := Set.prod_mono le_rfl (Set.subset_univ _)
  have hGK : ContinuousOn G K := hF.mono hKs
  have hKne : K.Nonempty := ⟨(a, 0), ⟨Set.left_mem_Icc.2 hab, Set.left_mem_Icc.2 zero_le_one⟩⟩
  -- a positive lower bound for `‖F‖` on `K`
  obtain ⟨p₀, hp₀K, hp₀⟩ := hKc.exists_isMinOn hKne (continuous_norm.comp_continuousOn hGK)
  set m := ‖G p₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (h0 _ hp₀K.1 _)
  have hmin : ∀ p ∈ K, m ≤ ‖G p‖ := fun p hp => hp₀ hp
  -- uniform continuity on `K`
  obtain ⟨δ, hδ, hδK⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hGK) m hm0
  -- each loop is continuous
  have hcont : ∀ l ∈ Set.Icc a b, Continuous (F l) := fun l hl =>
    hF.comp_continuous (continuous_const.prodMk continuous_id) fun t => ⟨hl, Set.mem_univ _⟩
  -- the step: loops at nearby parameters have the same winding
  have hstep : ∀ l ∈ Set.Icc a b, ∀ l' ∈ Set.Icc a b, |l - l'| < δ →
      HasLoopWind (F l) k → HasLoopWind (F l') k := by
    intro l hl l' hl' hll' hw
    refine hasLoopWind_of_re_conj_mul_pos hw (hcont l' hl') (hper l' hl') fun t => ?_
    set s := Int.fract t
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    have e1 : F l t = F l s := by
      rw [show s = t - ((⌊t⌋ : ℤ) : ℝ) * 1 by rw [mul_one, Int.self_sub_floor]]
      exact ((hper l hl).sub_int_mul_eq _).symm
    have e2 : F l' t = F l' s := by
      rw [show s = t - ((⌊t⌋ : ℤ) : ℝ) * 1 by rw [mul_one, Int.self_sub_floor]]
      exact ((hper l' hl').sub_int_mul_eq _).symm
    rw [e1, e2]
    apply wph_re_conj_mul_pos
    have hd : dist ((l, s) : ℝ × ℝ) (l', s) < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      exact lt_of_le_of_lt (max_le le_rfl (abs_nonneg _)) hll'
    have h1 := hδK (l, s) ⟨hl, hs⟩ (l', s) ⟨hl', hs⟩ hd
    rw [dist_eq_norm, ← norm_neg, neg_sub] at h1
    exact lt_of_lt_of_le h1 (hmin (l, s) ⟨hl, hs⟩ : m ≤ ‖F l s‖)
  -- induction along `[a, b]` in steps of `δ / 2`
  have hind : ∀ n : ℕ, ∀ l ∈ Set.Icc a b, l ≤ a + n * (δ / 2) → HasLoopWind (F l) k := by
    intro n
    induction n with
    | zero =>
      intro l hl hle
      simp only [Nat.cast_zero, zero_mul, add_zero] at hle
      rwa [le_antisymm hle hl.1]
    | succ n ih =>
      intro l hl hle
      by_cases h : l ≤ a + n * (δ / 2)
      · exact ih l hl h
      · push_neg at h
        set l₀ := a + n * (δ / 2) with hl₀def
        have hl₀ : l₀ ∈ Set.Icc a b :=
          ⟨le_add_of_nonneg_right (by positivity), h.le.trans hl.2⟩
        refine hstep l₀ hl₀ l hl ?_ (ih l₀ hl₀ le_rfl)
        rw [abs_sub_comm, abs_of_pos (sub_pos.2 h)]
        push_cast at hle
        rw [hl₀def]
        linarith
  intro l hl
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / (δ / 2))
  refine hind n l hl ?_
  have := (div_lt_iff₀ (half_pos hδ)).1 hn
  have := hl.2
  nlinarith

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {a b : ℝ} (F : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hper : ∀ l ∈ Set.Icc a b, Function.Periodic (F l) 1)
    (h0 : ∀ l ∈ Set.Icc a b, ∀ t, F l t ≠ 0) {k : ℤ} (hk : HasLoopWind (F a) k) :
    ∀ l ∈ Set.Icc a b, HasLoopWind (F l) k :=
  hasLoopWind_of_continuousOn_family_aux F hF hper h0 hk
