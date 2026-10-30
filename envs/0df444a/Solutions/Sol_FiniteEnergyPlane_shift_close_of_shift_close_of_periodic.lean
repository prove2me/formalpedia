-- Prove2me | solution 1 for FiniteEnergyPlane.shift_close_of_shift_close_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T21:13:12.605017+00:00
-- url     : https://prove2.me/submissions/c9339760-27c7-4601-9ea6-c1b3c7a3fab9

import Mathlib



namespace FiniteEnergyPlane

open Filter Topology Set

/-- Let `x : ℝ → E` and `y : ℝ → F` be continuous and `T`-periodic, and suppose every period of
`x` is a period of `y`. Then shifts of `y` are uniformly close whenever the same shifts of `x` are
uniformly close. -/
theorem shift_close_of_shift_close_of_periodic_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {x : ℝ → E} {y : ℝ → F} {T : ℝ} (hT : 0 < T)
    (hx : Continuous x) (hy : Continuous y) (hxT : Function.Periodic x T)
    (hyT : Function.Periodic y T)
    (hper : ∀ a : ℝ, (∀ τ, x (τ + a) = x τ) → ∀ τ, y (τ + a) = y τ) :
    ∀ ε > 0, ∃ δ > 0, ∀ a b : ℝ, (∀ τ, ‖x (τ + a) - x (τ + b)‖ ≤ δ) →
      ∀ τ, ‖y (τ + a) - y (τ + b)‖ ≤ ε := by
  intro ε hε
  -- reduction to `b = 0`, `a ∈ [0, T]`, `τ ∈ [0, T]`
  have red : ∀ δ : ℝ, (∀ a ∈ Icc 0 T, (∀ τ, ‖x (τ + a) - x τ‖ ≤ δ) →
      ∀ τ ∈ Icc 0 T, ‖y (τ + a) - y τ‖ < ε) →
      ∀ a b : ℝ, (∀ τ, ‖x (τ + a) - x (τ + b)‖ ≤ δ) → ∀ τ, ‖y (τ + a) - y (τ + b)‖ ≤ ε := by
    intro δ h a b hab τ
    set a' := toIcoMod hT 0 (a - b) with ha'
    have ha'm : a' ∈ Icc 0 T := by
      have := toIcoMod_mem_Ico hT 0 (a - b); simp only [zero_add] at this
      exact Ico_subset_Icc_self this
    have hsx : ∀ σ, x (σ + a') = x (σ + (a - b)) := by
      intro σ
      rw [ha', toIcoMod, ← add_sub_assoc, hxT.sub_zsmul_eq]
    have hsy : ∀ σ, y (σ + a') = y (σ + (a - b)) := by
      intro σ
      rw [ha', toIcoMod, ← add_sub_assoc, hyT.sub_zsmul_eq]
    have hxa : ∀ σ, ‖x (σ + a') - x σ‖ ≤ δ := by
      intro σ
      have := hab (σ - b)
      rw [hsx]
      convert this using 3 <;> ring_nf
    set τ' := toIcoMod hT 0 (τ + b) with hτ'
    have hτ'm : τ' ∈ Icc 0 T := by
      have := toIcoMod_mem_Ico hT 0 (τ + b); simp only [zero_add] at this
      exact Ico_subset_Icc_self this
    have e1 : y (τ' + a') = y (τ + a) := by
      rw [hsy, hτ', toIcoMod]
      generalize toIcoDiv hT 0 (τ + b) = k
      rw [show τ + b - k • T + (a - b) = τ + a - k • T by ring, hyT.sub_zsmul_eq]
    have e2 : y τ' = y (τ + b) := by
      rw [hτ', toIcoMod, hyT.sub_zsmul_eq]
    have := h a' ha'm hxa τ' hτ'm
    rw [e1, e2] at this
    exact this.le
  -- the compact set of bad shifts
  set K : Set ℝ := Prod.fst '' ((Icc 0 T ×ˢ Icc 0 T) ∩ {q : ℝ × ℝ | ε ≤ ‖y (q.2 + q.1) - y q.2‖})
    with hK
  have hKc : IsCompact K := by
    refine IsCompact.image ?_ continuous_fst
    refine (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_const ?_)
    fun_prop
  set g : ℝ → ENNReal := fun a => ⨆ τ, ENNReal.ofReal ‖x (τ + a) - x τ‖ with hg
  have hgl : LowerSemicontinuous g :=
    lowerSemicontinuous_iSup fun τ => (ENNReal.continuous_ofReal.comp (by fun_prop :
      Continuous fun a => ‖x (τ + a) - x τ‖)).lowerSemicontinuous
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, red 1 fun a ha _ τ hτ => ?_⟩
    by_contra hlt
    have : a ∈ K := ⟨(a, τ), ⟨⟨ha, hτ⟩, not_lt.1 hlt⟩, rfl⟩
    rw [hKe] at this; exact this
  · obtain ⟨a₀, ha₀K, hmin⟩ := (hgl.lowerSemicontinuousOn K).exists_isMinOn hKne hKc
    have hg0 : 0 < g a₀ := by
      rcases ha₀K with ⟨⟨a, τ₀⟩, ⟨_, hbad⟩, rfl⟩
      simp only [mem_setOf_eq] at hbad
      rw [pos_iff_ne_zero]
      intro h0
      have hall : ∀ τ, x (τ + a) = x τ := by
        intro τ
        have : ENNReal.ofReal ‖x (τ + a) - x τ‖ = 0 :=
          le_antisymm (h0 ▸ le_iSup (fun τ => ENNReal.ofReal ‖x (τ + a) - x τ‖) τ) bot_le
        rw [ENNReal.ofReal_eq_zero, norm_le_zero_iff, sub_eq_zero] at this
        exact this
      have := hper a hall τ₀
      simp only [this, sub_self, norm_zero] at hbad
      exact absurd hbad (not_le.2 hε)
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ < g a₀ := by
      obtain ⟨r, hr0, hrlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hg0
      refine ⟨r, ?_, hrlt.2⟩
      rcases hr0.lt_or_eq with h | h
      · exact h
      · rw [← h, ENNReal.ofReal_zero] at hrlt; exact absurd hrlt.1 (lt_irrefl _)
    refine ⟨δ, hδ0, red δ fun a ha hxa τ hτ => ?_⟩
    by_contra hlt
    have haK : a ∈ K := ⟨(a, τ), ⟨⟨ha, hτ⟩, not_lt.1 hlt⟩, rfl⟩
    have h1 : g a ≤ ENNReal.ofReal δ := iSup_le fun σ => ENNReal.ofReal_le_ofReal (hxa σ)
    exact absurd (lt_of_le_of_lt h1 hδ) (not_lt.2 (hmin haK))

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology Set

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {x : ℝ → E} {y : ℝ → F} {T : ℝ} (hT : 0 < T)
    (hx : Continuous x) (hy : Continuous y) (hxT : Function.Periodic x T)
    (hyT : Function.Periodic y T)
    (hper : ∀ a : ℝ, (∀ τ, x (τ + a) = x τ) → ∀ τ, y (τ + a) = y τ) :
    ∀ ε > 0, ∃ δ > 0, ∀ a b : ℝ, (∀ τ, ‖x (τ + a) - x (τ + b)‖ ≤ δ) →
      ∀ τ, ‖y (τ + a) - y (τ + b)‖ ≤ ε :=
  shift_close_of_shift_close_of_periodic_aux hT hx hy hxT hyT hper
