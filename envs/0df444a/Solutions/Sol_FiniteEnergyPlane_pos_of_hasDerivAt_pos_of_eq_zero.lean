-- Prove2me | solution 1 for FiniteEnergyPlane.pos_of_hasDerivAt_pos_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:49:32.37953+00:00
-- url     : https://prove2.me/submissions/e896d186-2a58-41af-9f98-535f2f541692

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope



namespace FiniteEnergyPlane

open Filter Topology

theorem pos_of_hasDerivAt_pos_of_eq_zero_aux {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t) (ha : f a = 0)
    (hz : ∀ t ∈ Set.Icc a b, f t = 0 → 0 < f' t) : 0 < f b := by
  have hcont : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hbar : Set.Icc a b ⊆ {t | 0 ≤ f t} := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · rw [Set.inter_comm]
      exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    · show 0 ≤ f a
      rw [ha]
    · rintro x ⟨hx, hxI⟩
      simp only [Set.mem_setOf_eq] at hx
      have hxI' : x ∈ Set.Icc a b := Set.Ico_subset_Icc_self hxI
      rcases hx.lt_or_eq with hlt | heq
      · filter_upwards [nhdsWithin_le_nhds
          ((hf x hxI').continuousAt.eventually (lt_mem_nhds hlt))] with t ht using le_of_lt ht
      · have hderpos := hz x hxI' heq.symm
        have hslope := hasDerivWithinAt_iff_tendsto_slope.1
          ((hf x hxI').hasDerivWithinAt (s := Set.Ioi x))
        rw [Set.diff_singleton_eq_self (s := Set.Ioi x) (lt_irrefl x)] at hslope
        have hev1 : ∀ᶠ t in 𝓝[>] x, 0 < slope f x t :=
          hslope.eventually (lt_mem_nhds hderpos)
        filter_upwards [hev1, self_mem_nhdsWithin] with t h1 h3
        rw [slope_def_field, ← heq, sub_zero] at h1
        have htx : 0 < t - x := sub_pos.2 h3
        show 0 ≤ f t
        by_contra hn
        push_neg at hn
        exact absurd h1 (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hn.le htx.le))
  have hb : 0 ≤ f b := hbar ⟨hab.le, le_refl b⟩
  rcases hb.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hbI : b ∈ Set.Icc a b := ⟨hab.le, le_refl b⟩
    have hderpos := hz b hbI heq.symm
    have hslope := hasDerivWithinAt_iff_tendsto_slope.1
      ((hf b hbI).hasDerivWithinAt (s := Set.Iio b))
    rw [Set.diff_singleton_eq_self (s := Set.Iio b) (lt_irrefl b)] at hslope
    have hev1 : ∀ᶠ t in 𝓝[<] b, 0 < slope f b t :=
      hslope.eventually (lt_mem_nhds hderpos)
    obtain ⟨t, h1, h2⟩ := (hev1.and (Ioo_mem_nhdsLT hab)).exists
    rw [slope_def_field, ← heq, sub_zero] at h1
    have htb : t - b < 0 := sub_neg.2 h2.2
    have hft : 0 ≤ f t := hbar ⟨h2.1.le, h2.2.le⟩
    have : f t / (t - b) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hft htb.le
    linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t) (ha : f a = 0)
    (hz : ∀ t ∈ Set.Icc a b, f t = 0 → 0 < f' t) : 0 < f b :=
  pos_of_hasDerivAt_pos_of_eq_zero_aux hab hf ha hz
