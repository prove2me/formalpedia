-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_bounded_off_finite_of_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T17:56:06.299115+00:00
-- url     : https://prove2.me/submissions/9b90a5e9-3788-4849-8f67-7d81ee79ff31

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ENNReal

/-- The points of `Γ` are blow-up limits of `g ∘ ψ` and carry mass `> γ` of `f ∘ ψ` on small balls. -/
def BUGood (g : ℕ → ℂ → ℝ) (f : ℕ → ℂ → ℝ≥0∞) (γ : ℝ) (ψ : ℕ → ℕ) (Γ : Finset ℂ) : Prop :=
  StrictMono ψ ∧ ∀ z ∈ Γ,
    (∃ ζ : ℕ → ℂ, Tendsto ζ atTop (𝓝 z) ∧ Tendsto (fun k => g (ψ k) (ζ k)) atTop atTop) ∧
    ∀ δ > 0, ∀ᶠ j in atTop, ENNReal.ofReal γ < ∫⁻ w in ball z δ, f (ψ j) w

theorem BUGood.comp {g : ℕ → ℂ → ℝ} {f : ℕ → ℂ → ℝ≥0∞} {γ : ℝ} {ψ : ℕ → ℕ} {Γ : Finset ℂ}
    (h : BUGood g f γ ψ Γ) {θ : ℕ → ℕ} (hθ : StrictMono θ) : BUGood g f γ (ψ ∘ θ) Γ := by
  refine ⟨h.1.comp hθ, fun z hz => ?_⟩
  obtain ⟨⟨ζ, hζ, hb⟩, hs⟩ := h.2 z hz
  have ht := hθ.tendsto_atTop
  exact ⟨⟨ζ ∘ θ, hζ.comp ht, hb.comp ht⟩, fun δ hδ => ht.eventually (hs δ hδ)⟩

/-- The mass count for a good family. -/
theorem BUGood.card_le {g : ℕ → ℂ → ℝ} {f : ℕ → ℂ → ℝ≥0∞} {γ T : ℝ} {ψ : ℕ → ℕ} {Γ : Finset ℂ}
    (h : BUGood g f γ ψ Γ) (hγ : 0 < γ) (hT0 : 0 ≤ T)
    (hT : ∀ k, ∫⁻ z, f k z ≤ ENNReal.ofReal T) : (Γ.card : ℝ) * γ ≤ T := by
  classical
  -- a radius making the balls pairwise disjoint
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ p ∈ Γ.offDiag, δ + δ ≤ dist p.1 p.2 := by
    rw [Filter.eventually_all_finset]
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.1 hp).2.2
    have hd : 0 < dist p.1 p.2 := dist_pos.2 hne
    have : Tendsto (fun δ : ℝ => δ + δ) (𝓝[>] 0) (𝓝 (0 + 0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).add
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    rw [add_zero] at this
    exact (this.eventually (gt_mem_nhds hd)).mono fun δ hδ => hδ.le
  obtain ⟨δ, hδd, hδ⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0 : 0 < δ := hδ
  have hall : ∀ᶠ j in atTop, ∀ z ∈ Γ, ENNReal.ofReal γ < ∫⁻ w in ball z δ, f (ψ j) w := by
    rw [Filter.eventually_all_finset]
    exact fun z hz => (h.2 z hz).2 δ hδ0
  obtain ⟨j, hj⟩ := hall.exists
  have hdisj : Set.PairwiseDisjoint (↑Γ) (fun z : ℂ => ball z δ) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (hδd (x, y) (Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩))
  have hsum : ∑ z ∈ Γ, ∫⁻ w in ball z δ, f (ψ j) w ≤ ENNReal.ofReal T := by
    rw [← lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
    exact (lintegral_mono_set (Set.subset_univ _)).trans (by simpa using hT (ψ j))
  have hlow : (Γ.card : ℝ≥0∞) * ENNReal.ofReal γ ≤ ∑ z ∈ Γ, ∫⁻ w in ball z δ, f (ψ j) w := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun z hz => (hj z hz).le
  have h2 := hlow.trans hsum
  rw [show (Γ.card : ℝ≥0∞) = ENNReal.ofReal (Γ.card : ℝ) from by simp,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_le_ofReal_iff hT0] at h2
  exact h2

/-- A sequence of functions unbounded on a compact set, each continuous, blows up along a
subsequence at a point of that set. -/
theorem bu_exists_blowup (g : ℕ → ℂ → ℝ) (hg : ∀ k, Continuous (g k)) (Kc : Set ℂ)
    (hKc : IsCompact Kc) (hun : ∀ M : ℝ, ∃ k, ∃ z ∈ Kc, M < g k z) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ ζ : ℕ → ℂ, ∃ z ∈ Kc, Tendsto ζ atTop (𝓝 z) ∧
      Tendsto (fun k => g (θ k) (ζ k)) atTop atTop := by
  classical
  have hB : ∀ k, ∃ B : ℝ, ∀ z ∈ Kc, g k z ≤ B := fun k => by
    obtain ⟨B, hB⟩ := hKc.bddAbove_image (hg k).continuousOn
    exact ⟨B, fun z hz => hB ⟨z, hz, rfl⟩⟩
  choose B hB using hB
  have hfr : ∀ m : ℕ, ∃ᶠ k in atTop, ∃ z ∈ Kc, (m : ℝ) < g k z := by
    intro m
    rw [frequently_atTop]
    intro a
    by_contra hcon
    push_neg at hcon
    obtain ⟨M, hM⟩ := ((Finset.range a).image B).exists_le
    obtain ⟨k, z, hz, hk⟩ := hun (max M m)
    rcases lt_or_ge k a with hka | hka
    · have h1 := hB k z hz
      have h2 := hM (B k) (Finset.mem_image_of_mem B (Finset.mem_range.2 hka))
      have h3 := le_max_left M (m : ℝ)
      linarith
    · have h1 := hcon k hka z hz
      have h3 := le_max_right M (m : ℝ)
      linarith
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_frequently hfr
  choose x hxK hx using hP
  obtain ⟨z, hz, σ, hσ, hlim⟩ := hKc.tendsto_subseq hxK
  refine ⟨φ ∘ σ, hφ.comp hσ, x ∘ σ, z, hz, hlim, ?_⟩
  refine tendsto_atTop_mono (fun k => ?_) (tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop)
  exact (hx (σ k)).le

/-- Selection of a finite set of blow-up points along a subsequence, under a concentration
hypothesis. -/
theorem exists_subseq_bounded_off_finite_of_concentration_aux (g : ℕ → ℂ → ℝ)
    (hg : ∀ k, Continuous (g k)) (f : ℕ → ℂ → ℝ≥0∞) (T γ : ℝ) (hγ : 0 < γ) (hT0 : 0 ≤ T)
    (hT : ∀ k, ∫⁻ z, f k z ≤ ENNReal.ofReal T)
    (hQ : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (ζ : ℕ → ℂ) (z : ℂ), Tendsto ζ atTop (𝓝 z) →
      Tendsto (fun k => g (ψ k) (ζ k)) atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ δ > 0, ∀ᶠ j in atTop,
        ENNReal.ofReal γ < ∫⁻ w in ball z δ, f (ψ (φ j)) w) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (Γ.card : ℝ) * γ ≤ T ∧
      (∀ Kc : Set ℂ, Kc ⊆ (↑Γ)ᶜ → IsCompact Kc → ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, g (φ k) z ≤ M) ∧
      ∀ z ∈ Γ, (∃ ζ : ℕ → ℂ, Tendsto ζ atTop (𝓝 z) ∧
          Tendsto (fun k => g (φ k) (ζ k)) atTop atTop) ∧
        ∀ δ > 0, ∀ᶠ j in atTop, ENNReal.ofReal γ < ∫⁻ w in ball z δ, f (φ j) w := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (T / γ)
  have hcard : ∀ ψ Γ, BUGood g f γ ψ Γ → Γ.card < N := by
    intro ψ Γ h
    have h1 := h.card_le hγ hT0 hT
    have h2 : (Γ.card : ℝ) ≤ T / γ := by rwa [le_div_iff₀ hγ]
    exact_mod_cast lt_of_le_of_lt h2 hN
  have key : ∀ d : ℕ, ∀ ψ Γ, BUGood g f γ ψ Γ → N ≤ Γ.card + d →
      ∃ φ : ℕ → ℕ, ∃ Γ' : Finset ℂ, BUGood g f γ φ Γ' ∧
        ∀ Kc : Set ℂ, Kc ⊆ (↑Γ')ᶜ → IsCompact Kc → ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, g (φ k) z ≤ M := by
    intro d
    induction d with
    | zero =>
      intro ψ Γ h hd
      exact absurd (hcard ψ Γ h) (by omega)
    | succ d ih =>
      intro ψ Γ h hd
      by_cases hbd : ∀ Kc : Set ℂ, Kc ⊆ (↑Γ)ᶜ → IsCompact Kc →
          ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, g (ψ k) z ≤ M
      · exact ⟨ψ, Γ, h, hbd⟩
      · push_neg at hbd
        obtain ⟨Kc, hKs, hKc, hun⟩ := hbd
        obtain ⟨θ, hθ, ζ, z, hz, hζ, hb⟩ :=
          bu_exists_blowup (fun k => g (ψ k)) (fun k => hg _) Kc hKc hun
        have hψθ : StrictMono (ψ ∘ θ) := h.1.comp hθ
        obtain ⟨φ, hφ, hs⟩ := hQ (ψ ∘ θ) hψθ ζ z hζ hb
        have hzΓ : z ∉ Γ := fun hzΓ => hKs hz (by simpa using hzΓ)
        have hnew : BUGood g f γ ((ψ ∘ θ) ∘ φ) (insert z Γ) := by
          refine ⟨hψθ.comp hφ, fun y hy => ?_⟩
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact ⟨⟨ζ ∘ φ, hζ.comp hφ.tendsto_atTop, hb.comp hφ.tendsto_atTop⟩, hs⟩
          · exact ((h.comp hθ).comp hφ).2 y hy
        exact ih _ _ hnew (by rw [Finset.card_insert_of_notMem hzΓ]; omega)
  have h0 : BUGood g f γ id ∅ := ⟨strictMono_id, by simp⟩
  obtain ⟨φ, Γ, hgood, hbd⟩ := key N id ∅ h0 (by simp)
  exact ⟨φ, hgood.1, Γ, hgood.card_le hγ hT0 hT, hbd, hgood.2⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (g : ℕ → ℂ → ℝ)
    (hg : ∀ k, Continuous (g k)) (f : ℕ → ℂ → ℝ≥0∞) (T γ : ℝ) (hγ : 0 < γ) (hT0 : 0 ≤ T)
    (hT : ∀ k, ∫⁻ z, f k z ≤ ENNReal.ofReal T)
    (hQ : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (ζ : ℕ → ℂ) (z : ℂ), Tendsto ζ atTop (𝓝 z) →
      Tendsto (fun k => g (ψ k) (ζ k)) atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ δ > 0, ∀ᶠ j in atTop,
        ENNReal.ofReal γ < ∫⁻ w in ball z δ, f (ψ (φ j)) w) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (Γ.card : ℝ) * γ ≤ T ∧
      (∀ Kc : Set ℂ, Kc ⊆ (↑Γ)ᶜ → IsCompact Kc → ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, g (φ k) z ≤ M) ∧
      ∀ z ∈ Γ, (∃ ζ : ℕ → ℂ, Tendsto ζ atTop (𝓝 z) ∧
          Tendsto (fun k => g (φ k) (ζ k)) atTop atTop) ∧
        ∀ δ > 0, ∀ᶠ j in atTop, ENNReal.ofReal γ < ∫⁻ w in ball z δ, f (φ j) w :=
  exists_subseq_bounded_off_finite_of_concentration_aux g hg f T γ hγ hT0 hT hQ
