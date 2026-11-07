-- Prove2me | solution 1 for FiniteEnergyPlane.exists_mul_norm_sub_le_of_isCompact_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T16:37:55.089679+00:00
-- url     : https://prove2.me/submissions/94b7b809-bc95-4ff1-b078-f01b2634a74f

import Mathlib



namespace FiniteEnergyPlane

open Metric Filter Topology

/-- A `C¹` map on a finite-dimensional space that separates the off-diagonal pairs of a compact set
`Q` of pairs of points, and has injective derivative at the diagonal pairs of `Q`, satisfies a
uniform lower Lipschitz bound on `Q`. -/
theorem exists_mul_norm_sub_le_of_isCompact_pairs_aux {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E → F) (hG : ContDiff ℝ 1 G) (Q : Set (E × E)) (hQ : IsCompact Q)
    (hne : ∀ p ∈ Q, p.1 ≠ p.2 → G p.1 ≠ G p.2)
    (hd : ∀ p ∈ Q, p.1 = p.2 → Function.Injective (fderiv ℝ G p.1)) :
    ∃ c > 0, ∀ p ∈ Q, c * ‖p.1 - p.2‖ ≤ ‖G p.1 - G p.2‖ := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ p ∈ Q, ‖G p.1 - G p.2‖ < (1 / ((n : ℝ) + 1)) * ‖p.1 - p.2‖ :=
    fun n => hcon _ (by positivity)
  choose q hqQ hq using hseq
  obtain ⟨p, hpQ, φ, hφ, hlim⟩ := hQ.tendsto_subseq hqQ
  have hφtop : Tendsto (fun n => ((φ n : ℕ) : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hinv : Tendsto (fun n => 1 / (((φ n : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hφtop
  have hl1 : Tendsto (fun n => (q (φ n)).1) atTop (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hl2 : Tendsto (fun n => (q (φ n)).2) atTop (𝓝 p.2) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  by_cases hpp : p.1 = p.2
  · -- diagonal limit
    have hs : HasStrictFDerivAt G (fderiv ℝ G p.1) p.1 :=
      hG.contDiffAt.hasStrictFDerivAt (by norm_num)
    obtain ⟨K, hKpos, hK⟩ := LinearMap.exists_antilipschitzWith
      (fderiv ℝ G p.1).toLinearMap (LinearMap.ker_eq_bot.2 (hd p hpQ hpp))
    have hlow : ∀ v : E, ‖v‖ ≤ (K : ℝ) * ‖fderiv ℝ G p.1 v‖ := by
      intro v
      have := hK.le_mul_dist v 0
      simpa [dist_eq_norm] using this
    have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    set δ : ℝ := 1 / (2 * (K : ℝ)) with hδ
    have hδpos : 0 < δ := by positivity
    have hev := hs.isLittleO.def hδpos
    have hpair : Tendsto (fun n => ((q (φ n)).1, (q (φ n)).2)) atTop (𝓝 (p.1, p.1)) := by
      have := hl1.prodMk_nhds (hpp ▸ hl2 : Tendsto (fun n => (q (φ n)).2) atTop (𝓝 p.1))
      exact this
    have hev' := (hpair.eventually hev).and
      ((hinv.eventually (gt_mem_nhds (show (0 : ℝ) < δ by positivity))))
    obtain ⟨n, hn1, hn2⟩ := hev'.exists
    simp only at hn1
    have hq' := hq (φ n)
    set a := (q (φ n)).1
    set b := (q (φ n)).2
    have hnorm : ‖fderiv ℝ G p.1 (a - b)‖ ≤ ‖G a - G b‖ + δ * ‖a - b‖ := by
      have htri : fderiv ℝ G p.1 (a - b) = (G a - G b) - (G a - G b - fderiv ℝ G p.1 (a - b)) := by
        abel
      rw [htri]
      refine (norm_sub_le _ _).trans ?_
      gcongr
    have h1 := hlow (a - b)
    have hab : 0 ≤ ‖a - b‖ := norm_nonneg _
    have hpos : 0 < ‖a - b‖ := by
      have : (0 : ℝ) ≤ ‖G a - G b‖ := norm_nonneg _
      by_contra h0
      have h00 : ‖a - b‖ = 0 := le_antisymm (not_lt.1 h0) hab
      rw [h00, mul_zero] at hq'
      linarith
    have h5 : (K : ℝ) * (2 * δ * ‖a - b‖) = ‖a - b‖ * ((K : ℝ) * (2 * δ)) := by ring
    have h6 : (K : ℝ) * (2 * δ) = 1 := by
      rw [hδ]; field_simp
    have h7 : ‖G a - G b‖ < δ * ‖a - b‖ := by
      refine hq'.trans_le ?_
      gcongr
    have h8 : ‖a - b‖ < (K : ℝ) * (2 * δ * ‖a - b‖) := by
      refine h1.trans_lt ?_
      refine mul_lt_mul_of_pos_left ?_ hKr
      linarith
    rw [h5, h6, mul_one] at h8
    exact lt_irrefl _ h8
  · -- off-diagonal limit
    apply hne p hpQ hpp
    have hGc := hG.continuous
    have hbound : ∃ M, ∀ n, ‖(q (φ n)).1 - (q (φ n)).2‖ ≤ M := by
      obtain ⟨M, hM⟩ := (hQ.image (continuous_fst.sub continuous_snd)).isBounded.exists_norm_le
      exact ⟨M, fun n => hM _ ⟨_, hqQ _, rfl⟩⟩
    obtain ⟨M, hM⟩ := hbound
    have h0 : Tendsto (fun n => ‖G (q (φ n)).1 - G (q (φ n)).2‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => norm_nonneg _) (g := fun n => 1 / (((φ n : ℕ) : ℝ) + 1) * M)
        (fun n => ?_) (by simpa using hinv.mul_const M)
      refine (hq (φ n)).le.trans ?_
      gcongr
      exact hM n
    have h1 : Tendsto (fun n => ‖G (q (φ n)).1 - G (q (φ n)).2‖) atTop (𝓝 ‖G p.1 - G p.2‖) :=
      (((hGc.tendsto _).comp hl1).sub ((hGc.tendsto _).comp hl2)).norm
    have := tendsto_nhds_unique h1 h0
    exact sub_eq_zero.1 (norm_eq_zero.1 this)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E → F) (hG : ContDiff ℝ 1 G) (Q : Set (E × E)) (hQ : IsCompact Q)
    (hne : ∀ p ∈ Q, p.1 ≠ p.2 → G p.1 ≠ G p.2)
    (hd : ∀ p ∈ Q, p.1 = p.2 → Function.Injective (fderiv ℝ G p.1)) :
    ∃ c > 0, ∀ p ∈ Q, c * ‖p.1 - p.2‖ ≤ ‖G p.1 - G p.2‖ :=
  exists_mul_norm_sub_le_of_isCompact_pairs_aux G hG Q hQ hne hd
