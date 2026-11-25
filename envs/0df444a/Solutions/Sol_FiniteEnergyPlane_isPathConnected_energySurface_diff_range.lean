-- Prove2me | solution 1 for FiniteEnergyPlane.isPathConnected_energySurface_diff_range
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T12:13:57.699526+00:00
-- url     : https://prove2.me/submissions/d7ff89ab-c9c5-40d1-bc35-51b07eb80227

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma pfo_ne_zero {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

lemma pfo_proj_mem {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) :
    H (proj H y) = 1 := proj_mem_energySurface H hH y hy

lemma pfo_proj_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) {r : ℝ} (hr : 0 < r) : proj H (r • x) = x :=
  proj_smul_eq_of_mem_energySurface H hH x hx r hr

lemma pfo_proj_self {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : proj H x = x := by
  simpa using pfo_proj_smul hH hx one_pos

lemma pfo_eq_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : y ≠ 0) : ∃ r : ℝ, y = Real.exp r • proj H y := by
  obtain ⟨s, hs, hsy⟩ := (hH.2.1 _ hy).exists
  refine ⟨-Real.log s, ?_⟩
  have h := pfo_proj_smul hH hsy (inv_pos.2 hs)
  rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at h
  rw [h, Real.exp_neg, Real.exp_log hs, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

lemma pfo_smul_eq {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x q : V n} {r : ℝ}
    (hx : H x = 1) (hq : H q = 1) (h : Real.exp r • x = q) : x = q := by
  rw [← pfo_proj_smul hH hx (Real.exp_pos r), h, pfo_proj_self hH hq]

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isPathConnected_energySurface_diff_range_aux {n : ℕ} (hn : 1 ≤ n) (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (x : ℝ → V n) (hx : ContDiff ℝ 1 x)
    (hxS : ∀ t, x t ∈ energySurface H) :
    IsPathConnected (energySurface H \ Set.range x) := by
  let G : Set (V n) := {y | y ≠ 0 ∧ proj H y ∉ Set.range x}
  have hG : ∀ y, y ≠ 0 → (∀ r t : ℝ, y ≠ Real.exp r • x t) → y ∈ G := by
    rintro y hy h
    refine ⟨hy, ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨r, hr⟩ := pfo_eq_smul hH hy
    exact h r t (by rw [ht]; exact hr)
  have hG' : ∀ y ∈ G, ∀ r t : ℝ, y ≠ Real.exp r • x t := by
    rintro y hy r t rfl
    exact hy.2 ⟨t, (pfo_proj_smul hH (hxS t) (Real.exp_pos r)).symm⟩
  have himg : proj H '' G = energySurface H \ Set.range x := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨pfo_proj_mem hH hy.1, hy.2⟩
    · rintro ⟨hq, hqx⟩
      have h := pfo_proj_self hH hq
      exact ⟨q, ⟨pfo_ne_zero hH hq, by rwa [h]⟩, h⟩
  -- the sets of points not visible from `q`
  let f : V n → ℝ × ℝ × ℝ → V n := fun q p => q + p.1 • (Real.exp p.2.1 • x p.2.2 - q)
  let g : V n → ℝ → V n := fun q s => s • q
  have hf : ∀ q, dimH (Set.range (f q)) ≤ 3 := fun q => by
    have hc : ContDiff ℝ 1 (f q) := by
      refine contDiff_const.add (contDiff_fst.smul (ContDiff.sub ?_ contDiff_const))
      exact (Real.contDiff_exp.comp (contDiff_fst.comp contDiff_snd)).smul
        (hx.comp (contDiff_snd.comp contDiff_snd))
    refine hc.dimH_range_le.trans ?_
    simp [Module.finrank_prod]
  have hg : ∀ q, dimH (Set.range (g q)) ≤ 3 := fun q => by
    have hc : ContDiff ℝ 1 (g q) := contDiff_id.smul contDiff_const
    refine hc.dimH_range_le.trans ?_
    simp
  have hvis : ∀ q ∈ G, ∀ b, b ∉ Set.range (f q) → b ∉ Set.range (g q) → JoinedIn G q b := by
    intro q hq b hb hb'
    refine JoinedIn.of_segment_subset ?_
    rw [segment_eq_image]
    rintro _ ⟨θ, hθ, rfl⟩
    rcases eq_or_ne θ 0 with rfl | h0
    · simpa using hq
    apply hG
    · intro h
      refine hb' ⟨1 - θ⁻¹, ?_⟩
      have h2 : θ⁻¹ • ((1 - θ) • q + θ • b) = 0 := by simp only at h; rw [h, smul_zero]
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ h0, one_smul] at h2
      show (1 - θ⁻¹) • q = b
      rw [eq_comm, ← sub_eq_zero, ← h2, mul_sub, inv_mul_cancel₀ h0]
      module
    · intro r t h
      refine hb ⟨(θ⁻¹, r, t), ?_⟩
      show q + θ⁻¹ • (Real.exp r • x t - q) = b
      rw [← h]
      have : (1 - θ) • q + θ • b - q = θ • (b - q) := by module
      simp only
      rw [this, smul_smul, inv_mul_cancel₀ h0, one_smul]
      abel
  have hdense : ∀ q q' : V n, ∃ b, (b ∉ Set.range (f q) ∧ b ∉ Set.range (g q)) ∧
      b ∉ Set.range (f q') ∧ b ∉ Set.range (g q') := fun q q' => by
    have hd : dimH ((Set.range (f q) ∪ Set.range (g q)) ∪ (Set.range (f q') ∪ Set.range (g q'))) <
        Module.finrank ℝ (V n) := by
      rw [dimH_union, dimH_union, dimH_union]
      refine lt_of_le_of_lt (max_le (max_le (hf q) (hg q)) (max_le (hf q') (hg q'))) ?_
      rw [Module.finrank_fin_fun]
      have : 3 < 2 * (n + 1) := by omega
      exact_mod_cast this
    obtain ⟨b, hb⟩ := (dense_compl_of_dimH_lt_finrank hd).nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hb
    exact ⟨b, hb⟩
  have hne : G.Nonempty := by
    obtain ⟨b, ⟨hb, hb'⟩, -⟩ := hdense 0 0
    refine ⟨b, hG b (fun h => hb' ⟨0, by simp [g, h]⟩) fun r t h => hb ⟨(1, r, t), by simp [f, h]⟩⟩
  have hGc : IsPathConnected G := by
    rw [isPathConnected_iff]
    refine ⟨hne, fun q hq q' hq' => ?_⟩
    obtain ⟨b, ⟨h1, h2⟩, h3, h4⟩ := hdense q q'
    exact (hvis q hq b h1 h2).trans (hvis q' hq' b h3 h4).symm
  rw [← himg]
  exact hGc.image' fun y hy =>
    (contDiffAt_aCoord_proj H hH y hy.1).2.continuousAt.continuousWithinAt

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (hn : 1 ≤ n) (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (x : ℝ → V n) (hx : ContDiff ℝ 1 x)
    (hxS : ∀ t, x t ∈ energySurface H) :
    IsPathConnected (energySurface H \ Set.range x) :=
  isPathConnected_energySurface_diff_range_aux hn H hH x hx hxS
