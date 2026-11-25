-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hit_of_isPlaneOpenBook
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T15:54:14.894956+00:00
-- url     : https://prove2.me/submissions/8d0ecadc-9821-48de-8def-61e958a74ba8

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_uniform_hit_near_orbit
import Theorems.Thm_FiniteEnergyPlane_exists_pos_le_leaf_speed
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
import Theorems.Thm_FiniteEnergyPlane_IsReebTrajectory_apply_not_mem_range_of_apply_zero



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_hit_of_isPlaneOpenBook_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (l : ℕ) (hl : 1 ≤ l) (U : ℝ × ℂ → V 1) (hU : IsPlaneOpenBook H J P l U)
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (hy₀ : y 0 ∉ Set.range P.x) (θ n : ℝ) :
    (∃ t > n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) ∧
      (∃ t < n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) := by
  obtain ⟨hUC, hper, hfast, -, huniq, hinj, hpos⟩ := hU
  have hoff := IsReebTrajectory.apply_not_mem_range_of_apply_zero hH P hy hy₀
  have hne : ∀ p, U p ≠ 0 := fun p => (hfast p.1).1.1.2.1 p.2 trivial
  obtain ⟨W, hW, hPW, L, hL, hhit⟩ :=
    exists_uniform_hit_near_orbit H hH J hJ P hcz _ (hfast θ).1 (hfast θ).2.1
  -- integer periodicity of the leaves
  have hperk : ∀ (k : ℤ) (a : ℝ) (z : ℂ), pageMap H U (a + k, z) = pageMap H U (a, z) := by
    intro k a z
    have h := Function.Periodic.int_mul (f := fun a : ℝ => pageMap H U (a, z)) (c := 1)
      (fun a => by simp only [pageMap, hper]) k a
    simpa using h
  -- every point off the orbit is on a leaf, unique modulo `1`
  have hleaf : ∀ q ∈ energySurface H, q ∉ Set.range P.x → ∃ p, pageMap H U p = q :=
    fun q hq hqP => let ⟨p, hp, _⟩ := huniq q hq hqP; ⟨p, hp.2⟩
  have hmod : ∀ t a b, y t ∈ Set.range (fun z => pageMap H U (a, z)) →
      y t ∈ Set.range (fun z => pageMap H U (b, z)) → ∃ k : ℤ, a = b + k := by
    rintro t a b ⟨z, hz⟩ ⟨w, hw⟩
    obtain ⟨p, -, hp⟩ := huniq (y t) (hy.1 t) (hoff t)
    have h : ∀ a z, pageMap H U (a, z) = y t → Int.fract a = p.1 := by
      intro a z hz
      refine congrArg Prod.fst (hp (Int.fract a, z) ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩)
      rw [← hperk ⌊a⌋, Int.fract_add_floor]; exact hz
    refine ⟨⌊a⌋ - ⌊b⌋, ?_⟩
    have h3 := (h a z hz).trans (h b w hw).symm
    rw [Int.fract, Int.fract] at h3
    push_cast; linarith
  set K : Set (V 1) := energySurface H \ W with hKdef
  have hK : IsCompact K := (isCompact_energySurface H hH).diff hW
  obtain ⟨ε, hε, hsp⟩ := exists_pos_le_leaf_speed H hH U (hUC.of_le (by exact_mod_cast hl)) hne
    hinj hpos K hK (fun q hq => hleaf q hq.1 fun h => hq.2 (hPW h))
  -- an interval spent in `K` without a hit is short
  have key : ∀ I : Set ℝ, IsOpen I → Convex ℝ I → (∀ t ∈ I, y t ∈ K) →
      (∀ t ∈ I, y t ∉ Set.range (fun z => pageMap H U (θ, z))) →
      ∀ a ∈ I, ∀ b ∈ I, a ≤ b → ε * (b - a) ≤ 1 := by
    intro I hI hIc hIK hIn a ha b hb hab
    have hex : ∀ t, t ∈ I → ∃ r ∈ Set.Ioo θ (θ + 1),
        y t ∈ Set.range (fun z => pageMap H U (r, z)) := by
      intro t ht
      obtain ⟨p, hp⟩ := hleaf (y t) (hy.1 t) (hoff t)
      refine ⟨θ + Int.fract (p.1 - θ), ⟨?_, by linarith [Int.fract_lt_one (p.1 - θ)]⟩, p.2, ?_⟩
      · rcases (Int.fract_nonneg (p.1 - θ)).lt_or_eq with h | h
        · linarith
        · exfalso
          refine hIn t ht ⟨p.2, ?_⟩
          have : θ + (⌊p.1 - θ⌋ : ℤ) = p.1 := by rw [Int.fract] at h; linarith
          simp only
          rw [← hperk ⌊p.1 - θ⌋, this]; exact hp
      · simp only
        rw [← hperk ⌊p.1 - θ⌋]
        have : θ + Int.fract (p.1 - θ) + (⌊p.1 - θ⌋ : ℤ) = p.1 := by rw [Int.fract]; ring
        rw [this]; exact hp
    choose! g hgI hg using hex
    have hd : ∀ t ∈ I, ∃ d, ε ≤ d ∧ HasDerivAt g d t := by
      intro t ht
      obtain ⟨f, d, hεd, hfd, hf⟩ := hsp y hy t (hIK t ht)
      obtain ⟨k, hk⟩ := hmod t _ _ hf.self_of_nhds (hg t ht)
      refine ⟨d, hεd, (hfd.sub_const (k : ℝ)).congr_of_eventuallyEq ?_⟩
      have hc : ContinuousAt (fun s => f s - k) t := hfd.continuousAt.sub continuousAt_const
      have hmem : ∀ᶠ s in 𝓝 t, f s - k ∈ Set.Ioo θ (θ + 1) :=
        hc.eventually (isOpen_Ioo.mem_nhds (by
          show f t - k ∈ _
          rw [hk]; simpa using hgI t ht))
      filter_upwards [hf, hmem, hI.mem_nhds ht] with s h1 h2 h3
      obtain ⟨m, hm⟩ := hmod s _ _ h1 (hg s h3)
      have h4 := hgI s h3
      have h5 : ((m - k : ℤ) : ℝ) < 1 := by push_cast; linarith [h2.1, h2.2, h4.1, h4.2]
      have h5' : (-1 : ℝ) < ((m - k : ℤ) : ℝ) := by push_cast; linarith [h2.1, h2.2, h4.1, h4.2]
      have h6 : (m - k : ℤ) < 1 := by exact_mod_cast h5
      have h7 : (-1 : ℤ) < m - k := by exact_mod_cast h5'
      have h8 : m = k := by omega
      rw [hm, h8]; ring
    have h := hIc.mul_sub_le_image_sub_of_le_deriv (f := g)
      (fun t ht => (hd t ht).choose_spec.2.continuousAt.continuousWithinAt)
      (by rw [hI.interior_eq]
          exact fun t ht => (hd t ht).choose_spec.2.differentiableAt.differentiableWithinAt)
      (C := ε) (by
        rw [hI.interior_eq]; intro t ht
        rw [(hd t ht).choose_spec.2.deriv]; exact (hd t ht).choose_spec.1) a ha b hb hab
    linarith [(hgI a ha).1, (hgI b hb).2]
  -- a visit to `W` forces hits on both sides
  have hvis : ∀ t, y t ∈ W →
      (∃ s > t, y s ∈ Set.range (fun z => pageMap H U (θ, z))) ∧
      (∃ s < t, y s ∈ Set.range (fun z => pageMap H U (θ, z))) := by
    intro t ht
    have hyt : IsReebTrajectory H (fun s => y (s + t)) := by
      refine ⟨fun s => hy.1 _, fun s => ?_⟩
      have := (hy.2 (s + t)).scomp s ((hasDerivAt_id s).add_const t)
      rwa [one_smul] at this
    obtain ⟨⟨s, hs, h⟩, ⟨s', hs', h'⟩⟩ := hhit _ hyt (by simpa using ht) (by simpa using hoff t)
    exact ⟨⟨s + t, by linarith [hs.1], h⟩, ⟨s' + t, by linarith [hs'.2], h'⟩⟩
  have h2 : ε * (2 / ε) = 2 := mul_div_cancel₀ _ hε.ne'
  have h0 := div_pos two_pos hε
  constructor
  · by_contra hno
    push Not at hno
    have hK' : ∀ t ∈ Set.Ioi n, y t ∈ K := fun t ht => ⟨hy.1 t, fun hw => by
      obtain ⟨s, hs, h⟩ := (hvis t hw).1
      exact hno s (lt_trans ht hs) h⟩
    have := key (Set.Ioi n) isOpen_Ioi (convex_Ioi n) hK' hno (n + 1) (by simp)
      (n + 1 + 2 / ε) (by simp only [Set.mem_Ioi]; linarith) (by linarith)
    rw [add_sub_cancel_left, h2] at this
    linarith
  · by_contra hno
    push Not at hno
    have hK' : ∀ t ∈ Set.Iio n, y t ∈ K := fun t ht => ⟨hy.1 t, fun hw => by
      obtain ⟨s, hs, h⟩ := (hvis t hw).2
      exact hno s (lt_trans hs ht) h⟩
    have := key (Set.Iio n) isOpen_Iio (convex_Iio n) hK' hno (n - 1 - 2 / ε)
      (by simp only [Set.mem_Iio]; linarith) (n - 1) (by simp) (by linarith)
    rw [sub_sub_cancel, h2] at this
    linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate)
    (l : ℕ) (hl : 1 ≤ l) (U : ℝ × ℂ → V 1) (hU : IsPlaneOpenBook H J P l U)
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (hy₀ : y 0 ∉ Set.range P.x) (θ n : ℝ) :
    (∃ t > n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) ∧
      (∃ t < n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) :=
  exists_hit_of_isPlaneOpenBook_aux H hH J hJ P hcz l hl U hU y hy hy₀ θ n
