-- Prove2me | solution 1 for DelaunayStretch.lemma_4_8_derivatives_along_curves
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:53:57.497042+00:00
-- url     : https://prove2.me/submissions/212a27d4-2541-4a02-919e-41d3f9f65f7a

import Mathlib
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

open DelaunayStretch Filter Topology Set

namespace Lemma48Aux

lemma clm_apply_eq_dot4 (L : R4 →L[ℝ] ℝ) (w : R4) :
    L w = dot4 (L (1, 0, 0, 0), L (0, 1, 0, 0), L (0, 0, 1, 0), L (0, 0, 0, 1)) w := by
  have hw : w = w.1 • ((1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)) + w.2.1 • ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ))
      + w.2.2.1 • ((0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ))
      + w.2.2.2 • ((0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    obtain ⟨a, b, c, d⟩ := w
    simp
  conv_lhs => rw [hw]
  simp only [map_add, map_smul, smul_eq_mul, dot4]
  ring

lemma isolated_countable (S : Set ℝ) : {t ∈ S | 𝓝[S \ {t}] t = ⊥}.Countable := by
  refine (countable_setOfPred_isolated_right_within (s := S)).mono ?_
  intro t ht
  refine ⟨ht.1, ?_⟩
  rw [← le_bot_iff, ← ht.2]
  exact nhdsWithin_mono _ (fun s hs => ⟨hs.1, fun h => (ne_of_gt hs.2) h⟩)

lemma deriv_eq_of_accPt {f g : ℝ → ℝ} {a b t : ℝ} {S : Set ℝ} (hf : HasDerivAt f a t)
    (hg : HasDerivAt g b t) (ht : t ∈ S) (hS : ∀ s ∈ S, f s = g s)
    (hne : (𝓝[S \ {t}] t).NeBot) : a = b := by
  have hsub : 𝓝[S \ {t}] t ≤ 𝓝[≠] t := nhdsWithin_mono _ (fun s hs => hs.2)
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left hsub
  have h2 := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left hsub
  have heq : slope f t =ᶠ[𝓝[S \ {t}] t] slope g t := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [slope, vsub_eq_sub, hS s hs.1, hS t ht]
  exact tendsto_nhds_unique h1 (h2.congr' heq.symm)

end Lemma48Aux

open Lemma48Aux

theorem solution (H : R4 → ℝ) (hH : CondH0 H) (P : PiecewiseC1 H)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (z : ℝ → R4) (hz : ContDiffOn ℝ 1 z (Set.Icc t₀ t₁))
    (hzΩ : Set.MapsTo z (Set.Icc t₀ t₁) OmegaTimesR) :
    AbsolutelyContinuousOnInterval (fun t => H (z t)) t₀ t₁ ∧
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc t₀ t₁)),
      ∃ g : R4, P.IncidentGradient (z t) g ∧
        HasDerivAt (fun t => H (z t)) (dot4 g (deriv z t)) t := by
  obtain ⟨Kz, hKz⟩ := hz.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hcomp : IsCompact (z '' Icc t₀ t₁) := isCompact_Icc.image_of_continuousOn hz.continuousOn
  obtain ⟨KH, hKH⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcomp
    (hH.2.mono (by rintro _ ⟨s, hs, rfl⟩; exact hzΩ hs))
  have hg : LipschitzOnWith (KH * Kz) (fun t => H (z t)) (Icc t₀ t₁) :=
    hKH.comp hKz (mapsTo_image z _)
  refine ⟨?_, ?_⟩
  · apply LipschitzOnWith.absolutelyContinuousOnInterval (K := KH * Kz)
    rw [uIcc_of_le ht]
    exact hg
  · have hae := (hg.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem_real
    set T : Fin P.m → Set ℝ := fun i => {s | s ∈ Icc t₀ t₁ ∧ z s ∈ P.Z i} with hT
    have hcount : ((⋃ i, {t ∈ T i | 𝓝[T i \ {t}] t = ⊥}) ∪ {t₀, t₁}).Countable :=
      (countable_iUnion (fun i => isolated_countable (T i))).union
        ((countable_singleton _).insert _)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae, hcount.ae_notMem MeasureTheory.volume] with t h1 h2 htI
    have hne0 : t ≠ t₀ := fun h => h2 (Or.inr (Or.inl h))
    have hne1 : t ≠ t₁ := fun h => h2 (Or.inr (Or.inr h))
    have htIoo : t ∈ Ioo t₀ t₁ := ⟨lt_of_le_of_ne htI.1 (Ne.symm hne0), lt_of_le_of_ne htI.2 hne1⟩
    have hgd : DifferentiableAt ℝ (fun t => H (z t)) t :=
      (h1 htIoo).differentiableAt (Ioo_mem_nhds htIoo.1 htIoo.2)
    obtain ⟨i, hzi⟩ := P.cover (z t) (hzΩ htI)
    have htT : t ∈ T i := ⟨htI, hzi⟩
    have hNe : (𝓝[T i \ {t}] t).NeBot := by
      refine ⟨fun hbot => h2 (Or.inl ?_)⟩
      exact mem_iUnion.2 ⟨i, htT, hbot⟩
    obtain ⟨V, hV, hZV, hF⟩ := P.smooth i
    have hFd : DifferentiableAt ℝ (P.F i) (z t) :=
      (hF.differentiableOn one_ne_zero (z t) (hZV hzi)).differentiableAt (hV.mem_nhds (hZV hzi))
    have hzd : DifferentiableAt ℝ z t :=
      (hz.differentiableOn one_ne_zero t htI).differentiableAt (Icc_mem_nhds htIoo.1 htIoo.2)
    have hFz : HasDerivAt (fun s => P.F i (z s)) (fderiv ℝ (P.F i) (z t) (deriv z t)) t :=
      hFd.hasFDerivAt.comp_hasDerivAt t hzd.hasDerivAt
    have heq : deriv (fun t => H (z t)) t = fderiv ℝ (P.F i) (z t) (deriv z t) :=
      deriv_eq_of_accPt hgd.hasDerivAt hFz htT (fun s hs => P.agree i (z s) hs.2) hNe
    refine ⟨gradient4 (P.F i) (z t), ⟨i, hzi, rfl⟩, ?_⟩
    have hdot : dot4 (gradient4 (P.F i) (z t)) (deriv z t)
        = fderiv ℝ (P.F i) (z t) (deriv z t) := (clm_apply_eq_dot4 _ _).symm
    rw [hdot, ← heq]
    exact hgd.hasDerivAt
