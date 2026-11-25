-- Prove2me | solution 1 for CosmologyFLRW.lt_of_mem_I_of_decelerating
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:01:13.109585+00:00
-- url     : https://prove2.me/submissions/49e11d70-fe42-4962-b82d-2f18e9d8fe45

import Definitions.Def_FLRWBigBangBound

open CosmologyFLRW Set

lemma deriv_antitoneOn (U : FLRWModel) (hdec : ∀ s ∈ U.I, deriv (deriv U.a) s ≤ 0) :
    AntitoneOn (deriv U.a) U.I := by
  have hconv : Convex ℝ U.I := U.ordConnected_I.convex
  have hint : interior U.I = U.I := U.isOpen_I.interior_eq
  refine antitoneOn_of_deriv_nonpos hconv U.differentiableOn_deriv_a.continuousOn ?_ ?_
  · rw [hint]; exact U.differentiableOn_deriv_a
  · rw [hint]; exact hdec

lemma tangent (U : FLRWModel)
    (hdec : ∀ s ∈ U.I, deriv (deriv U.a) s ≤ 0)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ U.I) (ht : t ∈ U.I) :
    U.a t ≤ U.a t₀ + deriv U.a t₀ * (t - t₀) := by
  have hanti := deriv_antitoneOn U hdec
  rcases lt_trichotomy t₀ t with hlt | heq | hgt
  · have hsub : Icc t₀ t ⊆ U.I := U.ordConnected_I.out ht₀ ht
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope U.a hlt
      (U.differentiableOn_a.continuousOn.mono hsub)
      (U.differentiableOn_a.mono (Ioo_subset_Icc_self.trans hsub))
    have hcI : c ∈ U.I := hsub (Ioo_subset_Icc_self hc)
    have hle : deriv U.a c ≤ deriv U.a t₀ := hanti ht₀ hcI hc.1.le
    have hpos : 0 < t - t₀ := sub_pos.mpr hlt
    rw [eq_div_iff hpos.ne'] at hcd
    nlinarith
  · subst heq; simp
  · have hsub : Icc t t₀ ⊆ U.I := U.ordConnected_I.out ht ht₀
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope U.a hgt
      (U.differentiableOn_a.continuousOn.mono hsub)
      (U.differentiableOn_a.mono (Ioo_subset_Icc_self.trans hsub))
    have hcI : c ∈ U.I := hsub (Ioo_subset_Icc_self hc)
    have hle : deriv U.a t₀ ≤ deriv U.a c := hanti hcI ht₀ hc.2.le
    have hpos : 0 < t₀ - t := sub_pos.mpr hgt
    rw [eq_div_iff hpos.ne'] at hcd
    nlinarith

theorem solution (U : FLRWModel)
    (hdec : ∀ s ∈ U.I, deriv (deriv U.a) s ≤ 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U.I) (h0 : 0 < deriv U.a t₀)
    {t : ℝ} (ht : t ∈ U.I) :
    t₀ - U.a t₀ / deriv U.a t₀ < t := by
  have h1 := tangent U hdec ht₀ ht
  have h2 := U.a_pos t ht
  rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ h0]
  nlinarith

