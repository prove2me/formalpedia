-- Prove2me | solution 1 for FluVaccineCoord.TwoSided.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T15:02:33.001332+00:00
-- url     : https://prove2.me/submissions/305d6108-d963-4926-8b34-81cc87de2642

import Mathlib
import Definitions.Def_FluVaccineCoord_TwoSided_Model

set_option autoImplicit false

namespace FluVaccineCoord.TwoSided

open MeasureTheory Set Filter Topology

lemma hzr_mem (M : Model) : hzr M ∈ Icc (0:ℝ) 1 := by
  unfold hzr
  split_ifs with h1
  · have hmem : (1:ℝ) ∈ {h ∈ Icc (0 : ℝ) 1 | (1 - h) * M.u h + h * M.v h = 0} :=
      ⟨⟨zero_le_one, le_rfl⟩, by simp [h1]⟩
    exact ⟨le_csInf ⟨1, hmem⟩ (fun h hh => hh.1.1), csInf_le ⟨0, fun h hh => hh.1.1⟩ hmem⟩
  · exact ⟨zero_le_one, le_rfl⟩

lemma psi_le (M : Model) (hS : Standing M) {h m : ℝ} (hh0 : 0 ≤ h) (hhz : h ≤ hzr M)
    (hhm : h ≤ m) (hm1 : m ≤ 1) :
    (1 - m) * (M.u m - M.v m) ≤ (1 - h) * (M.u h - M.v h) := by
  have hz := hzr_mem M
  by_cases hmz : m ≤ hzr M
  · exact hS.A1_iv.antitoneOn ⟨hh0, hhz⟩ ⟨hh0.trans hhm, hmz⟩ hhm
  · push Not at hmz
    have hv1 : M.v 1 = 0 := by
      by_contra hne
      have : hzr M = 1 := by simp [hzr, hne]
      linarith
    obtain ⟨hu, hv⟩ := hS.zero_risk hv1 m ⟨hmz.le, hm1⟩
    rw [hu, hv]
    have h1 := hS.v_le_u h ⟨hh0, hhz.trans hz.2⟩
    have h2 : 0 ≤ 1 - h := by linarith [hz.2]
    nlinarith

lemma gbar_xc1 (M : Model) (hS : Standing M) (xc1 : ℝ) (hx : IsXc1 M xc1) :
    Gbar M xc1 ∈ Icc 0 (hzr M) := by
  have hxb := hS.xbar_pos
  have hz := hzr_mem M
  have key : ∀ x ∈ Icc (xzr M) M.xbar, Gbar M x ∈ Icc 0 (hzr M) := by
    rintro x ⟨h1, h2⟩
    unfold Gbar
    unfold xzr at h1
    constructor
    · rw [sub_nonneg, div_le_one hxb]; exact h2
    · rw [sub_le_comm, le_div_iff₀ hxb]; linarith
  rcases hx with ⟨_, rfl⟩ | ⟨_, hm, _⟩
  · exact key _ ⟨le_rfl, by unfold xzr; nlinarith [hz.1]⟩
  · exact key _ ⟨hm.1.le, hm.2.le⟩

lemma S_eq (M : Model) (hS : Standing M) {h Qr : ℝ} (hh0 : 0 ≤ h) (hhz : h ≤ hzr M)
    (hhQ : h ≤ Qr) :
    {x ∈ Icc 0 M.xbar | 0 < x * (M.u (vacc M x Qr) - M.v (vacc M x Qr))
        - M.xbar * ((1 - h) * (M.u h - M.v h))} = Ioc (M.xbar * (1 - h)) M.xbar := by
  have hxb := hS.xbar_pos
  have hz := hzr_mem M
  have hh1 : h ≤ 1 := hhz.trans hz.2
  ext x
  simp only [mem_setOf_eq, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨hx0, hxx⟩, hpos⟩
    refine ⟨?_, hxx⟩
    by_contra hle
    push Not at hle
    have hxd : x / M.xbar ≤ 1 - h := by rw [div_le_iff₀ hxb]; linarith
    have hxd0 : 0 ≤ x / M.xbar := div_nonneg hx0 hxb.le
    have hm_le : vacc M x Qr ≤ 1 - x / M.xbar := by unfold vacc Gbar; exact min_le_left _ _
    have hm_ge : h ≤ vacc M x Qr := by
      unfold vacc Gbar; exact le_min (by linarith) hhQ
    have hm1 : vacc M x Qr ≤ 1 := by linarith
    have hD : 0 ≤ M.u (vacc M x Qr) - M.v (vacc M x Qr) :=
      sub_nonneg.2 (hS.v_le_u _ ⟨hh0.trans hm_ge, hm1⟩)
    have hxle : x ≤ M.xbar * (1 - vacc M x Qr) := by
      have : x / M.xbar ≤ 1 - vacc M x Qr := by linarith
      rwa [div_le_iff₀ hxb, mul_comm] at this
    have h1 := mul_le_mul_of_nonneg_right hxle hD
    have h2 := mul_le_mul_of_nonneg_left (psi_le M hS hh0 hhz hm_ge hm1) hxb.le
    linarith
  · rintro ⟨hlt, hxx⟩
    have hx0 : 0 ≤ x := le_trans (mul_nonneg hxb.le (by linarith)) hlt.le
    refine ⟨⟨hx0, hxx⟩, ?_⟩
    have hgd : 1 - h < x / M.xbar := by rw [lt_div_iff₀ hxb]; linarith
    have hg0 : 0 ≤ 1 - x / M.xbar := by rw [sub_nonneg, div_le_one hxb]; exact hxx
    have hvg : vacc M x Qr = 1 - x / M.xbar := by
      unfold vacc Gbar; exact min_eq_left (by linarith)
    rw [hvg]
    have hlt2 := hS.A1_iv ⟨hg0, by linarith⟩ ⟨hh0, hhz⟩ (by linarith : 1 - x / M.xbar < h)
    simp only at hlt2
    have hxx' : M.xbar * (1 - (1 - x / M.xbar)) = x := by
      rw [sub_sub_cancel, mul_div_assoc', mul_div_cancel_left₀ x hxb.ne']
    have h3 := mul_lt_mul_of_pos_left hlt2 hxb
    rw [← mul_assoc M.xbar (1 - (1 - x / M.xbar)), hxx'] at h3
    linarith

lemma thr_rInc (M : Model) (hS : Standing M) (xc1 : ℝ) (hg1 : Gbar M xc1 ∈ Icc 0 (hzr M))
    {Qr : ℝ} (hQr : 0 ≤ Qr) : thr M (rInc M xc1 Qr) Qr = xc M xc1 Qr := by
  have hxb := hS.xbar_pos
  have hz := hzr_mem M
  have hh0 : 0 ≤ hc M xc1 Qr := le_min hg1.1 hQr
  have hhz : hc M xc1 Qr ≤ hzr M := by unfold hc; exact (min_le_left _ _).trans hg1.2
  have hhQ : hc M xc1 Qr ≤ Qr := by unfold hc; exact min_le_right _ _
  have hrr : M.w + M.p - rInc M xc1 Qr
      = M.xbar * ((1 - hc M xc1 Qr) * (M.u (hc M xc1 Qr) - M.v (hc M xc1 Qr))) := by
    unfold rInc; ring
  unfold thr
  rw [hrr, S_eq M hS hh0 hhz hhQ]
  show sInf (insert M.xbar (Ioc (M.xbar * (1 - hc M xc1 Qr)) M.xbar)) = M.xbar * (1 - hc M xc1 Qr)
  have hle : M.xbar * (1 - hc M xc1 Qr) ≤ M.xbar := by nlinarith
  rcases hle.lt_or_eq with hlt | heq
  · rw [insert_eq_of_mem (right_mem_Ioc.2 hlt), csInf_Ioc hlt]
  · rw [heq, Ioc_self]; simp

noncomputable def ut (M : Model) (z : ℝ) : ℝ := M.u (max 0 (min 1 z))
noncomputable def vt (M : Model) (z : ℝ) : ℝ := M.v (max 0 (min 1 z))

lemma proj_mem (z : ℝ) : max 0 (min 1 z) ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma ut_cont (M : Model) (hS : Standing M) : Continuous (ut M) :=
  hS.u_cont.comp_continuous (by fun_prop) proj_mem

lemma vt_cont (M : Model) (hS : Standing M) : Continuous (vt M) :=
  hS.v_cont.comp_continuous (by fun_prop) proj_mem

lemma ut_eq (M : Model) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : ut M z = M.u z := by
  unfold ut; rw [min_eq_right hz.2, max_eq_right hz.1]

lemma vt_eq (M : Model) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : vt M z = M.v z := by
  unfold vt; rw [min_eq_right hz.2, max_eq_right hz.1]

lemma ut_bdd (M : Model) (hS : Standing M) : ∃ B, 0 ≤ B ∧ ∀ z, |ut M z| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hS.u_cont
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  have := hC _ (proj_mem z)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

lemma vt_bdd (M : Model) (hS : Standing M) : ∃ B, 0 ≤ B ∧ ∀ z, |vt M z| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hS.v_cont
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  have := hC _ (proj_mem z)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

noncomputable def Ef (M : Model) (h : ℝ) : ℝ := (1 - h ^ 2) * M.u h + h ^ 2 * M.v h
noncomputable def Eft (M : Model) (h : ℝ) : ℝ := (1 - h ^ 2) * ut M h + h ^ 2 * vt M h
noncomputable def Wf (M : Model) (h : ℝ) : ℝ :=
  M.VH - M.p * h - M.xbar / 2 * ((1 - h) ^ 2 * M.u h + (1 - (1 - h) ^ 2) * M.v h)
noncomputable def Wft (M : Model) (h : ℝ) : ℝ :=
  M.VH - M.p * h - M.xbar / 2 * ((1 - h) ^ 2 * ut M h + (1 - (1 - h) ^ 2) * vt M h)

lemma Eft_cont (M : Model) (hS : Standing M) : Continuous (Eft M) := by
  have := ut_cont M hS; have := vt_cont M hS; unfold Eft; fun_prop

lemma Wft_cont (M : Model) (hS : Standing M) : Continuous (Wft M) := by
  have := ut_cont M hS; have := vt_cont M hS; unfold Wft; fun_prop

lemma Eft_eq (M : Model) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : Eft M z = Ef M z := by
  unfold Eft Ef; rw [ut_eq M hz, vt_eq M hz]

lemma Wft_eq (M : Model) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : Wft M z = Wf M z := by
  unfold Wft Wf; rw [ut_eq M hz, vt_eq M hz]

lemma ae_nonneg (M : Model) (hS : Standing M) : ∀ᵐ y ∂M.μ, 0 ≤ y := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS.yield_nonneg] with y hy
  simpa using hy

lemma int_hc (M : Model) (hS : Standing M) (xc1 Q : ℝ) (hQ : 0 ≤ Q)
    (hg : Gbar M xc1 ∈ Icc (0:ℝ) 1)
    (Φ Φt : ℝ → ℝ) (hΦt : Continuous Φt) (hag : ∀ z ∈ Icc (0:ℝ) 1, Φt z = Φ z) :
    Integrable (fun y => Φ (hc M xc1 (y * Q))) M.μ := by
  haveI := hS.prob
  have hHc : Continuous (fun y : ℝ => min (Gbar M xc1) (max y 0 * Q)) := by fun_prop
  have hHr : ∀ y : ℝ, min (Gbar M xc1) (max y 0 * Q) ∈ Icc (0:ℝ) 1 := fun y =>
    ⟨le_min hg.1 (mul_nonneg (le_max_right _ _) hQ), (min_le_left _ _).trans hg.2⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΦt.continuousOn (s := Icc (0:ℝ) 1))
  have hI : Integrable (fun y => Φt (min (Gbar M xc1) (max y 0 * Q))) M.μ :=
    Integrable.of_bound (hΦt.comp hHc).aestronglyMeasurable C
      (Eventually.of_forall fun y => hC _ (hHr y))
  refine hI.congr ?_
  filter_upwards [ae_nonneg M hS] with y hy
  show Φt (min (Gbar M xc1) (max y 0 * Q)) = Φ (min (Gbar M xc1) (y * Q))
  rw [hag _ (hHr y), max_eq_left hy]

lemma gbar_xc (M : Model) (hS : Standing M) (xc1 Qr : ℝ) :
    Gbar M (xc M xc1 Qr) = hc M xc1 Qr := by
  unfold Gbar xc; rw [mul_div_cancel_left₀ _ hS.xbar_pos.ne']; ring

lemma Gc_xc (M : Model) (hS : Standing M) (xc1 Qr : ℝ) :
    Gc M (xc M xc1 Qr) = 1 - hc M xc1 Qr := by
  unfold Gc xc; rw [mul_div_cancel_left₀ _ hS.xbar_pos.ne']

lemma vacc_xc (M : Model) (hS : Standing M) (xc1 Qr : ℝ) :
    vacc M (xc M xc1 Qr) Qr = hc M xc1 Qr := by
  unfold vacc; rw [gbar_xc M hS]; exact min_eq_left (min_le_right _ _)

lemma welfare_xc (M : Model) (hS : Standing M) (xc1 : ℝ) {Qr : ℝ} (hQr : 0 ≤ Qr)
    (hg0 : 0 ≤ Gbar M xc1) :
    welfare M (xc M xc1 Qr) Qr = Wf M (hc M xc1 Qr) := by
  unfold welfare
  rw [Gc_xc M hS, vacc_xc M hS]
  have h0' : (0:ℝ) ≤ hc M xc1 Qr := le_min hg0 hQr
  rcases h0'.eq_or_lt with h0 | hpos
  · rw [← h0]; unfold Wf; ring
  · have hF : fill M (xc M xc1 Qr) Qr = 1 := by
      unfold fill; rw [gbar_xc M hS]; apply min_eq_left
      rw [le_div_iff₀ hpos, one_mul]; unfold hc; exact min_le_right _ _
    rw [hF]; unfold Wf; ring

lemma Snet_eq (M : Model) (xc1 K Qr : ℝ) :
    Snet M xc1 K Qr = K - M.xbar / 2 * Ef M (hc M xc1 Qr) := by
  unfold Snet Tpay rInc Ef; ring

lemma piI_pt (M : Model) (hS : Standing M) (xc1 K : ℝ) (hg1 : Gbar M xc1 ∈ Icc 0 (hzr M))
    {Qr : ℝ} (hQr : 0 ≤ Qr) :
    M.w * vacc M (thr M (rInc M xc1 Qr) Qr) Qr + Tpay M xc1 K Qr
      = K - M.VH + Wf M (hc M xc1 Qr) := by
  rw [thr_rInc M hS xc1 hg1 hQr, vacc_xc M hS]; unfold Tpay Wf; ring

lemma indUtil_gen (M : Model) (rr t x Qr : ℝ) :
    indUtil M rr t x Qr = welfare M x Qr - (M.w - rr) * vacc M x Qr - t := by
  unfold indUtil welfare; ring

lemma indUtil_rInc (M : Model) (hS : Standing M) (xc1 : ℝ) (hg1 : Gbar M xc1 ∈ Icc 0 (hzr M))
    (t : ℝ) {Qr : ℝ} (hQr : 0 ≤ Qr) :
    indUtil M (rInc M xc1 Qr) t (thr M (rInc M xc1 Qr) Qr) Qr
      = M.VH - M.xbar / 2 * Ef M (hc M xc1 Qr) - t := by
  rw [indUtil_gen, thr_rInc M hS xc1 hg1 hQr, welfare_xc M hS xc1 hQr hg1.1, vacc_xc M hS]
  unfold Wf Ef rInc; ring

lemma thr_bdd (M : Model) (hS : Standing M) (rr Qr : ℝ) :
    BddBelow (insert M.xbar {x ∈ Icc 0 M.xbar |
      0 < x * (M.u (vacc M x Qr) - M.v (vacc M x Qr)) - (M.w + M.p - rr)}) :=
  ⟨0, by rintro z (rfl | ⟨⟨hz0, _⟩, _⟩); exacts [hS.xbar_pos.le, hz0]⟩

lemma thr_mem (M : Model) (hS : Standing M) (rr Qr : ℝ) : thr M rr Qr ∈ Icc 0 M.xbar := by
  have hxb := hS.xbar_pos
  unfold thr
  exact ⟨le_csInf (insert_nonempty _ _)
    (by rintro z (rfl | ⟨⟨hz0, _⟩, _⟩); exacts [hxb.le, hz0]),
    csInf_le (thr_bdd M hS rr Qr) (mem_insert _ _)⟩

lemma vacc_mem (M : Model) (hS : Standing M) {x Qr : ℝ} (hx : x ∈ Icc 0 M.xbar)
    (hQr : 0 ≤ Qr) : vacc M x Qr ∈ Icc (0:ℝ) 1 := by
  have hxb := hS.xbar_pos
  have h1 : 0 ≤ Gbar M x := by unfold Gbar; rw [sub_nonneg, div_le_one hxb]; exact hx.2
  have h2 : Gbar M x ≤ 1 := by unfold Gbar; have := div_nonneg hx.1 hxb.le; linarith
  exact ⟨le_min h1 hQr, (min_le_left _ _).trans h2⟩

lemma fill_mem (M : Model) (hS : Standing M) {x Qr : ℝ} (hx : x ∈ Icc 0 M.xbar)
    (hQr : 0 ≤ Qr) : fill M x Qr ∈ Icc (0:ℝ) 1 := by
  have hxb := hS.xbar_pos
  have h1 : 0 ≤ Gbar M x := by unfold Gbar; rw [sub_nonneg, div_le_one hxb]; exact hx.2
  exact ⟨le_min zero_le_one (div_nonneg hQr h1), min_le_left _ _⟩

lemma Gc_mem (M : Model) (hS : Standing M) {x : ℝ} (hx : x ∈ Icc 0 M.xbar) :
    Gc M x ∈ Icc (0:ℝ) 1 := by
  have hxb := hS.xbar_pos
  exact ⟨div_nonneg hx.1 hxb.le, (div_le_one hxb).2 hx.2⟩

lemma thr_usc (M : Model) (hS : Standing M) (Q : ℝ) (hQ : 0 ≤ Q) :
    UpperSemicontinuous (fun y : ℝ => thr M 0 (max y 0 * Q)) := by
  intro y0 a ha
  have ha' : sInf (insert M.xbar {x ∈ Icc 0 M.xbar | 0 < x * (M.u (vacc M x (max y0 0 * Q))
      - M.v (vacc M x (max y0 0 * Q))) - (M.w + M.p - 0)}) < a := ha
  obtain ⟨b, hb, hba⟩ := (csInf_lt_iff (thr_bdd M hS 0 _) (insert_nonempty _ _)).1 ha'
  rcases hb with rfl | ⟨hb0, hbpos⟩
  · exact Eventually.of_forall fun y =>
      lt_of_le_of_lt (csInf_le (thr_bdd M hS 0 _) (mem_insert _ _)) hba
  · have hvm : ∀ y : ℝ, vacc M b (max y 0 * Q) ∈ Icc (0:ℝ) 1 := fun y =>
      vacc_mem M hS hb0 (mul_nonneg (le_max_right _ _) hQ)
    have hcont : Continuous (fun y : ℝ => b * (ut M (vacc M b (max y 0 * Q))
        - vt M (vacc M b (max y 0 * Q))) - (M.w + M.p - 0)) := by
      have := ut_cont M hS; have := vt_cont M hS; unfold vacc; fun_prop
    have hag : ∀ y : ℝ, b * (ut M (vacc M b (max y 0 * Q)) - vt M (vacc M b (max y 0 * Q)))
        - (M.w + M.p - 0) = b * (M.u (vacc M b (max y 0 * Q)) - M.v (vacc M b (max y 0 * Q)))
        - (M.w + M.p - 0) := fun y => by rw [ut_eq M (hvm y), vt_eq M (hvm y)]
    have h0 : 0 < b * (ut M (vacc M b (max y0 0 * Q)) - vt M (vacc M b (max y0 0 * Q)))
        - (M.w + M.p - 0) := by rw [hag]; exact hbpos
    filter_upwards [(hcont.tendsto y0).eventually (lt_mem_nhds h0)] with y hy
    rw [hag] at hy
    exact lt_of_le_of_lt (csInf_le (thr_bdd M hS 0 _) (mem_insert_of_mem _ ⟨hb0, hy⟩)) hba

noncomputable def welt (M : Model) (x Qr : ℝ) : ℝ :=
  M.VH - M.p * vacc M x Qr - M.xbar / 2 * Gc M x ^ 2 * ut M (vacc M x Qr)
    - M.xbar / 2 * (1 - Gc M x ^ 2)
      * (fill M x Qr * vt M (vacc M x Qr) + (1 - fill M x Qr) * ut M (vacc M x Qr))

lemma welt_eq (M : Model) (hS : Standing M) {x Qr : ℝ} (hx : x ∈ Icc 0 M.xbar)
    (hQr : 0 ≤ Qr) : welt M x Qr = welfare M x Qr := by
  unfold welt welfare
  rw [ut_eq M (vacc_mem M hS hx hQr), vt_eq M (vacc_mem M hS hx hQr)]

lemma welt_meas (M : Model) (hS : Standing M) (X R : ℝ → ℝ) (hX : Measurable X)
    (hR : Measurable R) : Measurable (fun y => welt M (X y) (R y)) := by
  have hu := (ut_cont M hS).measurable
  have hv := (vt_cont M hS).measurable
  unfold welt vacc fill Gc Gbar
  fun_prop

lemma vw_meas (M : Model) (X R : ℝ → ℝ) (hX : Measurable X)
    (hR : Measurable R) : Measurable (fun y => M.w * vacc M (X y) (R y)) := by
  unfold vacc Gbar
  fun_prop

lemma alg_bound {VH p xb m G f U V Bu Bv : ℝ} (hp : 0 < p) (hxb : 0 < xb) (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1) (hG0 : 0 ≤ G) (hG1 : G ≤ 1) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hU : |U| ≤ Bu) (hV : |V| ≤ Bv) :
    |VH - p * m - xb / 2 * G ^ 2 * U - xb / 2 * (1 - G ^ 2) * (f * V + (1 - f) * U)|
      ≤ |VH| + p + xb / 2 * Bu + xb / 2 * (Bu + Bv) := by
  have hG2 : G ^ 2 ≤ 1 := by nlinarith
  have hG20 : 0 ≤ G ^ 2 := sq_nonneg _
  have hP2 : |G ^ 2 * U| ≤ Bu := by
    rw [abs_mul, abs_of_nonneg hG20]
    exact (mul_le_mul_of_nonneg_right hG2 (abs_nonneg U)).trans (by linarith)
  have hfV : |f * V| ≤ Bv := by
    rw [abs_mul, abs_of_nonneg hf0]
    exact (mul_le_mul_of_nonneg_right hf1 (abs_nonneg V)).trans (by linarith)
  have hfU : |(1 - f) * U| ≤ Bu := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - f)]
    exact (mul_le_mul_of_nonneg_right (by linarith : 1 - f ≤ 1) (abs_nonneg U)).trans
      (by linarith)
  have hW : |f * V + (1 - f) * U| ≤ Bu + Bv := by
    have a1 := abs_le.mp hfV
    have a2 := abs_le.mp hfU
    rw [abs_le]; constructor <;> linarith
  have hP3 : |(1 - G ^ 2) * (f * V + (1 - f) * U)| ≤ Bu + Bv := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - G ^ 2)]
    exact (mul_le_mul_of_nonneg_right (by linarith : 1 - G ^ 2 ≤ 1)
      (abs_nonneg _)).trans (by linarith)
  have h2 := abs_le.mp hP2
  have h3 := abs_le.mp hP3
  have hVH := abs_le.mp (le_refl |VH|)
  have hx2 : (0:ℝ) ≤ xb / 2 := by linarith
  have k1 : p * m ≤ p := by nlinarith
  have k1' : 0 ≤ p * m := by positivity
  have k2 := mul_le_mul_of_nonneg_left h2.2 hx2
  have k2' := mul_le_mul_of_nonneg_left h2.1 hx2
  have k3 := mul_le_mul_of_nonneg_left h3.2 hx2
  have k3' := mul_le_mul_of_nonneg_left h3.1 hx2
  rw [abs_le]
  constructor <;> linarith

lemma welt_bound (M : Model) (hS : Standing M) :
    ∃ C, ∀ x Qr, x ∈ Icc 0 M.xbar → 0 ≤ Qr → |welt M x Qr| ≤ C := by
  obtain ⟨Bu, _, hBu⟩ := ut_bdd M hS
  obtain ⟨Bv, _, hBv⟩ := vt_bdd M hS
  refine ⟨|M.VH| + M.p + M.xbar / 2 * Bu + M.xbar / 2 * (Bu + Bv), fun x Qr hx hQr => ?_⟩
  obtain ⟨hm0, hm1⟩ := vacc_mem M hS hx hQr
  obtain ⟨hf0, hf1⟩ := fill_mem M hS hx hQr
  obtain ⟨hG0, hG1⟩ := Gc_mem M hS hx
  exact alg_bound hS.p_pos hS.xbar_pos hm0 hm1 hG0 hG1 hf0 hf1 (hBu _) (hBv _)

lemma indUtil_zero (M : Model) (x Qr : ℝ) :
    indUtil M 0 0 x Qr = welfare M x Qr - M.w * vacc M x Qr := by
  rw [indUtil_gen]; ring

lemma EUtilD_eq (M : Model) (hS : Standing M) (Q : ℝ) (hQ : 0 ≤ Q) :
    EUtilD M Q = Wd M Q - piD M Q := by
  haveI := hS.prob
  have hXm : Measurable (fun y : ℝ => thr M 0 (max y 0 * Q)) := (thr_usc M hS Q hQ).measurable
  have hRm : Measurable (fun y : ℝ => max y 0 * Q) := by fun_prop
  have hR0 : ∀ y : ℝ, 0 ≤ max y 0 * Q := fun y => mul_nonneg (le_max_right _ _) hQ
  obtain ⟨C, hC⟩ := welt_bound M hS
  have hA : Integrable (fun y => welfare M (thr M 0 (y * Q)) (y * Q)) M.μ := by
    refine (Integrable.of_bound (welt_meas M hS _ _ hXm hRm).aestronglyMeasurable C
      (Eventually.of_forall fun y => ?_)).congr ?_
    · rw [Real.norm_eq_abs]; exact hC _ _ (thr_mem M hS _ _) (hR0 y)
    · filter_upwards [ae_nonneg M hS] with y hy
      simp only [max_eq_left hy]
      exact welt_eq M hS (thr_mem M hS _ _) (mul_nonneg hy hQ)
  have hB : Integrable (fun y => M.w * vacc M (thr M 0 (y * Q)) (y * Q)) M.μ := by
    refine (Integrable.of_bound (vw_meas M _ _ hXm hRm).aestronglyMeasurable M.w
      (Eventually.of_forall fun y => ?_)).congr ?_
    · obtain ⟨hm0, hm1⟩ := vacc_mem M hS (thr_mem M hS 0 (max y 0 * Q)) (hR0 y)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hS.w_pos, abs_of_nonneg hm0]
      nlinarith [hS.w_pos]
    · filter_upwards [ae_nonneg M hS] with y hy
      simp only [max_eq_left hy]
  unfold EUtilD Wd piD
  simp_rw [indUtil_zero]
  rw [integral_sub hA hB]
  ring

end FluVaccineCoord.TwoSided

open FluVaccineCoord.TwoSided MeasureTheory Set in
theorem solution (M : Model) (hS : Standing M) (xc1 : ℝ) (hx : IsXc1 M xc1)
    (Qc : ℝ) (hQc0 : 0 ≤ Qc) (hQc : IsMaxOn (Wc M xc1) (Ici 0) Qc) (K : ℝ) :
    K - Kbn M xc1 Qc = ∫ y, Snet M xc1 K (y * Qc) ∂M.μ ∧
      IsMaxOn (piI M xc1 K) (Ici 0) Qc ∧
      (∀ Q, 0 ≤ Q → IsMaxOn (piI M xc1 K) (Ici 0) Q → IsMaxOn (Wc M xc1) (Ici 0) Q) ∧
      EUtilI M xc1 (K - Kbn M xc1 Qc) Qc = M.VH - K ∧
      piI M xc1 K Qc = K + Wc M xc1 Qc - M.VH ∧
      (∀ Qd, 0 ≤ Qd → IsMaxOn (piD M) (Ici 0) Qd →
        Kunder M xc1 Qc Qd < K → piD M Qd < piI M xc1 K Qc) ∧
      (∀ Qd, 0 ≤ Qd → IsMaxOn (piD M) (Ici 0) Qd →
        K < Kover M Qd → EUtilD M Qd < EUtilI M xc1 (K - Kbn M xc1 Qc) Qc) := by
  haveI := hS.prob
  have hz := hzr_mem M
  have hg1 : Gbar M xc1 ∈ Icc 0 (hzr M) := gbar_xc1 M hS xc1 hx
  have hg1' : Gbar M xc1 ∈ Icc (0:ℝ) 1 := ⟨hg1.1, hg1.2.trans hz.2⟩
  have hae := ae_nonneg M hS
  have hconst : ∀ c : ℝ, ∫ _y, c ∂M.μ = c := fun c => by simp
  have hE : Integrable (fun y => Ef M (hc M xc1 (y * Qc))) M.μ :=
    int_hc M hS xc1 Qc hQc0 hg1' (Ef M) (Eft M) (Eft_cont M hS) (fun z hz => Eft_eq M hz)
  have hKbn : Kbn M xc1 Qc = M.xbar / 2 * ∫ y, Ef M (hc M xc1 (y * Qc)) ∂M.μ := rfl
  have hSnet : ∫ y, Snet M xc1 K (y * Qc) ∂M.μ = K - Kbn M xc1 Qc := by
    simp_rw [Snet_eq]
    rw [integral_sub (integrable_const K) (hE.const_mul _), integral_const_mul, hconst, hKbn]
  have hpiI : ∀ Q, 0 ≤ Q → piI M xc1 K Q = K - M.VH + Wc M xc1 Q := by
    intro Q hQ
    have hW : Integrable (fun y => Wf M (hc M xc1 (y * Q))) M.μ :=
      int_hc M hS xc1 Q hQ hg1' (Wf M) (Wft M) (Wft_cont M hS) (fun z hz => Wft_eq M hz)
    have e1 : ∫ y, (M.w * vacc M (thr M (rInc M xc1 (y * Q)) (y * Q)) (y * Q)
        + Tpay M xc1 K (y * Q)) ∂M.μ = ∫ y, (K - M.VH + Wf M (hc M xc1 (y * Q))) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards [hae] with y hy
      exact piI_pt M hS xc1 K hg1 (mul_nonneg hy hQ)
    have e2 : ∫ y, welfare M (xc M xc1 (y * Q)) (y * Q) ∂M.μ
        = ∫ y, Wf M (hc M xc1 (y * Q)) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards [hae] with y hy
      exact welfare_xc M hS xc1 (mul_nonneg hy hQ) hg1.1
    unfold piI Wc
    rw [e1, e2, integral_add (integrable_const _) hW, hconst]
    ring
  have hEU : EUtilI M xc1 (K - Kbn M xc1 Qc) Qc = M.VH - K := by
    unfold EUtilI
    have e : ∫ y, indUtil M (rInc M xc1 (y * Qc)) (K - Kbn M xc1 Qc)
        (thr M (rInc M xc1 (y * Qc)) (y * Qc)) (y * Qc) ∂M.μ
        = ∫ y, ((M.VH - (K - Kbn M xc1 Qc)) - M.xbar / 2 * Ef M (hc M xc1 (y * Qc))) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards [hae] with y hy
      exact (indUtil_rInc M hS xc1 hg1 _ (mul_nonneg hy hQc0)).trans (by ring)
    rw [e, integral_sub (integrable_const _) (hE.const_mul _), integral_const_mul, hconst,
      ← hKbn]
    ring
  refine ⟨hSnet.symm, ?_, ?_, hEU, ?_, ?_, ?_⟩
  · rw [isMaxOn_iff]
    intro z hz
    have h1 : Wc M xc1 z ≤ Wc M xc1 Qc := isMaxOn_iff.1 hQc z hz
    rw [hpiI z hz, hpiI Qc hQc0]; linarith
  · intro Q hQ hmax
    rw [isMaxOn_iff] at hmax ⊢
    intro z hz
    have h1 := hmax z hz
    rw [hpiI z hz, hpiI Q hQ] at h1; linarith
  · rw [hpiI Qc hQc0]; ring
  · intro Qd _ _ hK
    rw [hpiI Qc hQc0]; unfold Kunder at hK; linarith
  · intro Qd hQd _ hK
    rw [hEU, EUtilD_eq M hS Qd hQd]; unfold Kover at hK; linarith
