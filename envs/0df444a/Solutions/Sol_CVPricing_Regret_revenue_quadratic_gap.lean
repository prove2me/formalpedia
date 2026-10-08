-- Prove2me | solution 1 for CVPricing.Regret.revenue_quadratic_gap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:52:56.603266+00:00
-- url     : https://prove2.me/submissions/ab69055f-3d4a-448c-94a2-12a2f430f9d4

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP

set_option autoImplicit false

/-- One-sided quadratic bound from a Lipschitz-type bound on the derivative around `c`. -/
theorem p60_key (f : ℝ → ℝ) (c q K : ℝ)
    (hd : ∀ t ∈ Set.uIcc c q, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Set.uIcc c q, |deriv f t| ≤ K * |t - c|) :
    f c - f q ≤ K / 2 * (q - c) ^ 2 := by
  set g : ℝ → ℝ := fun t => f t + K / 2 * (t - c) ^ 2 with hg
  have hgd : ∀ t ∈ Set.uIcc c q, HasDerivAt g (deriv f t + K * (t - c)) t := by
    intro t ht
    have h1 := (hd t ht).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => K / 2 * (t - c) ^ 2) (K * (t - c)) t := by
      have hx : HasDerivAt (fun x : ℝ => x - c) 1 t := (hasDerivAt_id' t).sub_const c
      have h3 := (hx.mul hx).const_mul (K / 2)
      refine (h3.congr_deriv (by ring)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => ?_)
      simp only [Pi.mul_apply]
      ring
    exact h1.add h2
  have hcont : ContinuousOn g (Set.uIcc c q) := fun t ht =>
    (hgd t ht).continuousAt.continuousWithinAt
  rcases le_total c q with hcq | hqc
  · have hU : Set.uIcc c q = Set.Icc c q := Set.uIcc_of_le hcq
    rw [hU] at hgd hcont hb
    have hmono : MonotoneOn g (Set.Icc c q) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc c q) hcont
      · intro t ht
        rw [interior_Icc] at ht
        exact (hgd t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht' := Set.Ioo_subset_Icc_self ht
        rw [(hgd t ht').deriv]
        have hb' := hb t ht'
        have habs : |t - c| = t - c := abs_of_nonneg (by linarith [ht.1])
        rw [habs] at hb'
        have := neg_abs_le (deriv f t)
        linarith
    have := hmono (Set.left_mem_Icc.2 hcq) (Set.right_mem_Icc.2 hcq) hcq
    simp only [hg, sub_self] at this
    nlinarith [this]
  · have hU : Set.uIcc c q = Set.Icc q c := Set.uIcc_of_ge hqc
    rw [hU] at hgd hcont hb
    have hanti : AntitoneOn g (Set.Icc q c) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc q c) hcont
      · intro t ht
        rw [interior_Icc] at ht
        exact (hgd t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht' := Set.Ioo_subset_Icc_self ht
        rw [(hgd t ht').deriv]
        have hb' := hb t ht'
        have habs : |t - c| = c - t := by
          rw [abs_of_nonpos (by linarith [ht.2])]; ring
        rw [habs] at hb'
        have := le_abs_self (deriv f t)
        linarith
    have := hanti (Set.left_mem_Icc.2 hqc) (Set.right_mem_Icc.2 hqc) hqc
    simp only [hg, sub_self] at this
    nlinarith [this]

open CVPricing.Regret in
theorem p60_pOpt (M : Model) :
    pOpt M ∈ Set.Ioo M.pl M.ph ∧
      ∀ q ∈ Set.Icc M.pl M.ph, revenue M.h M.a0 q ≤ revenue M.h M.a0 (pOpt M) := by
  obtain ⟨U, _, ha0, hall⟩ := M.nbhd
  obtain ⟨q0, hq0, hstrict, _⟩ := hall M.a0 ha0
  have hmax : ∀ q ∈ Set.Icc M.pl M.ph, revenue M.h M.a0 q ≤ revenue M.h M.a0 q0 := by
    intro q hq
    by_cases h : q = q0
    · rw [h]
    · exact (hstrict q hq h).le
  have hex : ∃ q, ∀ q', IsRevMaxOn M M.a0 (Set.Icc M.pl M.ph) q' ↔ q' = q := by
    refine ⟨q0, fun q' => ⟨fun h => ?_, fun h => ?_⟩⟩
    · by_contra hne
      have := hstrict q' h.1 hne
      have := h.2 q0 (Set.Ioo_subset_Icc_self hq0)
      linarith
    · subst h
      exact ⟨Set.Ioo_subset_Icc_self hq0, hmax⟩
  have hp : pOpt M = q0 := by
    unfold pOpt optPriceOf
    rw [dif_pos hex]
    have hq0max : IsRevMaxOn M M.a0 (Set.Icc M.pl M.ph) q0 :=
      ⟨Set.Ioo_subset_Icc_self hq0, hmax⟩
    exact ((Classical.choose_spec hex q0).1 hq0max).symm
  rw [hp]
  exact ⟨hq0, hmax⟩

open CVPricing.Regret in
theorem p60_contDiff (M : Model) :
    ContDiffOn ℝ 2 (revenue M.h M.a0) {p : ℝ | 0 < M.a0.1 + M.a0.2 * p} := by
  have haff : ContDiff ℝ 2 (fun p : ℝ => M.a0.1 + M.a0.2 * p) := by
    fun_prop
  have hcomp : ContDiffOn ℝ 2 (M.h ∘ fun p : ℝ => M.a0.1 + M.a0.2 * p)
      {p : ℝ | 0 < M.a0.1 + M.a0.2 * p} :=
    M.h_contDiffOn.comp haff.contDiffOn (fun p (hp : 0 < M.a0.1 + M.a0.2 * p) => Set.mem_Ici.2 hp.le)
  have : revenue M.h M.a0 = fun p => p * (M.h ∘ fun p : ℝ => M.a0.1 + M.a0.2 * p) p := by
    funext p; rfl
  rw [this]
  exact contDiffOn_id.mul hcomp

open CVPricing.Regret in
theorem solution (M : Model) :
    ∀ q ∈ Set.Icc M.pl M.ph,
      |revenue M.h M.a0 q - revenue M.h M.a0 (pOpt M)| ≤
        sSup ((fun x => |deriv (deriv (revenue M.h M.a0)) x|) '' Set.Icc M.pl M.ph) / 2 *
          (q - pOpt M) ^ 2 := by
  intro q hq
  set r := revenue M.h M.a0 with hr
  set S : Set ℝ := {p : ℝ | 0 < M.a0.1 + M.a0.2 * p} with hS
  have hSopen : IsOpen S := isOpen_lt continuous_const (by fun_prop)
  have hIS : Set.Icc M.pl M.ph ⊆ S := by
    intro p hp
    show 0 < M.a0.1 + M.a0.2 * p
    have h1 := M.a01_neg
    have h2 := M.a0_ph_pos
    nlinarith [hp.2]
  have hcd : ContDiffOn ℝ 2 r S := p60_contDiff M
  have hcd1 : ContDiffOn ℝ 1 (deriv r) S := hcd.deriv_of_isOpen hSopen (by norm_num)
  have hcont2 : ContinuousOn (deriv (deriv r)) S :=
    hcd1.continuousOn_deriv_of_isOpen hSopen (by norm_num)
  have hdiff1 : ∀ x ∈ S, DifferentiableAt ℝ (deriv r) x := fun x hx =>
    (hcd1.contDiffAt (hSopen.mem_nhds hx)).differentiableAt (by norm_num)
  have hdiff0 : ∀ x ∈ S, DifferentiableAt ℝ r x := fun x hx =>
    (hcd.contDiffAt (hSopen.mem_nhds hx)).differentiableAt (by norm_num)
  set K := sSup ((fun x => |deriv (deriv r) x|) '' Set.Icc M.pl M.ph) with hK
  have hbdd : BddAbove ((fun x => |deriv (deriv r) x|) '' Set.Icc M.pl M.ph) := by
    have hc : ContinuousOn (fun x => |deriv (deriv r) x|) (Set.Icc M.pl M.ph) :=
      (hcont2.mono hIS).abs
    exact (isCompact_Icc.image_of_continuousOn hc).bddAbove
  have hKb : ∀ x ∈ Set.Icc M.pl M.ph, ‖deriv (deriv r) x‖ ≤ K := fun x hx =>
    le_csSup hbdd ⟨x, hx, rfl⟩
  obtain ⟨hpI, hmax⟩ := p60_pOpt M
  set c := pOpt M with hc
  have hcI : c ∈ Set.Icc M.pl M.ph := Set.Ioo_subset_Icc_self hpI
  have hloc : IsLocalMax r c := by
    have : Set.Icc M.pl M.ph ∈ nhds c := Icc_mem_nhds hpI.1 hpI.2
    exact Filter.mem_of_superset this (fun x hx => hmax x hx)
  have hd0 : deriv r c = 0 := hloc.deriv_eq_zero
  have hsub : Set.uIcc c q ⊆ Set.Icc M.pl M.ph := Set.uIcc_subset_Icc hcI hq
  have hkey := p60_key r c q K (fun t ht => hdiff0 t (hIS (hsub ht))) (by
    intro t ht
    have := (convex_Icc M.pl M.ph).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => hdiff1 x (hIS hx)) hKb hcI (hsub ht)
    simpa [hd0, Real.norm_eq_abs] using this)
  have hle : r q ≤ r c := hmax q hq
  rw [abs_of_nonpos (by linarith)]
  linarith
