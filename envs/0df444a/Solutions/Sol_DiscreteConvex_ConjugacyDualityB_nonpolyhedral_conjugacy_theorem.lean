-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.nonpolyhedral_conjugacy_theorem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T06:09:50.149551+00:00
-- url     : https://prove2.me/submissions/bf1887d2-60e2-4fb4-b720-696f454457eb

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsClosedProperConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateRW

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NonPolyConjAux

open DiscreteConvex.ConjugacyDualityB
open Classical
open scoped Pointwise BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Legendre-Fenchel transform for closed proper convex functions -/

lemma fromE_coe (t : ℝ) : FromEReal ((t : ℝ) : EReal) = ((t : ℝ) : WithTop ℝ) := rfl
lemma fromE_top : FromEReal (⊤ : EReal) = ⊤ := rfl
lemma fromE_bot : FromEReal (⊥ : EReal) = ⊤ := rfl
lemma toE_coe (t : ℝ) : ToEReal ((t : ℝ) : WithTop ℝ) = ((t : ℝ) : EReal) := rfl
lemma toE_top : ToEReal (⊤ : WithTop ℝ) = (⊤ : EReal) := rfl

lemma fromE_ge {s : ℝ} {S : EReal} (h : (s : EReal) ≤ S) : ((s : ℝ) : WithTop ℝ) ≤ FromEReal S := by
  induction S using EReal.rec with
  | bot => exact absurd h (by simp)
  | coe t => rw [fromE_coe]; exact WithTop.coe_le_coe.2 (EReal.coe_le_coe_iff.1 h)
  | top => rw [fromE_top]; exact le_top

lemma fromE_le {C : ℝ} {S : EReal} (hb : S ≠ ⊥) (h : S ≤ (C : EReal)) :
    FromEReal S ≤ ((C : ℝ) : WithTop ℝ) := by
  induction S using EReal.rec with
  | bot => exact absurd rfl hb
  | coe t => rw [fromE_coe]; exact WithTop.coe_le_coe.2 (EReal.coe_le_coe_iff.1 h)
  | top => exact absurd h (by simp)

lemma cc_unfold (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) :
    ConvexConjugateRW f p = FromEReal (sSup {v : EReal | ∃ x : V → ℝ,
      v = ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f x)}) := rfl

lemma term_top {f : (V → ℝ) → WithTop ℝ} {x : V → ℝ} (h : f x = ⊤) (s : ℝ) :
    (s : EReal) - ToEReal (f x) = ⊥ := by
  rw [h, toE_top, EReal.sub_top]

lemma term_val {f : (V → ℝ) → WithTop ℝ} {x : V → ℝ} {a : ℝ} (h : f x = (a : WithTop ℝ)) (s : ℝ) :
    (s : EReal) - ToEReal (f x) = ((s - a : ℝ) : EReal) := by
  rw [h, toE_coe, ← EReal.coe_sub]

lemma cc_ge {f : (V → ℝ) → WithTop ℝ} {x : V → ℝ} {a : ℝ} (h : f x = (a : WithTop ℝ))
    (p : V → ℝ) :
    (((∑ i, p i * x i) - a : ℝ) : WithTop ℝ) ≤ ConvexConjugateRW f p := by
  rw [cc_unfold]
  apply fromE_ge
  apply le_sSup
  exact ⟨x, by rw [term_val h]⟩

lemma cc_le {f : (V → ℝ) → WithTop ℝ} {p : V → ℝ} {C : ℝ} (hne : (DomR f).Nonempty)
    (h : ∀ x (a : ℝ), f x = (a : WithTop ℝ) → (∑ i, p i * x i) - a ≤ C) :
    ConvexConjugateRW f p ≤ ((C : ℝ) : WithTop ℝ) := by
  rw [cc_unfold]
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨a0, ha0⟩ := WithTop.ne_top_iff_exists.1 hx0
  apply fromE_le
  · apply ne_bot_of_le_ne_bot (EReal.coe_ne_bot ((∑ i, p i * x0 i) - a0))
    apply le_sSup
    exact ⟨x0, by rw [term_val ha0.symm]⟩
  · apply sSup_le
    rintro t ⟨x, rfl⟩
    by_cases hx : f x = ⊤
    · rw [term_top hx]; exact bot_le
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hx
      rw [term_val ha.symm]
      exact EReal.coe_le_coe_iff.2 (h x a ha.symm)

lemma cc_bdd {f : (V → ℝ) → WithTop ℝ} {p : V → ℝ} {c : ℝ}
    (hc : ConvexConjugateRW f p = ((c : ℝ) : WithTop ℝ)) {x : V → ℝ} {a : ℝ}
    (h : f x = (a : WithTop ℝ)) : (∑ i, p i * x i) - a ≤ c := by
  have := cc_ge h p
  rw [hc] at this
  exact WithTop.coe_le_coe.1 this

lemma cc_empty {f : (V → ℝ) → WithTop ℝ} (h : ∀ x, f x = ⊤) :
    ConvexConjugateRW f = fun _ => ⊤ := by
  funext p
  rw [cc_unfold]
  have hs : sSup {v : EReal | ∃ x : V → ℝ,
      v = ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f x)} = ⊥ := by
    apply sSup_eq_bot.2
    rintro v ⟨x, rfl⟩
    exact term_top (h x) _
  rw [hs, fromE_bot]

lemma cc_top_of_unbdd {f : (V → ℝ) → WithTop ℝ} {p : V → ℝ}
    (h : ∀ M : ℝ, ∃ x, ∃ a : ℝ, f x = (a : WithTop ℝ) ∧ M ≤ (∑ i, p i * x i) - a) :
    ConvexConjugateRW f p = ⊤ := by
  by_contra hne
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hne
  obtain ⟨x, a, ha, hM⟩ := h (c + 1)
  have h1 := cc_ge ha p
  rw [← hc, WithTop.coe_le_coe] at h1
  linarith

lemma cc_exists_gt {f : (V → ℝ) → WithTop ℝ} {p : V → ℝ} {c : ℝ}
    (hc : ConvexConjugateRW f p = (c : WithTop ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : V → ℝ, ∃ a : ℝ, f x = (a : WithTop ℝ) ∧ c - ε < (∑ i, p i * x i) - a := by
  by_contra hall
  push_neg at hall
  have hne : (DomR f).Nonempty := by
    by_contra hdom
    have htop : ∀ x, f x = ⊤ := fun x => by by_contra hx; exact hdom ⟨x, hx⟩
    have := congrFun (cc_empty htop) p
    rw [hc] at this
    exact WithTop.coe_ne_top this
  have hle : ConvexConjugateRW f p ≤ ((c - ε : ℝ) : WithTop ℝ) := cc_le hne hall
  rw [hc, WithTop.coe_le_coe] at hle
  linarith

lemma biconj_le {f : (V → ℝ) → WithTop ℝ} (hne : (DomR (ConvexConjugateRW f)).Nonempty)
    (x : V → ℝ) : ConvexConjugateRW (ConvexConjugateRW f) x ≤ f x := by
  induction hfx : f x using WithTop.recTopCoe with
  | top => exact le_top
  | coe a =>
    refine cc_le hne fun p c hpc => ?_
    have h1 := cc_ge hfx p
    rw [hpc, WithTop.coe_le_coe] at h1
    have hcomm : ∑ i, x i * p i = ∑ i, p i * x i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    linarith

def EpiSet (f : (V → ℝ) → WithTop ℝ) : Set ((V → ℝ) × ℝ) :=
  {q | f q.1 ≤ (q.2 : WithTop ℝ)}

lemma epiSet_isClosed {f : (V → ℝ) → WithTop ℝ} (hlsc : LowerSemicontinuous f) :
    IsClosed (EpiSet f) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨x0, r0⟩ h0
  simp only [EpiSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at h0
  obtain ⟨r1, hr01, hr1x⟩ : ∃ r1 : ℝ, r0 < r1 ∧ ((r1 : ℝ) : WithTop ℝ) < f x0 := by
    induction hfx : f x0 using WithTop.recTopCoe with
    | top => exact ⟨r0 + 1, by linarith, WithTop.coe_lt_top _⟩
    | coe a =>
      rw [hfx, WithTop.coe_lt_coe] at h0
      exact ⟨(r0 + a) / 2, by linarith, by rw [WithTop.coe_lt_coe]; linarith⟩
  refine ⟨{x | ((r1 : ℝ) : WithTop ℝ) < f x} ×ˢ Set.Iio r1, ?_,
    (hlsc.isOpen_preimage (r1 : WithTop ℝ)).prod isOpen_Iio, ⟨hr1x, hr01⟩⟩
  rintro ⟨x, r⟩ ⟨hx, hr⟩
  simp only [EpiSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  exact (WithTop.coe_lt_coe.mpr hr).trans hx

lemma psm_le_coe {a r : ℝ} (ha : 0 ≤ a) {z : WithTop ℝ} (hz : z ≤ (r : WithTop ℝ)) :
    PosScalarMul a z ≤ ((a * r : ℝ) : WithTop ℝ) := by
  induction z using WithTop.recTopCoe with
  | top => exact absurd hz (by simp)
  | coe v =>
    rw [WithTop.coe_le_coe] at hz
    simp only [PosScalarMul, WithTop.coe_le_coe]
    exact mul_le_mul_of_nonneg_left hz ha

lemma epiSet_convex {f : (V → ℝ) → WithTop ℝ} (hconv : IsConvexWithTop f) :
    Convex ℝ (EpiSet f) := by
  rintro ⟨x, r⟩ hxr ⟨y, s⟩ hys a b ha hb hab
  simp only [EpiSet, Set.mem_setOf_eq] at hxr hys ⊢
  change f (a • x + b • y) ≤ ((a * r + b * s : ℝ) : WithTop ℝ)
  have hb_eq : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have h1 := hconv x y a ha ha1
  have heq : (fun v => a * x v + (1 - a) * y v) = a • x + b • y := by
    funext v; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb_eq]
  rw [← heq]
  refine h1.trans ?_
  rw [← hb_eq]
  exact (add_le_add (psm_le_coe ha hxr) (psm_le_coe hb hys)).trans (by rw [← WithTop.coe_add])

lemma clm_decomp (L : ((V → ℝ) × ℝ) →L[ℝ] ℝ) (y : V → ℝ) (r : ℝ) :
    L (y, r) = - (∑ v : V, (- L (Pi.single v 1, 0)) * y v) + L (0, 1) * r := by
  have hy : y = ∑ v : V, y v • (Pi.single v (1 : ℝ) : V → ℝ) := by
    ext v; simp [Finset.sum_apply, Pi.single_apply]
  have hpair : (y, r) = ∑ v : V, y v • ((Pi.single v (1 : ℝ) : V → ℝ), (0 : ℝ)) +
      r • ((0 : V → ℝ), (1 : ℝ)) := by
    ext v
    · conv_lhs => rw [hy]
      simp [Prod.fst_sum, Prod.smul_fst]
    · simp [Prod.snd_sum, Prod.smul_snd]
  conv_lhs => rw [hpair]
  rw [map_add, map_sum, map_smul, smul_eq_mul]
  have hsum : ∑ v : V, L (y v • (Pi.single v 1, (0 : ℝ))) =
      - ∑ v : V, (- L (Pi.single v 1, 0)) * y v := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, smul_eq_mul]
    ring
  rw [hsum]
  ring

lemma sep_epiSet {f : (V → ℝ) → WithTop ℝ} (hf : IsClosedProperConvex f)
    {x : V → ℝ} {s : ℝ} (hxs : (x, s) ∉ EpiSet f) :
    ∃ (a : V → ℝ) (c u : ℝ), 0 ≤ c ∧
      - (∑ v, a v * x v) + c * s < u ∧
      ∀ y : V → ℝ, ∀ r : ℝ, f y ≤ (r : WithTop ℝ) → u < - (∑ v, a v * y v) + c * r := by
  obtain ⟨L, u, hLxs, hLE⟩ := geometric_hahn_banach_point_closed
    (epiSet_convex hf.2.2) (epiSet_isClosed hf.2.1) hxs
  let a : V → ℝ := fun v => - L (Pi.single v 1, 0)
  let c : ℝ := L (0, 1)
  have hL : ∀ y r, L (y, r) = - (∑ v, a v * y v) + c * r := clm_decomp L
  obtain ⟨x0, hx0⟩ := hf.1
  obtain ⟨r0, hr0⟩ := WithTop.ne_top_iff_exists.1 hx0
  have hc : 0 ≤ c := by
    by_contra hc_neg
    push_neg at hc_neg
    let t : ℝ := (|u| + |∑ v, a v * x0 v| + |c * r0| + 1) / (-c)
    have ht_pos : 0 < t := div_pos (by positivity) (by linarith)
    have hmem : (x0, r0 + t) ∈ EpiSet f := by
      simp only [EpiSet, Set.mem_setOf_eq, ← hr0, WithTop.coe_le_coe]
      linarith
    have hlt := hLE (x0, r0 + t) hmem
    rw [hL] at hlt
    have hct : c * t = - (|u| + |∑ v, a v * x0 v| + |c * r0| + 1) := by
      dsimp [t]
      have hne : -c ≠ 0 := by linarith
      calc c * ((|u| + |∑ v, a v * x0 v| + |c * r0| + 1) / -c)
          = - ((-c) * ((|u| + |∑ v, a v * x0 v| + |c * r0| + 1) / -c)) := by ring
        _ = - (|u| + |∑ v, a v * x0 v| + |c * r0| + 1) := by rw [mul_div_cancel₀ _ hne]
    have h1 := neg_abs_le u
    have h2 := neg_abs_le (∑ v, a v * x0 v)
    have h3 := le_abs_self (c * r0)
    have hcr : c * (r0 + t) = c * r0 + c * t := mul_add c r0 t
    linarith
  refine ⟨a, c, u, hc, ?_, ?_⟩
  · rwa [← hL]
  · intro y r hyr
    rw [← hL]
    exact hLE (y, r) hyr

lemma closed_proper_dom_conj {f : (V → ℝ) → WithTop ℝ} (hf : IsClosedProperConvex f) :
    ∃ (p0 : V → ℝ) (c0 : ℝ), ConvexConjugateRW f p0 ≤ (c0 : WithTop ℝ) ∧
      ∀ y (r : ℝ), f y = (r : WithTop ℝ) → (∑ v, p0 v * y v) - r ≤ c0 := by
  obtain ⟨x0, hx0⟩ := hf.1
  obtain ⟨r0, hr0⟩ := WithTop.ne_top_iff_exists.1 hx0
  have hnot : (x0, r0 - 1) ∉ EpiSet f := by
    simp only [EpiSet, Set.mem_setOf_eq, ← hr0, WithTop.coe_le_coe]
    linarith
  obtain ⟨a, c, u, hc, hlt, hgt⟩ := sep_epiSet hf hnot
  have hgt0 : u < - (∑ v, a v * x0 v) + c * r0 :=
    hgt x0 r0 (by simp [← hr0])
  have hc_pos : 0 < c := by linarith
  let p0 : V → ℝ := fun v => a v / c
  let c0 : ℝ := - u / c
  have hbound : ∀ y (r : ℝ), f y = (r : WithTop ℝ) → (∑ v, p0 v * y v) - r ≤ c0 := by
    intro y r hyr
    have h1 := hgt y r (by simp [hyr])
    have hsum : ∑ v, p0 v * y v = (∑ v, a v * y v) / c := by
      dsimp [p0]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun v _ => div_mul_eq_mul_div _ _ _
    rw [hsum]
    dsimp [c0]
    have h2 : (∑ v, a v * y v) - c * r ≤ -u := by linarith
    have h3 := div_le_div_of_nonneg_right h2 hc_pos.le
    have h4 : ((∑ v, a v * y v) - c * r) / c = (∑ v, a v * y v) / c - r := by
      rw [sub_div, mul_div_cancel_left₀ _ hc_pos.ne']
    linarith
  exact ⟨p0, c0, cc_le hf.1 hbound, hbound⟩

lemma closed_proper_biconj {f : (V → ℝ) → WithTop ℝ} (hf : IsClosedProperConvex f) :
    ConvexConjugateRW (ConvexConjugateRW f) = f := by
  obtain ⟨p0, c0, hp0_le, hp0_bound⟩ := closed_proper_dom_conj hf
  have hdom_conj : (DomR (ConvexConjugateRW f)).Nonempty :=
    ⟨p0, ne_of_lt (hp0_le.trans_lt (WithTop.coe_lt_top c0))⟩
  funext x
  refine le_antisymm (biconj_le hdom_conj x) ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hs⟩ : ∃ s : ℝ, ConvexConjugateRW (ConvexConjugateRW f) x = (s : WithTop ℝ) := by
    induction h : ConvexConjugateRW (ConvexConjugateRW f) x using WithTop.recTopCoe with
    | top => exact absurd (h ▸ hlt) (not_lt_of_ge le_top)
    | coe s => exact ⟨s, rfl⟩
  rw [hs] at hlt
  have hnot : (x, s) ∉ EpiSet f := by
    simp only [EpiSet, Set.mem_setOf_eq, not_le]
    exact hlt
  obtain ⟨a, c, u, hc, hxs, hgt⟩ := sep_epiSet hf hnot
  rcases hc.lt_or_eq with hc_pos | hc_zero
  · let p : V → ℝ := fun v => a v / c
    let d : ℝ := - u / c
    have hbound : ∀ y (r : ℝ), f y = (r : WithTop ℝ) → (∑ v, p v * y v) - r ≤ d := by
      intro y r hyr
      have h1 := hgt y r (by simp [hyr])
      have hsum : ∑ v, p v * y v = (∑ v, a v * y v) / c := by
        dsimp [p]
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun v _ => div_mul_eq_mul_div _ _ _
      rw [hsum]
      dsimp [d]
      have h2 : (∑ v, a v * y v) - c * r ≤ -u := by linarith
      have h3 := div_le_div_of_nonneg_right h2 hc_pos.le
      have h4 : ((∑ v, a v * y v) - c * r) / c = (∑ v, a v * y v) / c - r := by
        rw [sub_div, mul_div_cancel_left₀ _ hc_pos.ne']
      linarith
    have hcc : ConvexConjugateRW f p ≤ (d : WithTop ℝ) := cc_le hf.1 hbound
    obtain ⟨cp, hcp⟩ := WithTop.ne_top_iff_exists.1
      (ne_of_lt (hcc.trans_lt (WithTop.coe_lt_top d)))
    have hcp_le : cp ≤ d := WithTop.coe_le_coe.1 (hcp ▸ hcc)
    have hge := cc_ge hcp.symm x
    rw [hs, WithTop.coe_le_coe] at hge
    have hsum_x : ∑ v, x v * p v = (∑ v, a v * x v) / c := by
      dsimp [p]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun v _ => by ring
    have hlt_x : d < (∑ v, a v * x v) / c - s := by
      dsimp [d]
      have h2 : -u < (∑ v, a v * x v) - c * s := by linarith
      have h3 := (div_lt_div_iff_of_pos_right hc_pos).2 h2
      have h4 : ((∑ v, a v * x v) - c * s) / c = (∑ v, a v * x v) / c - s := by
        rw [sub_div, mul_div_cancel_left₀ _ hc_pos.ne']
      linarith
    linarith
  · subst hc_zero
    simp only [zero_mul, add_zero] at hxs hgt
    have hpos : 0 < (∑ v, a v * x v) + u := by linarith
    let B0 : ℝ := (∑ v, p0 v * x v) - c0
    let t : ℝ := (|s - B0| + 1) / ((∑ v, a v * x v) + u)
    have ht_pos : 0 < t := div_pos (by positivity) hpos
    let pt : V → ℝ := fun v => p0 v + t * a v
    let dt : ℝ := c0 - t * u
    have hbound : ∀ y (r : ℝ), f y = (r : WithTop ℝ) → (∑ v, pt v * y v) - r ≤ dt := by
      intro y r hyr
      have h1 := hgt y r (by simp [hyr])
      have h2 := hp0_bound y r hyr
      have hsum : ∑ v, pt v * y v = (∑ v, p0 v * y v) + t * (∑ v, a v * y v) := by
        dsimp [pt]
        simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hsum]
      dsimp [dt]
      nlinarith
    have hcc : ConvexConjugateRW f pt ≤ (dt : WithTop ℝ) := cc_le hf.1 hbound
    obtain ⟨cp, hcp⟩ := WithTop.ne_top_iff_exists.1
      (ne_of_lt (hcc.trans_lt (WithTop.coe_lt_top dt)))
    have hcp_le : cp ≤ dt := WithTop.coe_le_coe.1 (hcp ▸ hcc)
    have hge := cc_ge hcp.symm x
    rw [hs, WithTop.coe_le_coe] at hge
    have hsum_x : (∑ v, x v * pt v) - dt = B0 + t * ((∑ v, a v * x v) + u) := by
      dsimp [pt, dt, B0]
      have h1 : ∑ v, x v * (p0 v + t * a v) = (∑ v, p0 v * x v) + t * (∑ v, a v * x v) := by
        have : ∀ v, x v * (p0 v + t * a v) = p0 v * x v + t * (a v * x v) := fun v => by ring
        simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [h1]
      ring
    have ht_eq : t * ((∑ v, a v * x v) + u) = |s - B0| + 1 :=
      div_mul_cancel₀ _ hpos.ne'
    have habs := le_abs_self (s - B0)
    linarith

lemma conj_lsc {f : (V → ℝ) → WithTop ℝ} (hne : (DomR f).Nonempty) :
    LowerSemicontinuous (ConvexConjugateRW f) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro C
  induction C using WithTop.recTopCoe with
  | top =>
    have : ConvexConjugateRW f ⁻¹' Set.Iic ⊤ = Set.univ := by
      ext p; simp
    rw [this]
    exact isClosed_univ
  | coe c =>
    have heq : ConvexConjugateRW f ⁻¹' Set.Iic (c : WithTop ℝ) =
        ⋂ (x : V → ℝ) (a : ℝ) (_ : f x = (a : WithTop ℝ)),
          {p : V → ℝ | (∑ v, p v * x v) - a ≤ c} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro hp x a hfx
        have h1 := (cc_ge hfx p).trans hp
        exact WithTop.coe_le_coe.1 h1
      · intro h
        exact cc_le hne h
    rw [heq]
    refine isClosed_iInter fun x => isClosed_iInter fun a => isClosed_iInter fun _ => ?_
    refine isClosed_le ?_ continuous_const
    refine Continuous.sub ?_ continuous_const
    exact continuous_finset_sum _ fun v _ => (continuous_apply v).mul continuous_const

lemma conj_convex {f : (V → ℝ) → WithTop ℝ} (hne : (DomR f).Nonempty) :
    IsConvexWithTop (ConvexConjugateRW f) := by
  intro p q t ht0 ht1
  by_cases ht_zero : t = 0
  · subst ht_zero
    have heq : (fun v => 0 * p v + (1 - 0) * q v) = q := by funext v; ring
    have hp0 : PosScalarMul 0 (ConvexConjugateRW f p) = 0 := by
      induction ConvexConjugateRW f p using WithTop.recTopCoe <;> simp [PosScalarMul]
    have hq1 : PosScalarMul (1 - 0) (ConvexConjugateRW f q) = ConvexConjugateRW f q := by
      induction ConvexConjugateRW f q using WithTop.recTopCoe <;> simp [PosScalarMul]
    rw [heq, hp0, hq1, zero_add]
  by_cases ht_one : t = 1
  · subst ht_one
    have heq : (fun v => 1 * p v + (1 - 1) * q v) = p := by funext v; ring
    have hp1 : PosScalarMul 1 (ConvexConjugateRW f p) = ConvexConjugateRW f p := by
      induction ConvexConjugateRW f p using WithTop.recTopCoe <;> simp [PosScalarMul]
    have hq0 : PosScalarMul (1 - 1) (ConvexConjugateRW f q) = 0 := by
      induction ConvexConjugateRW f q using WithTop.recTopCoe <;> simp [PosScalarMul]
    rw [heq, hp1, hq0, add_zero]
  have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
  have ht1_pos : 0 < 1 - t := by linarith [lt_of_le_of_ne ht1 ht_one]
  induction hcp : ConvexConjugateRW f p using WithTop.recTopCoe with
  | top =>
    simp only [PosScalarMul, if_neg ht_pos.ne', top_add, le_top]
  | coe cp =>
    induction hcq : ConvexConjugateRW f q using WithTop.recTopCoe with
    | top =>
      simp only [PosScalarMul, if_neg ht1_pos.ne', add_top, le_top]
    | coe cq =>
      simp only [PosScalarMul, ← WithTop.coe_add]
      refine cc_le hne fun x a hfx => ?_
      have hp := WithTop.coe_le_coe.1 (hcp ▸ cc_ge hfx p)
      have hq := WithTop.coe_le_coe.1 (hcq ▸ cc_ge hfx q)
      have hsum : ∑ i, (t * p i + (1 - t) * q i) * x i =
          t * (∑ i, p i * x i) + (1 - t) * (∑ i, q i * x i) := by
        have : ∀ i, (t * p i + (1 - t) * q i) * x i =
            t * (p i * x i) + (1 - t) * (q i * x i) := fun i => by ring
        simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hsum]
      nlinarith

lemma closed_proper_conj {f : (V → ℝ) → WithTop ℝ} (hf : IsClosedProperConvex f) :
    IsClosedProperConvex (ConvexConjugateRW f) := by
  obtain ⟨p0, c0, hp0, -⟩ := closed_proper_dom_conj hf
  refine ⟨⟨p0, ne_of_lt (hp0.trans_lt (WithTop.coe_lt_top c0))⟩,
    conj_lsc hf.1, conj_convex hf.1⟩

/-! ## Section 2: Backward direction (SBFR ∧ TRFR → MExchangeAxiomR of conjugate) -/

def rdot (p x : V → ℝ) : ℝ := ∑ i, p i * x i

lemma rdot_comm (p x : V → ℝ) : rdot p x = rdot x p :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma ind_sub (u v w : V) :
    (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ) =
      (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
  simp [IndicatorVec]

lemma rdot_ex_right (p x : V → ℝ) (u v : V) (α : ℝ) :
    rdot p (fun w => x w - α * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)) =
      rdot p x - α * (p u - p v) := by
  dsimp [rdot]
  have h0 : ∀ i : V, p i * (x i - α * (IndicatorVec ({u} : Finset V) i - IndicatorVec ({v} : Finset V) i : ℝ)) =
      p i * x i - α * (p i * (if i = u then (1 : ℝ) else 0) - p i * (if i = v then (1 : ℝ) else 0)) := by
    intro i; rw [ind_sub]; ring
  simp_rw [h0, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp

lemma rdot_ex_right_add (p y : V → ℝ) (u v : V) (α : ℝ) :
    rdot p (fun w => y w + α * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)) =
      rdot p y + α * (p u - p v) := by
  have := rdot_ex_right p y u v (-α)
  simpa [neg_mul, sub_neg_eq_add] using this

lemma conj_dom_sum {g : (V → ℝ) → WithTop ℝ} {r : ℝ}
    (hr : ∀ p : V → ℝ, ∀ α : ℝ, g (fun v => p v + α) = g p + (α * r : WithTop ℝ))
    (hne : (DomR g).Nonempty) {x : V → ℝ} (hx : ConvexConjugateRW g x ≠ ⊤) :
    ∑ i, x i = r := by
  by_contra hne_r
  obtain ⟨p0, hp0⟩ := hne
  obtain ⟨a0, ha0⟩ := WithTop.ne_top_iff_exists.1 hp0
  let s : ℝ := (∑ i, x i) - r
  have hs : s ≠ 0 := sub_ne_zero.2 hne_r
  let B0 : ℝ := (∑ i, x i * p0 i) - a0
  refine hx (cc_top_of_unbdd fun M => ?_)
  let α : ℝ := (M - B0) / s
  refine ⟨fun v => p0 v + α, a0 + α * r, ?_, ?_⟩
  · rw [hr p0 α, ← ha0, ← WithTop.coe_mul, ← WithTop.coe_add]
  · have hsum : (∑ i, x i * (p0 i + α)) - (a0 + α * r) = B0 + α * s := by
      dsimp [B0, s]
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring
    rw [hsum]
    have hαs : α * s = M - B0 := div_mul_cancel₀ _ hs
    linarith

noncomputable def rv (f : (V → ℝ) → WithTop ℝ) (x : V → ℝ) : ℝ :=
  if h : ∃ a : ℝ, f x = (a : WithTop ℝ) then h.choose else 0

lemma rv_spec {f : (V → ℝ) → WithTop ℝ} {x : V → ℝ} (hx : f x ≠ ⊤) :
    f x = ((rv f x : ℝ) : WithTop ℝ) := by
  have h : ∃ a : ℝ, f x = (a : WithTop ℝ) := by
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hx
    exact ⟨a, ha.symm⟩
  unfold rv
  rw [dif_pos h]
  exact h.choose_spec

lemma rv_of_eq {f : (V → ℝ) → WithTop ℝ} {x : V → ℝ} {a : ℝ} (h : f x = (a : WithTop ℝ)) :
    rv f x = a := by
  have hx : f x ≠ ⊤ := by rw [h]; exact WithTop.coe_ne_top
  have h2 := rv_spec hx
  rw [h] at h2
  exact WithTop.coe_injective h2.symm

noncomputable def gap (g : (V → ℝ) → WithTop ℝ) (x p : V → ℝ) : ℝ :=
  rv (ConvexConjugateRW g) x - (rdot x p - rv g p)

lemma gap_nonneg {g : (V → ℝ) → WithTop ℝ} {x p : V → ℝ}
    (hx : ConvexConjugateRW g x ≠ ⊤) (hp : g p ≠ ⊤) :
    0 ≤ gap g x p := by
  unfold gap
  have h1 := cc_bdd (rv_spec hx) (rv_spec hp)
  change rdot x p - rv g p ≤ rv (ConvexConjugateRW g) x at h1
  linarith

lemma gap_shift {g : (V → ℝ) → WithTop ℝ} {r : ℝ}
    (hr : ∀ p : V → ℝ, ∀ α : ℝ, g (fun v => p v + α) = g p + (α * r : WithTop ℝ))
    {x p : V → ℝ} (hsx : ∑ i, x i = r) (hp : g p ≠ ⊤) (α : ℝ) :
    g (fun v => p v + α) ≠ ⊤ ∧ gap g x (fun v => p v + α) = gap g x p := by
  have hgp : g (fun v => p v + α) = ((rv g p + α * r : ℝ) : WithTop ℝ) := by
    rw [hr p α, rv_spec hp, ← WithTop.coe_mul, ← WithTop.coe_add]
  refine ⟨by rw [hgp]; exact WithTop.coe_ne_top, ?_⟩
  unfold gap
  rw [rv_of_eq hgp]
  have hrdot : rdot x (fun v => p v + α) = rdot x p + α * r := by
    dsimp [rdot]
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsx, mul_comm r α]
  rw [hrdot]
  ring

lemma gap_convex {g : (V → ℝ) → WithTop ℝ} (hg : IsConvexWithTop g)
    {x p1 p2 : V → ℝ} (hp1 : g p1 ≠ ⊤) (hp2 : g p2 ≠ ⊤) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    g (fun v => (1 - t) * p1 v + t * p2 v) ≠ ⊤ ∧
      gap g x (fun v => (1 - t) * p1 v + t * p2 v) ≤ (1 - t) * gap g x p1 + t * gap g x p2 := by
  have hconv := hg p1 p2 (1 - t) (by linarith) (by linarith)
  have heq : (fun v => (1 - t) * p1 v + (1 - (1 - t)) * p2 v) =
      (fun v => (1 - t) * p1 v + t * p2 v) := by funext v; ring
  rw [heq] at hconv
  have hp1_le : PosScalarMul (1 - t) (g p1) ≤ (((1 - t) * rv g p1 : ℝ) : WithTop ℝ) :=
    psm_le_coe (by linarith) (rv_spec hp1).le
  have hp2_le : PosScalarMul (1 - (1 - t)) (g p2) ≤ ((t * rv g p2 : ℝ) : WithTop ℝ) := by
    have : 1 - (1 - t) = t := by ring
    rw [this]
    exact psm_le_coe ht0 (rv_spec hp2).le
  have hle : g (fun v => (1 - t) * p1 v + t * p2 v) ≤
      (((1 - t) * rv g p1 + t * rv g p2 : ℝ) : WithTop ℝ) :=
    hconv.trans ((add_le_add hp1_le hp2_le).trans (by rw [← WithTop.coe_add]))
  have hne : g (fun v => (1 - t) * p1 v + t * p2 v) ≠ ⊤ :=
    ne_of_lt (hle.trans_lt (WithTop.coe_lt_top _))
  refine ⟨hne, ?_⟩
  have hrv : rv g (fun v => (1 - t) * p1 v + t * p2 v) ≤ (1 - t) * rv g p1 + t * rv g p2 := by
    rw [rv_spec hne, WithTop.coe_le_coe] at hle
    exact hle
  unfold gap
  have hrdot : rdot x (fun v => (1 - t) * p1 v + t * p2 v) =
      (1 - t) * rdot x p1 + t * rdot x p2 := by
    dsimp [rdot]
    have : ∀ i, x i * ((1 - t) * p1 i + t * p2 i) =
        (1 - t) * (x i * p1 i) + t * (x i * p2 i) := fun i => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hrdot]
  linarith

lemma sbf_fin {g : (V → ℝ) → WithTop ℝ} (hs : SBFR g) {p q : V → ℝ}
    (hp : g p ≠ ⊤) (hq : g q ≠ ⊤) :
    g (p ⊔ q) ≠ ⊤ ∧ g (p ⊓ q) ≠ ⊤ ∧
      rv g (p ⊔ q) + rv g (p ⊓ q) ≤ rv g p + rv g q := by
  have h := hs p q
  rw [ge_iff_le, rv_spec hp, rv_spec hq, ← WithTop.coe_add] at h
  have h1 : g (p ⊔ q) ≠ ⊤ := by
    intro ht; rw [ht, top_add] at h; exact WithTop.coe_ne_top (top_le_iff.1 h)
  have h2 : g (p ⊓ q) ≠ ⊤ := by
    intro ht; rw [ht, add_top] at h; exact WithTop.coe_ne_top (top_le_iff.1 h)
  refine ⟨h1, h2, ?_⟩
  rw [rv_spec h1, rv_spec h2, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  exact h

lemma rdot_sup_inf (x p q : V → ℝ) :
    rdot x (p ⊔ q) + rdot x (p ⊓ q) = rdot x p + rdot x q := by
  dsimp [rdot]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change x i * (p i ⊔ q i) + x i * (p i ⊓ q i) = x i * p i + x i * q i
  rcases le_total (p i) (q i) with h | h
  · rw [sup_eq_right.2 h, inf_eq_left.2 h]; ring
  · rw [sup_eq_left.2 h, inf_eq_right.2 h]

lemma gap_sup_inf {g : (V → ℝ) → WithTop ℝ} (hs : SBFR g) {x p q : V → ℝ}
    (hp : g p ≠ ⊤) (hq : g q ≠ ⊤) :
    g (p ⊔ q) ≠ ⊤ ∧ g (p ⊓ q) ≠ ⊤ ∧
      gap g x (p ⊔ q) + gap g x (p ⊓ q) ≤ gap g x p + gap g x q := by
  obtain ⟨h1, h2, hle⟩ := sbf_fin hs hp hq
  refine ⟨h1, h2, ?_⟩
  unfold gap
  have hrd := rdot_sup_inf x p q
  linarith

lemma gap_sup' {g : (V → ℝ) → WithTop ℝ} (hs : SBFR g) {x : V → ℝ}
    (hx : ConvexConjugateRW g x ≠ ⊤) {S : Finset V} (hS : S.Nonempty)
    {P : V → V → ℝ} (hP : ∀ v ∈ S, g (P v) ≠ ⊤) :
    g (S.sup' hS P) ≠ ⊤ ∧ gap g x (S.sup' hS P) ≤ ∑ v ∈ S, gap g x (P v) := by
  induction S using Finset.cons_induction with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | cons a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs_ne
    · have h1 : (Finset.cons a ∅ ha).sup' hS P = P a := by simp
      have h2 : ∑ v ∈ Finset.cons a ∅ ha, gap g x (P v) = gap g x (P a) := by simp
      rw [h1, h2]
      exact ⟨hP a (Finset.mem_cons_self a _), le_rfl⟩
    · have hPa : g (P a) ≠ ⊤ := hP a (Finset.mem_cons_self a s)
      have hPs : ∀ v ∈ s, g (P v) ≠ ⊤ := fun v hv => hP v (Finset.mem_cons.2 (Or.inr hv))
      obtain ⟨hgs, hles⟩ := ih hs_ne hPs
      rw [Finset.sup'_cons hs_ne, Finset.sum_cons]
      obtain ⟨hsup, hinf, hgap⟩ := gap_sup_inf hs (x := x) hPa hgs
      have hnn := gap_nonneg hx hinf
      exact ⟨hsup, by linarith⟩

lemma gap_inf' {g : (V → ℝ) → WithTop ℝ} (hs : SBFR g) {y : V → ℝ}
    (hy : ConvexConjugateRW g y ≠ ⊤) {S : Finset V} (hS : S.Nonempty)
    {Q : V → V → ℝ} (hQ : ∀ v ∈ S, g (Q v) ≠ ⊤) :
    g (S.inf' hS Q) ≠ ⊤ ∧ gap g y (S.inf' hS Q) ≤ ∑ v ∈ S, gap g y (Q v) := by
  induction S using Finset.cons_induction with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | cons a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs_ne
    · have h1 : (Finset.cons a ∅ ha).inf' hS Q = Q a := by simp
      have h2 : ∑ v ∈ Finset.cons a ∅ ha, gap g y (Q v) = gap g y (Q a) := by simp
      rw [h1, h2]
      exact ⟨hQ a (Finset.mem_cons_self a _), le_rfl⟩
    · have hQa : g (Q a) ≠ ⊤ := hQ a (Finset.mem_cons_self a s)
      have hQs : ∀ v ∈ s, g (Q v) ≠ ⊤ := fun v hv => hQ v (Finset.mem_cons.2 (Or.inr hv))
      obtain ⟨hgs, hles⟩ := ih hs_ne hQs
      rw [Finset.inf'_cons hs_ne, Finset.sum_cons]
      obtain ⟨hsup, hinf, hgap⟩ := gap_sup_inf hs (x := y) hQa hgs
      have hnn := gap_nonneg hy hsup
      exact ⟨hinf, by linarith⟩

lemma mono_ineq_gap {g : (V → ℝ) → WithTop ℝ} (hs : SBFR g) {x y P Q : V → ℝ}
    (hx : ConvexConjugateRW g x ≠ ⊤) (hy : ConvexConjugateRW g y ≠ ⊤)
    (hP : g P ≠ ⊤) (hQ : g Q ≠ ⊤) :
    ∑ w : V, (x w - y w) * max (Q w - P w) 0 ≤ gap g x P + gap g y Q := by
  obtain ⟨hsup, hinf, hle⟩ := sbf_fin hs hP hQ
  have h1 := gap_nonneg hx hsup
  have h2 := gap_nonneg hy hinf
  unfold gap at h1 h2 ⊢
  have heq : ∑ w : V, (x w - y w) * max (Q w - P w) 0 =
      (rdot x (P ⊔ Q) - rdot x P) + (rdot y (P ⊓ Q) - rdot y Q) := by
    dsimp [rdot]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    change (x w - y w) * max (Q w - P w) 0 =
      (x w * (P w ⊔ Q w) - x w * P w) + (y w * (P w ⊓ Q w) - y w * Q w)
    rcases le_total (P w) (Q w) with h | h
    · rw [sup_eq_right.2 h, inf_eq_left.2 h, max_eq_left (by linarith)]; ring
    · rw [sup_eq_left.2 h, inf_eq_right.2 h, max_eq_right (by linarith)]; ring
  linarith

set_option maxHeartbeats 800000 in
theorem lconv_mexc {g : (V → ℝ) → WithTop ℝ} (hg : IsClosedProperConvex g)
    (hs : SBFR g) (ht : TRFR g) :
    MExchangeAxiomR (ConvexConjugateRW g) := by
  intro x hx y hy u hu
  have hx' : ConvexConjugateRW g x ≠ ⊤ := hx
  have hy' : ConvexConjugateRW g y ≠ ⊤ := hy
  obtain ⟨r, hr⟩ := ht
  have hsx : ∑ i, x i = r := conj_dom_sum hr hg.1 hx'
  have hsy : ∑ i, y i = r := conj_dom_sum hr hg.1 hy'
  have hxu : y u < x u := hu
  let N : Finset V := Finset.univ.filter (fun w => x w < y w)
  have hN : N.Nonempty := by
    by_contra hN_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hN_empty
    have hall : ∀ w : V, y w ≤ x w := fun w => by
      by_contra hlt
      push_neg at hlt
      have hw : w ∈ N := Finset.mem_filter.2 ⟨Finset.mem_univ w, hlt⟩
      rw [hN_empty] at hw
      exact Finset.notMem_empty w hw
    have hlt_sum : ∑ w, y w < ∑ w, x w :=
      Finset.sum_lt_sum (fun w _ => hall w) ⟨u, Finset.mem_univ u, hxu⟩
    linarith
  -- Sufficient condition for a candidate v ∈ N and α0 > 0:
  have h_suff : ∀ v ∈ N, ∀ α0 : ℝ, 0 < α0 →
      (∀ p q : V → ℝ, g p ≠ ⊤ → g q ≠ ⊤ →
        α0 * ((p v - p u) - (q v - q u)) ≤ gap g x p + gap g y q) →
      ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
        ConvexConjugateRW g x + ConvexConjugateRW g y ≥
          ConvexConjugateRW g (fun w => x w - α * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)) +
            ConvexConjugateRW g (fun w => y w + α * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)) := by
    intro v hv α0 hα0 hbound α hα_nn hα_le
    set x' : V → ℝ := fun w => x w - α * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)
    set y' : V → ℝ := fun w => y w + α * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)
    have key : ∀ p q : V → ℝ, ∀ a b : ℝ, g p = (a : WithTop ℝ) → g q = (b : WithTop ℝ) →
        ((∑ i, x' i * p i) - a) + ((∑ i, y' i * q i) - b) ≤
          rv (ConvexConjugateRW g) x + rv (ConvexConjugateRW g) y := by
      intro p q a b hp hq
      have hp_ne : g p ≠ ⊤ := by rw [hp]; exact WithTop.coe_ne_top
      have hq_ne : g q ≠ ⊤ := by rw [hq]; exact WithTop.coe_ne_top
      have hb1 := hbound p q hp_ne hq_ne
      have hb0 : 0 ≤ gap g x p + gap g y q := add_nonneg (gap_nonneg hx' hp_ne) (gap_nonneg hy' hq_ne)
      have hbα : α * ((p v - p u) - (q v - q u)) ≤ gap g x p + gap g y q := by
        rcases le_total ((p v - p u) - (q v - q u)) 0 with hneg | hpos
        · exact (mul_nonpos_of_nonneg_of_nonpos hα_nn hneg).trans hb0
        · exact (mul_le_mul_of_nonneg_right hα_le hpos).trans hb1
      unfold gap at hbα
      rw [rv_of_eq hp, rv_of_eq hq] at hbα
      have hx'p : ∑ i, x' i * p i = rdot x p + α * (p v - p u) := by
        change rdot x' p = rdot x p + α * (p v - p u)
        rw [← rdot_comm p x', rdot_ex_right p x u v α, rdot_comm p x]; ring
      have hy'q : ∑ i, y' i * q i = rdot y q - α * (q v - q u) := by
        change rdot y' q = rdot y q - α * (q v - q u)
        rw [← rdot_comm q y', rdot_ex_right_add q y u v α, rdot_comm q y]; ring
      rw [hx'p, hy'q]
      linarith
    obtain ⟨p0, hp0⟩ := hg.1
    obtain ⟨a0, ha0⟩ := WithTop.ne_top_iff_exists.1 hp0
    have hx'_le : ConvexConjugateRW g x' ≤
        ((rv (ConvexConjugateRW g) x + rv (ConvexConjugateRW g) y - ((∑ i, y' i * p0 i) - a0) : ℝ) : WithTop ℝ) :=
      cc_le hg.1 fun p a hp => by linarith [key p p0 a a0 hp ha0.symm]
    have hx'_ne : ConvexConjugateRW g x' ≠ ⊤ :=
      ne_of_lt (hx'_le.trans_lt (WithTop.coe_lt_top _))
    have hy'_le : ConvexConjugateRW g y' ≤
        ((rv (ConvexConjugateRW g) x + rv (ConvexConjugateRW g) y - rv (ConvexConjugateRW g) x' : ℝ) : WithTop ℝ) := by
      refine cc_le hg.1 fun q b hq => ?_
      have hx'_bdd : ConvexConjugateRW g x' ≤
          ((rv (ConvexConjugateRW g) x + rv (ConvexConjugateRW g) y - ((∑ i, y' i * q i) - b) : ℝ) : WithTop ℝ) :=
        cc_le hg.1 fun p a hp => by linarith [key p q a b hp hq]
      rw [rv_spec hx'_ne, WithTop.coe_le_coe] at hx'_bdd
      linarith
    rw [ge_iff_le, rv_spec hx', rv_spec hy', rv_spec hx'_ne]
    refine (add_le_add le_rfl hy'_le).trans ?_
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
    linarith
  -- Now prove by contradiction that some v ∈ N and α0 > 0 satisfy the sufficient condition
  by_contra h_contra
  have h_fail : ∀ v ∈ N, ∀ α0 : ℝ, 0 < α0 →
      ∃ p q : V → ℝ, g p ≠ ⊤ ∧ g q ≠ ⊤ ∧
        gap g x p + gap g y q < α0 * ((p v - p u) - (q v - q u)) := by
    intro v hv α0 hα0
    by_contra h_ok
    push_neg at h_ok
    exact h_contra ⟨v, (Finset.mem_filter.1 hv).2, α0, hα0, h_suff v hv α0 hα0 h_ok⟩
  -- Step A: α1 = (x u - y u) / (2 * N.card + 1)
  let α1 : ℝ := (x u - y u) / (2 * (N.card : ℝ) + 1)
  have hα1_pos : 0 < α1 := div_pos (sub_pos.2 hxu) (by positivity)
  choose! p1 q1 hp1 hq1 hlt1 using fun v hv => h_fail v hv α1 hα1_pos
  let T : V → ℝ := fun v => (p1 v v - p1 v u) - (q1 v v - q1 v u)
  have hT_pos : ∀ v ∈ N, 0 < T v := by
    intro v hv
    have hnn : 0 ≤ gap g x (p1 v) + gap g y (q1 v) :=
      add_nonneg (gap_nonneg hx' (hp1 v hv)) (gap_nonneg hy' (hq1 v hv))
    have hlt := hlt1 v hv
    exact pos_of_mul_pos_right (hnn.trans_lt hlt) hα1_pos.le
  -- Step B: t = min_{v ∈ N} T v > 0
  let t : ℝ := N.inf' hN T
  have ht_pos : 0 < t := (Finset.lt_inf'_iff hN).2 hT_pos
  have ht_le : ∀ v ∈ N, t ≤ T v := fun v hv => Finset.inf'_le T hv
  -- Step C: δ = (α1 * t) / 2, pick p0, q0 with gap < δ/2 each
  let δ : ℝ := (α1 * t) / 2
  have hδ_pos : 0 < δ := half_pos (mul_pos hα1_pos ht_pos)
  obtain ⟨p0, a0, hp0_eq, hp0_gt⟩ := cc_exists_gt (rv_spec hx') (half_pos hδ_pos)
  obtain ⟨q0, b0, hq0_eq, hq0_gt⟩ := cc_exists_gt (rv_spec hy') (half_pos hδ_pos)
  have hp0_ne : g p0 ≠ ⊤ := by rw [hp0_eq]; exact WithTop.coe_ne_top
  have hq0_ne : g q0 ≠ ⊤ := by rw [hq0_eq]; exact WithTop.coe_ne_top
  have hgap0 : gap g x p0 + gap g y q0 < δ := by
    unfold gap rdot
    rw [rv_of_eq hp0_eq, rv_of_eq hq0_eq]
    linarith
  let D0 : V → ℝ := fun v => (p0 v - p0 u) - (q0 v - q0 u)
  let C : ℝ := (∑ v ∈ N, |D0 v|) + 1
  have hC_pos : 0 < C := by
    have : 0 ≤ ∑ v ∈ N, |D0 v| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hD0_ge : ∀ v ∈ N, -C ≤ D0 v := by
    intro v hv
    have h1 : |D0 v| ≤ ∑ w ∈ N, |D0 w| :=
      Finset.single_le_sum (fun w _ => abs_nonneg (D0 w)) hv
    have h2 := neg_abs_le (D0 v)
    dsimp [C]; linarith
  -- Step D: α2 = δ / C
  let α2 : ℝ := δ / C
  have hα2_pos : 0 < α2 := div_pos hδ_pos hC_pos
  choose! p2 q2 hp2 hq2 hlt2 using fun v hv => h_fail v hv α2 hα2_pos
  let S : V → ℝ := fun v => (p2 v v - p2 v u) - (q2 v v - q2 v u)
  have hS_pos : ∀ v ∈ N, 0 < S v := by
    intro v hv
    have hnn : 0 ≤ gap g x (p2 v) + gap g y (q2 v) :=
      add_nonneg (gap_nonneg hx' (hp2 v hv)) (gap_nonneg hy' (hq2 v hv))
    exact pos_of_mul_pos_right (hnn.trans_lt (hlt2 v hv)) hα2_pos.le
  -- Step E: First convex combination p', q'
  let lam : V → ℝ := fun v => C / (S v + C)
  let p' : V → V → ℝ := fun v w => (1 - lam v) * p0 w + lam v * p2 v w
  let q' : V → V → ℝ := fun v w => (1 - lam v) * q0 w + lam v * q2 v w
  have hp'_Step : ∀ v ∈ N, g (p' v) ≠ ⊤ ∧ g (q' v) ≠ ⊤ ∧
      0 ≤ (p' v v - p' v u) - (q' v v - q' v u) ∧
      gap g x (p' v) + gap g y (q' v) < α1 * t := by
    intro v hv
    have hSv : 0 < S v := hS_pos v hv
    have hden : 0 < S v + C := by linarith
    have hlam0 : 0 ≤ lam v := div_nonneg hC_pos.le hden.le
    have hlam1 : lam v ≤ 1 := (div_le_one hden).2 (by linarith)
    have h1m : 1 - lam v = S v / (S v + C) := by
      dsimp [lam]; rw [sub_div' hden.ne']; ring_nf
    obtain ⟨hp'_ne, hgap_p'⟩ := gap_convex hg.2.2 (x := x) hp0_ne (hp2 v hv) hlam0 hlam1
    obtain ⟨hq'_ne, hgap_q'⟩ := gap_convex hg.2.2 (x := y) hq0_ne (hq2 v hv) hlam0 hlam1
    refine ⟨hp'_ne, hq'_ne, ?_, ?_⟩
    · have hD' : (p' v v - p' v u) - (q' v v - q' v u) =
          (1 - lam v) * D0 v + lam v * S v := by
        dsimp [p', q', D0, S]; ring
      rw [hD', h1m]
      dsimp [lam]
      have hge : -(S v * C) ≤ S v * D0 v := by
        have := mul_le_mul_of_nonneg_left (hD0_ge v hv) hSv.le
        linarith
      have hsum_num : S v / (S v + C) * D0 v + C / (S v + C) * S v =
          (S v * D0 v + C * S v) / (S v + C) := by ring
      rw [hsum_num]
      exact div_nonneg (by linarith) hden.le
    · have hlt_v := hlt2 v hv
      have h1m_le : 1 - lam v ≤ 1 := by linarith
      have h1m_nn : 0 ≤ 1 - lam v := by linarith
      have hnn0 : 0 ≤ gap g x p0 + gap g y q0 :=
        add_nonneg (gap_nonneg hx' hp0_ne) (gap_nonneg hy' hq0_ne)
      have hterm1 : (1 - lam v) * (gap g x p0 + gap g y q0) < δ :=
        calc (1 - lam v) * (gap g x p0 + gap g y q0)
            ≤ 1 * (gap g x p0 + gap g y q0) := mul_le_mul_of_nonneg_right h1m_le hnn0
          _ = gap g x p0 + gap g y q0 := one_mul _
          _ < δ := hgap0
      have hterm2 : lam v * (gap g x (p2 v) + gap g y (q2 v)) < δ := by
        have hmul : lam v * (gap g x (p2 v) + gap g y (q2 v)) < lam v * (α2 * S v) :=
          mul_lt_mul_of_pos_left hlt_v (div_pos hC_pos hden)
        have hle2 : lam v * (α2 * S v) ≤ δ := by
          dsimp [lam, α2]
          have h3 : C / (S v + C) * (δ / C * S v) = δ * (S v / (S v + C)) := by
            field_simp [hC_pos.ne', hden.ne']
          rw [h3]
          have h4 : S v / (S v + C) ≤ 1 := (div_le_one hden).2 (by linarith)
          calc δ * (S v / (S v + C)) ≤ δ * 1 := mul_le_mul_of_nonneg_left h4 hδ_pos.le
            _ = δ := mul_one _
        linarith
      have h2δ : 2 * δ = α1 * t := by dsimp [δ]; ring
      linarith
  -- Step F: Second convex combination pv, qv, then shift so pv v u = 0, qv v u = 0
  let mu : V → ℝ := fun v => t / T v
  let pv0 : V → V → ℝ := fun v w => (1 - mu v) * p' v w + mu v * p1 v w
  let qv0 : V → V → ℝ := fun v w => (1 - mu v) * q' v w + mu v * q1 v w
  let pv : V → V → ℝ := fun v w => pv0 v w + (- pv0 v u)
  let qv : V → V → ℝ := fun v w => qv0 v w + (- qv0 v u)
  have hpv_Step : ∀ v ∈ N, g (pv v) ≠ ⊤ ∧ g (qv v) ≠ ⊤ ∧
      pv v u = 0 ∧ qv v u = 0 ∧ t ≤ pv v v - qv v v ∧
      gap g x (pv v) + gap g y (qv v) < 2 * α1 * t := by
    intro v hv
    obtain ⟨hp'_ne, hq'_ne, hD'_nn, hgap'_lt⟩ := hp'_Step v hv
    have hTv : 0 < T v := hT_pos v hv
    have hmu0 : 0 ≤ mu v := div_nonneg ht_pos.le hTv.le
    have hmu1 : mu v ≤ 1 := (div_le_one hTv).2 (ht_le v hv)
    obtain ⟨hpv0_ne, hgap_pv0⟩ := gap_convex hg.2.2 (x := x) hp'_ne (hp1 v hv) hmu0 hmu1
    obtain ⟨hqv0_ne, hgap_qv0⟩ := gap_convex hg.2.2 (x := y) hq'_ne (hq1 v hv) hmu0 hmu1
    obtain ⟨hpv_ne, hgap_pv⟩ := gap_shift hr hsx hpv0_ne (- pv0 v u)
    obtain ⟨hqv_ne, hgap_qv⟩ := gap_shift hr hsy hqv0_ne (- qv0 v u)
    refine ⟨hpv_ne, hqv_ne, by simp [pv], by simp [qv], ?_, ?_⟩
    · have hdiff : pv v v - qv v v =
          (1 - mu v) * ((p' v v - p' v u) - (q' v v - q' v u)) + mu v * T v := by
        dsimp [pv, qv, pv0, qv0, T]; ring
      rw [hdiff]
      have hmuT : mu v * T v = t := div_mul_cancel₀ t hTv.ne'
      have h1m_nn : 0 ≤ 1 - mu v := by linarith
      have hprod_nn : 0 ≤ (1 - mu v) * ((p' v v - p' v u) - (q' v v - q' v u)) :=
        mul_nonneg h1m_nn hD'_nn
      linarith
    · rw [hgap_pv, hgap_qv]
      have hlt_v := hlt1 v hv
      have hmu_pos : 0 < mu v := div_pos ht_pos hTv
      have hterm2 : mu v * (gap g x (p1 v) + gap g y (q1 v)) < α1 * t := by
        have hmul := mul_lt_mul_of_pos_left hlt_v hmu_pos
        have heq : mu v * (α1 * T v) = α1 * (mu v * T v) := by ring
        rw [heq, div_mul_cancel₀ t hTv.ne'] at hmul
        exact hmul
      have hterm1 : (1 - mu v) * (gap g x (p' v) + gap g y (q' v)) ≤ α1 * t := by
        have h1m_le : 1 - mu v ≤ 1 := by linarith
        have hnn : 0 ≤ gap g x (p' v) + gap g y (q' v) :=
          add_nonneg (gap_nonneg hx' hp'_ne) (gap_nonneg hy' hq'_ne)
        calc (1 - mu v) * (gap g x (p' v) + gap g y (q' v))
            ≤ 1 * (gap g x (p' v) + gap g y (q' v)) := mul_le_mul_of_nonneg_right h1m_le hnn
          _ = gap g x (p' v) + gap g y (q' v) := one_mul _
          _ ≤ α1 * t := hgap'_lt.le
      linarith
  -- Step G: Aggregate P = N.sup' pv and Q = N.inf' qv
  obtain ⟨hP_ne, hgap_P⟩ := gap_sup' hs hx' hN (fun v hv => (hpv_Step v hv).1)
  obtain ⟨hQ_ne, hgap_Q⟩ := gap_inf' hs hy' hN (fun v hv => (hpv_Step v hv).2.1)
  let P : V → ℝ := N.sup' hN pv
  let Q : V → ℝ := N.inf' hN qv
  have hPu : P u = 0 := by
    dsimp [P]
    rw [Finset.sup'_apply]
    apply le_antisymm
    · exact Finset.sup'_le hN _ fun v hv => (hpv_Step v hv).2.2.1.le
    · obtain ⟨v0, hv0⟩ := hN
      exact (hpv_Step v0 hv0).2.2.1.symm.le.trans (Finset.le_sup' (fun v => pv v u) hv0)
  have hQu : Q u = 0 := by
    dsimp [Q]
    rw [Finset.inf'_apply]
    apply le_antisymm
    · obtain ⟨v0, hv0⟩ := hN
      exact (Finset.inf'_le (fun v => qv v u) hv0).trans (hpv_Step v0 hv0).2.2.2.1.le
    · exact Finset.le_inf' hN _ fun v hv => (hpv_Step v hv).2.2.2.1.symm.le
  have hPQ_diff : ∀ w ∈ N, Q w - P w + t ≤ 0 := by
    intro w hw
    have hPw : pv w w ≤ P w := by
      dsimp [P]; rw [Finset.sup'_apply]; exact Finset.le_sup' (fun v => pv v w) hw
    have hQw : Q w ≤ qv w w := by
      dsimp [Q]; rw [Finset.inf'_apply]; exact Finset.inf'_le (fun v => qv v w) hw
    have htw := (hpv_Step w hw).2.2.2.2.1
    linarith
  obtain ⟨hQt_ne, hgap_Qt⟩ := gap_shift hr hsy hQ_ne t
  have hmono := mono_ineq_gap hs hx' hy' hP_ne hQt_ne
  rw [hgap_Qt] at hmono
  have hterm_nn : ∀ z : V, 0 ≤ (x z - y z) * max ((Q z + t) - P z) 0 := by
    intro z
    by_cases hz : z ∈ N
    · have hle : Q z + t - P z ≤ 0 := by linarith [hPQ_diff z hz]
      rw [max_eq_right hle, mul_zero]
    · have hge : y z ≤ x z := by
        by_contra hlt
        push_neg at hlt
        exact hz (Finset.mem_filter.2 ⟨Finset.mem_univ z, hlt⟩)
      exact mul_nonneg (sub_nonneg.2 hge) (le_max_right _ _)
  have hterm_u : (x u - y u) * t ≤ ∑ z : V, (x z - y z) * max ((Q z + t) - P z) 0 := by
    have h1 := Finset.single_le_sum (fun z _ => hterm_nn z) (Finset.mem_univ u)
    rw [hPu, hQu, sub_zero, zero_add, max_eq_left ht_pos.le] at h1
    exact h1
  have hsum_lt : gap g x P + gap g y Q < (x u - y u) * t := by
    have h1 : gap g x P + gap g y Q ≤ ∑ v ∈ N, (gap g x (pv v) + gap g y (qv v)) := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hgap_P hgap_Q
    have h2 : ∑ v ∈ N, (gap g x (pv v) + gap g y (qv v)) < ∑ _v ∈ N, (2 * α1 * t) :=
      Finset.sum_lt_sum_of_nonempty hN fun v hv => (hpv_Step v hv).2.2.2.2.2
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (N.card : ℝ) * (2 * α1 * t) < (x u - y u) * t := by
      dsimp [α1]
      have hden : 0 < 2 * (N.card : ℝ) + 1 := by positivity
      have hlt_frac : 2 * (N.card : ℝ) / (2 * (N.card : ℝ) + 1) < 1 :=
        (div_lt_one hden).2 (by linarith)
      have heq : (N.card : ℝ) * (2 * ((x u - y u) / (2 * (N.card : ℝ) + 1)) * t) =
          (2 * (N.card : ℝ) / (2 * (N.card : ℝ) + 1)) * ((x u - y u) * t) := by ring
      rw [heq]
      linarith [mul_lt_mul_of_pos_right hlt_frac (mul_pos (sub_pos.2 hxu) ht_pos)]
    linarith
  linarith

/-! ## Section 3: Forward direction (MExchangeAxiomR → SBFR ∧ TRFR of conjugate) -/

lemma sum_sublevel_isClosed {f1 f2 : (V → ℝ) → WithTop ℝ}
    (h1 : LowerSemicontinuous f1) (h2 : LowerSemicontinuous f2) (C : ℝ) :
    IsClosed {p : (V → ℝ) × (V → ℝ) | f1 p.1 + f2 p.2 ≤ (C : WithTop ℝ)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨z1, z2⟩ hz
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hz
  obtain ⟨c1, c2, hc_sum, hc1, hc2⟩ :
      ∃ c1 c2 : ℝ, C ≤ c1 + c2 ∧ ((c1 : ℝ) : WithTop ℝ) < f1 z1 ∧ ((c2 : ℝ) : WithTop ℝ) < f2 z2 := by
    induction hf1 : f1 z1 using WithTop.recTopCoe with
    | top =>
      induction hf2 : f2 z2 using WithTop.recTopCoe with
      | top => exact ⟨C, 0, by linarith, WithTop.coe_lt_top _, WithTop.coe_lt_top _⟩
      | coe b =>
        exact ⟨C - b + 1, b - 1, by linarith, WithTop.coe_lt_top _, by rw [WithTop.coe_lt_coe]; linarith⟩
    | coe a =>
      induction hf2 : f2 z2 using WithTop.recTopCoe with
      | top =>
        exact ⟨a - 1, C - a + 1, by linarith, by rw [WithTop.coe_lt_coe]; linarith, WithTop.coe_lt_top _⟩
      | coe b =>
        rw [hf1, hf2, ← WithTop.coe_add, WithTop.coe_lt_coe] at hz
        let δ := (a + b - C) / 2
        refine ⟨a - δ, b - δ, by dsimp [δ]; linarith, ?_, ?_⟩ <;>
        · rw [WithTop.coe_lt_coe]; dsimp [δ]; linarith
  refine ⟨{z | ((c1 : ℝ) : WithTop ℝ) < f1 z} ×ˢ {z | ((c2 : ℝ) : WithTop ℝ) < f2 z}, ?_,
    (h1.isOpen_preimage (c1 : WithTop ℝ)).prod (h2.isOpen_preimage (c2 : WithTop ℝ)), ⟨hc1, hc2⟩⟩
  rintro ⟨w1, w2⟩ ⟨hw1, hw2⟩
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  calc (C : WithTop ℝ) ≤ ((c1 + c2 : ℝ) : WithTop ℝ) := WithTop.coe_le_coe.2 hc_sum
    _ = (c1 : WithTop ℝ) + (c2 : WithTop ℝ) := WithTop.coe_add c1 c2
    _ < f1 w1 + f2 w2 := WithTop.add_lt_add hw1 hw2

lemma sum_ex_sub (x : V → ℝ) (u v : V) (t : ℝ) :
    (∑ w : V, (x w - t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ))) =
      ∑ w : V, x w := by
  have h := rdot_ex_right (fun _ => 1) x u v t
  simpa [rdot] using h

lemma sum_ex_add (y : V → ℝ) (u v : V) (t : ℝ) :
    (∑ w : V, (y w + t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ))) =
      ∑ w : V, y w := by
  have h := rdot_ex_right_add (fun _ => 1) y u v t
  simpa [rdot] using h

lemma step_in_box {lo hi z1 z2 : V → ℝ} {u v : V} (huv : u ≠ v)
    (hz1 : z1 ∈ Set.Icc lo hi) (hz2 : z2 ∈ Set.Icc lo hi)
    {t : ℝ} (ht0 : 0 ≤ t)
    (htu : 2 * t ≤ z1 u - z2 u) (htv : 2 * t ≤ z2 v - z1 v) :
    (fun w => z1 w - t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)) ∈ Set.Icc lo hi ∧
    (fun w => z2 w + t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)) ∈ Set.Icc lo hi ∧
    (∑ w : V, |(z1 w - t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)) -
        (z2 w + t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ))|) =
      (∑ w : V, |z1 w - z2 w|) - 4 * t := by
  set z1' : V → ℝ := fun w => z1 w - t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)
  set z2' : V → ℝ := fun w => z2 w + t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)
  have hz1' : z1' ∈ Set.Icc lo hi := by
    constructor <;> intro w <;> dsimp [z1'] <;> rw [ind_sub]
    · by_cases hwu : w = u
      · subst hwu; simp only [if_true, if_neg huv, sub_zero, mul_one]; linarith [hz2.1 w]
      · by_cases hwv : w = v
        · subst hwv; simp only [if_neg huv.symm, if_true, zero_sub, mul_neg, mul_one, sub_neg_eq_add]; linarith [hz1.1 w]
        · simp only [if_neg hwu, if_neg hwv, sub_zero, mul_zero]; exact hz1.1 w
    · by_cases hwu : w = u
      · subst hwu; simp only [if_true, if_neg huv, sub_zero, mul_one]; linarith [hz1.2 w]
      · by_cases hwv : w = v
        · subst hwv; simp only [if_neg huv.symm, if_true, zero_sub, mul_neg, mul_one, sub_neg_eq_add]; linarith [hz2.2 w]
        · simp only [if_neg hwu, if_neg hwv, sub_zero, mul_zero]; exact hz1.2 w
  have hz2' : z2' ∈ Set.Icc lo hi := by
    constructor <;> intro w <;> dsimp [z2'] <;> rw [ind_sub]
    · by_cases hwu : w = u
      · subst hwu; simp only [if_true, if_neg huv, sub_zero, mul_one]; linarith [hz2.1 w]
      · by_cases hwv : w = v
        · subst hwv; simp only [if_neg huv.symm, if_true, zero_sub, mul_neg, mul_one, ← sub_eq_add_neg]; linarith [hz1.1 w]
        · simp only [if_neg hwu, if_neg hwv, sub_zero, mul_zero, add_zero]; exact hz2.1 w
    · by_cases hwu : w = u
      · subst hwu; simp only [if_true, if_neg huv, sub_zero, mul_one]; linarith [hz1.2 w]
      · by_cases hwv : w = v
        · subst hwv; simp only [if_neg huv.symm, if_true, zero_sub, mul_neg, mul_one, ← sub_eq_add_neg]; linarith [hz2.2 w]
        · simp only [if_neg hwu, if_neg hwv, sub_zero, mul_zero, add_zero]; exact hz2.2 w
  refine ⟨hz1', hz2', ?_⟩
  have hpt : ∀ w : V, |z1' w - z2' w| =
      |z1 w - z2 w| - (if w = u then 2 * t else 0) - (if w = v then 2 * t else 0) := by
    intro w
    dsimp [z1', z2']
    rw [ind_sub]
    by_cases hwu : w = u
    · subst hwu
      simp only [if_true, if_neg huv, sub_zero, mul_one]
      have h1 : |(z1 w - t) - (z2 w + t)| = (z1 w - z2 w) - 2 * t := by
        rw [show (z1 w - t) - (z2 w + t) = (z1 w - z2 w) - 2 * t by ring]
        exact abs_of_nonneg (by linarith)
      have h2 : |z1 w - z2 w| = z1 w - z2 w := abs_of_nonneg (by linarith)
      linarith
    · by_cases hwv : w = v
      · subst hwv
        simp only [if_neg huv.symm, if_true, zero_sub, mul_neg, mul_one]
        have h1 : |(z1 w - -(t)) - (z2 w + -(t))| = (z2 w - z1 w) - 2 * t := by
          rw [show (z1 w - -t) - (z2 w + -t) = -((z2 w - z1 w) - 2 * t) by ring, abs_neg]
          exact abs_of_nonneg (by linarith)
        have h2 : |z1 w - z2 w| = z2 w - z1 w := by
          rw [← abs_neg, neg_sub]
          exact abs_of_nonneg (by linarith)
        linarith
      · simp only [if_neg hwu, if_neg hwv, sub_zero, mul_zero, add_zero]
  change (∑ w : V, |z1' w - z2' w|) = (∑ w : V, |z1 w - z2 w|) - 4 * t
  simp_rw [hpt, Finset.sum_sub_distrib]
  have hu_sum : (∑ w : V, if w = u then 2 * t else 0) = 2 * t := by simp
  have hv_sum : (∑ w : V, if w = v then 2 * t else 0) = 2 * t := by simp
  rw [hu_sum, hv_sum]
  ring

lemma sum_const_R {f : (V → ℝ) → WithTop ℝ} (hlsc : LowerSemicontinuous f)
    (hm : MExchangeAxiomR f) {x y : V → ℝ} (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) :
    ∑ w : V, x w = ∑ w : V, y w := by
  let lo : V → ℝ := x ⊓ y
  let hi : V → ℝ := x ⊔ y
  let C : ℝ := rv f x + rv f y
  let K : Set ((V → ℝ) × (V → ℝ)) :=
    (Set.Icc lo hi ×ˢ Set.Icc lo hi) ∩
      ({p | ∑ w, p.1 w = ∑ w, x w} ∩
        ({p | ∑ w, p.2 w = ∑ w, y w} ∩
          {p | f p.1 + f p.2 ≤ (C : WithTop ℝ)}))
  have hK_compact : IsCompact K := by
    refine (isCompact_Icc.prod isCompact_Icc).inter_right ?_
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (sum_sublevel_isClosed hlsc hlsc C))
    · exact isClosed_eq (continuous_finset_sum _ fun w _ => (continuous_apply w).comp continuous_fst) continuous_const
    · exact isClosed_eq (continuous_finset_sum _ fun w _ => (continuous_apply w).comp continuous_snd) continuous_const
  have hxy_mem : (x, y) ∈ K := by
    refine ⟨⟨⟨inf_le_left, le_sup_left⟩, ⟨inf_le_right, le_sup_right⟩⟩, rfl, rfl, ?_⟩
    simp only [Set.mem_setOf_eq, C, ← rv_spec hx, ← rv_spec hy, WithTop.coe_add, le_rfl]
  let φ : (V → ℝ) × (V → ℝ) → ℝ := fun p => ∑ w : V, |p.1 w - p.2 w|
  have hφ_cont : Continuous φ :=
    continuous_finset_sum _ fun w _ =>
      ((continuous_apply w).comp continuous_fst).sub ((continuous_apply w).comp continuous_snd) |>.abs
  obtain ⟨⟨z1, z2⟩, hz_mem, hz_min⟩ := hK_compact.exists_isMinOn ⟨(x, y), hxy_mem⟩ hφ_cont.continuousOn
  rcases hz_mem with ⟨⟨hz1_box, hz2_box⟩, hz1_sum, hz2_sum, hz_val⟩
  change ∑ w, z1 w = ∑ w, x w at hz1_sum
  change ∑ w, z2 w = ∑ w, y w at hz2_sum
  change f z1 + f z2 ≤ (C : WithTop ℝ) at hz_val
  have hz1_dom : f z1 ≠ ⊤ := by
    intro htop; rw [htop, top_add] at hz_val; exact WithTop.coe_ne_top (top_le_iff.1 hz_val)
  have hz2_dom : f z2 ≠ ⊤ := by
    intro htop; rw [htop, add_top] at hz_val; exact WithTop.coe_ne_top (top_le_iff.1 hz_val)
  have hle : ∀ u : V, z1 u ≤ z2 u := by
    intro u
    by_contra hlt
    push_neg at hlt
    obtain ⟨v, hv, α0, hα0, hex⟩ := hm z1 hz1_dom z2 hz2_dom u hlt
    change z1 v < z2 v at hv
    have huv : u ≠ v := fun h => by subst h; linarith
    let t : ℝ := min α0 (min ((z1 u - z2 u) / 2) ((z2 v - z1 v) / 2))
    have ht_pos : 0 < t := lt_min hα0 (lt_min (by linarith) (by linarith))
    have ht_α0 : t ≤ α0 := min_le_left _ _
    have htu : 2 * t ≤ z1 u - z2 u := by
      have : t ≤ (z1 u - z2 u) / 2 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have htv : 2 * t ≤ z2 v - z1 v := by
      have : t ≤ (z2 v - z1 v) / 2 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    obtain ⟨hz1'_box, hz2'_box, hφ_step⟩ := step_in_box huv hz1_box hz2_box ht_pos.le htu htv
    set z1' : V → ℝ := fun w => z1 w - t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)
    set z2' : V → ℝ := fun w => z2 w + t * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)
    have hz'_mem : (z1', z2') ∈ K := by
      refine ⟨⟨hz1'_box, hz2'_box⟩, ?_, ?_, ?_⟩
      · change ∑ w, z1' w = ∑ w, x w
        rw [sum_ex_sub, hz1_sum]
      · change ∑ w, z2' w = ∑ w, y w
        rw [sum_ex_add, hz2_sum]
      · exact (hex t ht_pos.le ht_α0).trans hz_val
    have hmin_le : φ (z1, z2) ≤ φ (z1', z2') := hz_min hz'_mem
    change ∑ w, |z1 w - z2 w| ≤ ∑ w, |z1' w - z2' w| at hmin_le
    linarith
  have heq : z1 = z2 := by
    funext u
    refine le_antisymm (hle u) ?_
    by_contra hlt
    push_neg at hlt
    obtain ⟨v, hv, -⟩ := hm z2 hz2_dom z1 hz1_dom u hlt
    change z2 v < z1 v at hv
    linarith [hle v]
  rw [← hz1_sum, ← hz2_sum, heq]

lemma mconv_trf {f : (V → ℝ) → WithTop ℝ} (hf : IsClosedProperConvex f)
    (hm : MExchangeAxiomR f) : TRFR (ConvexConjugateRW f) := by
  obtain ⟨x0, hx0⟩ := hf.1
  let r : ℝ := ∑ w : V, x0 w
  refine ⟨r, fun p α => ?_⟩
  have hsum_all : ∀ x : V → ℝ, ∀ a : ℝ, f x = (a : WithTop ℝ) →
      ∑ i, (p i + α) * x i - a = ((∑ i, p i * x i) - a) + α * r := by
    intro x a hfx
    have hx : f x ≠ ⊤ := by rw [hfx]; exact WithTop.coe_ne_top
    have hsx : ∑ i, x i = r := sum_const_R hf.2.1 hm hx hx0
    simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hsx]
    ring
  induction hcp : ConvexConjugateRW f p using WithTop.recTopCoe with
  | top =>
    rw [top_add]
    refine cc_top_of_unbdd fun M => ?_
    by_contra hall
    push_neg at hall
    have hle : ConvexConjugateRW f p ≤ ((M - α * r : ℝ) : WithTop ℝ) := by
      refine cc_le hf.1 fun x a hfx => ?_
      have h1 := (hall x a hfx).le
      rw [hsum_all x a hfx] at h1
      linarith
    rw [hcp] at hle
    exact WithTop.coe_ne_top (top_le_iff.1 hle)
  | coe c =>
    rw [← WithTop.coe_mul, ← WithTop.coe_add]
    refine le_antisymm ?_ ?_
    · refine cc_le hf.1 fun x a hfx => ?_
      have h1 := cc_bdd hcp hfx
      rw [hsum_all x a hfx]
      linarith
    · by_contra hlt
      push_neg at hlt
      obtain ⟨d, hd⟩ : ∃ d : ℝ, ConvexConjugateRW f (fun v => p v + α) = (d : WithTop ℝ) := by
        induction h : ConvexConjugateRW f (fun v => p v + α) using WithTop.recTopCoe with
        | top => exact absurd (h ▸ hlt) (not_lt_of_ge le_top)
        | coe d => exact ⟨d, rfl⟩
      rw [hd, WithTop.coe_lt_coe] at hlt
      let ε : ℝ := (c + α * r) - d
      have hε : 0 < ε := by dsimp [ε]; linarith
      obtain ⟨x, a, hfx, hgt⟩ := cc_exists_gt hcp (half_pos hε)
      have hbd := cc_bdd hd hfx
      rw [hsum_all x a hfx] at hbd
      dsimp [ε] at hgt
      linarith

lemma midpoint_pair {F : (V → ℝ) → WithTop ℝ} (hlsc : LowerSemicontinuous F)
    (hm : MExchangeAxiomR F) {u v : V} (huv : u ≠ v)
    {lo hi x y : V → ℝ} (hx_box : x ∈ Set.Icc lo hi) (hy_box : y ∈ Set.Icc lo hi)
    (hx : F x ≠ ⊤) (hy : F y ≠ ⊤) (hab : y u ≤ x u) (hcd : y v ≤ x v) :
    ∃ z1 z2 : V → ℝ, z1 ∈ Set.Icc lo hi ∧ z2 ∈ Set.Icc lo hi ∧
      z1 u = (x u + y u) / 2 ∧ z2 u = (x u + y u) / 2 ∧
      z1 v = x v ∧ z2 v = y v ∧
      F z1 ≠ ⊤ ∧ F z2 ≠ ⊤ ∧ rv F z1 + rv F z2 ≤ rv F x + rv F y := by
  let C : ℝ := rv F x + rv F y
  let K : Set ((V → ℝ) × (V → ℝ)) :=
    (Set.Icc lo hi ×ˢ Set.Icc lo hi) ∩
      ({p | p.1 v = x v} ∩
        ({p | p.2 v = y v} ∩
          ({p | p.1 u + p.2 u = x u + y u} ∩
            ({p | p.2 u ≤ p.1 u} ∩
              {p | F p.1 + F p.2 ≤ (C : WithTop ℝ)}))))
  have hK_compact : IsCompact K := by
    refine (isCompact_Icc.prod isCompact_Icc).inter_right ?_
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (sum_sublevel_isClosed hlsc hlsc C))))
    · exact isClosed_eq ((continuous_apply v).comp continuous_fst) continuous_const
    · exact isClosed_eq ((continuous_apply v).comp continuous_snd) continuous_const
    · exact isClosed_eq (((continuous_apply u).comp continuous_fst).add ((continuous_apply u).comp continuous_snd)) continuous_const
    · exact isClosed_le ((continuous_apply u).comp continuous_snd) ((continuous_apply u).comp continuous_fst)
  have hxy_mem : (x, y) ∈ K := by
    refine ⟨⟨hx_box, hy_box⟩, rfl, rfl, rfl, hab, ?_⟩
    simp only [Set.mem_setOf_eq, C, ← rv_spec hx, ← rv_spec hy, WithTop.coe_add, le_rfl]
  let ψ : (V → ℝ) × (V → ℝ) → ℝ := fun p => (p.1 u - p.2 u) + ∑ w : V, |p.1 w - p.2 w|
  have hψ_cont : Continuous ψ := by
    refine Continuous.add (((continuous_apply u).comp continuous_fst).sub ((continuous_apply u).comp continuous_snd)) ?_
    exact continuous_finset_sum _ fun w _ =>
      ((continuous_apply w).comp continuous_fst).sub ((continuous_apply w).comp continuous_snd) |>.abs
  obtain ⟨⟨z1, z2⟩, hz_mem, hz_min⟩ := hK_compact.exists_isMinOn ⟨(x, y), hxy_mem⟩ hψ_cont.continuousOn
  rcases hz_mem with ⟨⟨hz1_box, hz2_box⟩, hz1_v, hz2_v, hz_u_sum, hz_u_le, hz_val⟩
  change z1 v = x v at hz1_v
  change z2 v = y v at hz2_v
  change z1 u + z2 u = x u + y u at hz_u_sum
  change z2 u ≤ z1 u at hz_u_le
  change F z1 + F z2 ≤ (C : WithTop ℝ) at hz_val
  have hz1_dom : F z1 ≠ ⊤ := by
    intro htop; rw [htop, top_add] at hz_val; exact WithTop.coe_ne_top (top_le_iff.1 hz_val)
  have hz2_dom : F z2 ≠ ⊤ := by
    intro htop; rw [htop, add_top] at hz_val; exact WithTop.coe_ne_top (top_le_iff.1 hz_val)
  have hzu_eq : z1 u = z2 u := by
    refine le_antisymm ?_ hz_u_le
    by_contra hlt
    push_neg at hlt
    obtain ⟨w, hw, α0, hα0, hex⟩ := hm z1 hz1_dom z2 hz2_dom u hlt
    change z1 w < z2 w at hw
    have huw : u ≠ w := fun h => by subst h; linarith
    have hvw : v ≠ w := fun h => by subst h; linarith
    let t : ℝ := min α0 (min ((z1 u - z2 u) / 2) ((z2 w - z1 w) / 2))
    have ht_pos : 0 < t := lt_min hα0 (lt_min (by linarith) (by linarith))
    have ht_α0 : t ≤ α0 := min_le_left _ _
    have htu : 2 * t ≤ z1 u - z2 u := by
      have : t ≤ (z1 u - z2 u) / 2 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have htw : 2 * t ≤ z2 w - z1 w := by
      have : t ≤ (z2 w - z1 w) / 2 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    have hz1_sub : z1 ∈ Set.Icc (z1 ⊓ z2) (z1 ⊔ z2) := ⟨inf_le_left, le_sup_left⟩
    have hz2_sub : z2 ∈ Set.Icc (z1 ⊓ z2) (z1 ⊔ z2) := ⟨inf_le_right, le_sup_right⟩
    obtain ⟨hz1'_sub, hz2'_sub, hφ_step⟩ := step_in_box huw hz1_sub hz2_sub ht_pos.le htu htw
    set z1' : V → ℝ := fun k => z1 k - t * (IndicatorVec ({u} : Finset V) k - IndicatorVec ({w} : Finset V) k : ℝ)
    set z2' : V → ℝ := fun k => z2 k + t * (IndicatorVec ({u} : Finset V) k - IndicatorVec ({w} : Finset V) k : ℝ)
    have hz1'_box : z1' ∈ Set.Icc lo hi :=
      ⟨fun k => (le_inf (hz1_box.1 k) (hz2_box.1 k)).trans (hz1'_sub.1 k),
       fun k => (hz1'_sub.2 k).trans (sup_le (hz1_box.2 k) (hz2_box.2 k))⟩
    have hz2'_box : z2' ∈ Set.Icc lo hi :=
      ⟨fun k => (le_inf (hz1_box.1 k) (hz2_box.1 k)).trans (hz2'_sub.1 k),
       fun k => (hz2'_sub.2 k).trans (sup_le (hz1_box.2 k) (hz2_box.2 k))⟩
    have hz1'_u : z1' u = z1 u - t := by
      dsimp [z1']; rw [ind_sub, if_pos rfl, if_neg huw, sub_zero, mul_one]
    have hz2'_u : z2' u = z2 u + t := by
      dsimp [z2']; rw [ind_sub, if_pos rfl, if_neg huw, sub_zero, mul_one]
    have hz1'_v : z1' v = x v := by
      dsimp [z1']; rw [ind_sub, if_neg huv.symm, if_neg hvw, sub_zero, mul_zero, sub_zero, hz1_v]
    have hz2'_v : z2' v = y v := by
      dsimp [z2']; rw [ind_sub, if_neg huv.symm, if_neg hvw, sub_zero, mul_zero, add_zero, hz2_v]
    have hz'_mem : (z1', z2') ∈ K := by
      refine ⟨⟨hz1'_box, hz2'_box⟩, hz1'_v, hz2'_v, ?_, ?_, ?_⟩
      · change z1' u + z2' u = x u + y u
        rw [hz1'_u, hz2'_u]; linarith
      · change z2' u ≤ z1' u
        rw [hz1'_u, hz2'_u]; linarith
      · exact (hex t ht_pos.le ht_α0).trans hz_val
    have hmin_le : ψ (z1, z2) ≤ ψ (z1', z2') := hz_min hz'_mem
    change (z1 u - z2 u) + ∑ k, |z1 k - z2 k| ≤ (z1' u - z2' u) + ∑ k, |z1' k - z2' k| at hmin_le
    rw [hz1'_u, hz2'_u, hφ_step] at hmin_le
    linarith
  refine ⟨z1, z2, hz1_box, hz2_box, by linarith, by linarith, hz1_v, hz2_v, hz1_dom, hz2_dom, ?_⟩
  rw [rv_spec hz1_dom, rv_spec hz2_dom, ← WithTop.coe_add, WithTop.coe_le_coe] at hz_val
  exact hz_val

lemma lsc_bddBelow_on_compact {F : (V → ℝ) → WithTop ℝ} (hlsc : LowerSemicontinuous F)
    {B : Set (V → ℝ)} (hB : IsCompact B) :
    ∃ M : ℝ, ∀ z ∈ B, F z ≠ ⊤ → M ≤ rv F z := by
  have hcov : B ⊆ ⋃ n : ℕ, {z : V → ℝ | ((- (n : ℝ) : ℝ) : WithTop ℝ) < F z} := by
    intro z _
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    induction F z using WithTop.recTopCoe with
    | top => exact ⟨0, WithTop.coe_lt_top _⟩
    | coe a =>
      obtain ⟨n, hn⟩ := exists_nat_gt (-a)
      exact ⟨n, WithTop.coe_lt_coe.2 (by linarith)⟩
  obtain ⟨t, ht⟩ := hB.elim_finite_subcover
    (fun n : ℕ => {z : V → ℝ | ((- (n : ℝ) : ℝ) : WithTop ℝ) < F z})
    (fun n => hlsc.isOpen_preimage _) hcov
  let N : ℕ := t.sup id
  refine ⟨- (N : ℝ), fun z hz hFz => ?_⟩
  rcases Set.mem_iUnion₂.1 (ht hz) with ⟨n, hn_mem, hzn⟩
  simp only [Set.mem_setOf_eq] at hzn
  rw [rv_spec hFz, WithTop.coe_lt_coe] at hzn
  have hnN : (n : ℝ) ≤ (N : ℝ) := Nat.cast_le.2 (Finset.le_sup (f := id) hn_mem)
  linarith

lemma box_convex_comb {F : (V → ℝ) → WithTop ℝ} (hconv : IsConvexWithTop F)
    {lo hi z1 z2 : V → ℝ} (hz1_box : z1 ∈ Set.Icc lo hi) (hz2_box : z2 ∈ Set.Icc lo hi)
    (hz1_dom : F z1 ≠ ⊤) (hz2_dom : F z2 ≠ ⊤) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun w => (1 - t) * z1 w + t * z2 w) ∈ Set.Icc lo hi ∧
      F (fun w => (1 - t) * z1 w + t * z2 w) ≠ ⊤ := by
  refine ⟨⟨fun w => by nlinarith [hz1_box.1 w, hz2_box.1 w],
           fun w => by nlinarith [hz1_box.2 w, hz2_box.2 w]⟩, ?_⟩
  have hc := hconv z1 z2 (1 - t) (by linarith) (by linarith)
  have heq : (fun w => (1 - t) * z1 w + (1 - (1 - t)) * z2 w) =
      (fun w => (1 - t) * z1 w + t * z2 w) := by funext w; ring
  rw [heq] at hc
  have h1 : PosScalarMul (1 - t) (F z1) ≤ (((1 - t) * rv F z1 : ℝ) : WithTop ℝ) :=
    psm_le_coe (by linarith) (rv_spec hz1_dom).le
  have h2 : PosScalarMul (1 - (1 - t)) (F z2) ≤ ((t * rv F z2 : ℝ) : WithTop ℝ) := by
    rw [show 1 - (1 - t) = t by ring]
    exact psm_le_coe ht0 (rv_spec hz2_dom).le
  have hle := hc.trans ((add_le_add h1 h2).trans (by rw [← WithTop.coe_add]))
  exact ne_of_lt (hle.trans_lt (WithTop.coe_lt_top _))

lemma near_endpoints {F : (V → ℝ) → WithTop ℝ} (hlsc : LowerSemicontinuous F)
    (hconv : IsConvexWithTop F) (hm : MExchangeAxiomR F) {u v : V} (huv : u ≠ v)
    {x y : V → ℝ} (hx : F x ≠ ⊤) (hy : F y ≠ ⊤) (hab : y u < x u) (hcd : y v < x v)
    (m : ℕ) (hm_ge : 1 ≤ m) :
    let δ := (x u - y u) / ((m : ℝ) + 2)
    ∃ z1 z2 : V → ℝ, z1 u = y u + δ ∧ z2 u = x u - δ ∧ z1 v = x v ∧ z2 v = y v ∧
      F z1 ≠ ⊤ ∧ F z2 ≠ ⊤ ∧ rv F z1 + rv F z2 ≤ rv F x + rv F y + δ := by
  intro δ
  let lo : V → ℝ := x ⊓ y
  let hi : V → ℝ := x ⊔ y
  let a : ℝ := y u
  let b : ℝ := x u
  let c : ℝ := y v
  let d : ℝ := x v
  have hx_box : x ∈ Set.Icc lo hi := ⟨inf_le_left, le_sup_left⟩
  have hy_box : y ∈ Set.Icc lo hi := ⟨inf_le_right, le_sup_right⟩
  let Slice : ℝ → ℝ → Set (V → ℝ) := fun s t =>
    {z ∈ Set.Icc lo hi | z u = s ∧ z v = t ∧ F z ≠ ⊤}
  have hx_slice : x ∈ Slice b d := ⟨hx_box, rfl, rfl, hx⟩
  have hy_slice : y ∈ Slice a c := ⟨hy_box, rfl, rfl, hy⟩
  -- Step 1: dyadic points in Slice
  have hdyadic : ∀ k : ℕ,
      (Slice (a + (b - a) / 2 ^ (k + 1)) d).Nonempty ∧
      (Slice (b - (b - a) / 2 ^ (k + 1)) c).Nonempty := by
    intro k
    induction k with
    | zero =>
      obtain ⟨z1, z2, hz1_box, hz2_box, hz1_u, hz2_u, hz1_v, hz2_v, hz1_dom, hz2_dom, -⟩ :=
        midpoint_pair hlsc hm huv hx_box hy_box hx hy hab.le hcd.le
      have h1 : (b + a) / 2 = a + (b - a) / 2 ^ (0 + 1) := by ring
      have h2 : (b + a) / 2 = b - (b - a) / 2 ^ (0 + 1) := by ring
      exact ⟨⟨z1, hz1_box, hz1_u.trans h1, hz1_v, hz1_dom⟩,
             ⟨z2, hz2_box, hz2_u.trans h2, hz2_v, hz2_dom⟩⟩
    | succ k ih =>
      obtain ⟨⟨wd, hwd_box, hwd_u, hwd_v, hwd_dom⟩, ⟨wc, hwc_box, hwc_u, hwc_v, hwc_dom⟩⟩ := ih
      have hba_pos : 0 < (b - a) / 2 ^ (k + 1) := div_pos (sub_pos.2 hab) (by positivity)
      obtain ⟨z1, _, hz1_box, _, hz1_u, _, hz1_v, _, hz1_dom, _, -⟩ :=
        midpoint_pair hlsc hm huv hwd_box hy_box hwd_dom hy
          (by rw [hwd_u]; linarith) (by rw [hwd_v]; exact hcd.le)
      obtain ⟨_, w2, _, hw2_box, _, hw2_u, _, hw2_v, _, hw2_dom, -⟩ :=
        midpoint_pair hlsc hm huv hx_box hwc_box hx hwc_dom
          (by rw [hwc_u]; linarith) (by rw [hwc_v]; exact hcd.le)
      have h1 : (wd u + a) / 2 = a + (b - a) / 2 ^ (k + 1 + 1) := by
        rw [hwd_u, pow_succ]; ring
      have h2 : (b + wc u) / 2 = b - (b - a) / 2 ^ (k + 1 + 1) := by
        rw [hwc_u, pow_succ]; ring
      exact ⟨⟨z1, hz1_box, hz1_u.trans h1, hz1_v.trans hwd_v, hz1_dom⟩,
             ⟨w2, hw2_box, hw2_u.trans h2, hw2_v.trans hwc_v, hw2_dom⟩⟩
  -- Step 2: every s ∈ (a, b) has nonempty Slice s d and Slice s c
  have hslice_ne : ∀ s : ℝ, a < s → s < b →
      (Slice s d).Nonempty ∧ (Slice s c).Nonempty := by
    intro s has hsb
    let δ0 : ℝ := min (s - a) (b - s)
    have hδ0_pos : 0 < δ0 := lt_min (sub_pos.2 has) (sub_pos.2 hsb)
    obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / δ0)
    have hk_pow : (k : ℝ) < (2 : ℝ) ^ (k + 1) := by
      have h1 : k < 2 ^ (k + 1) := k.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))
      exact_mod_cast h1
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
    have hstep_le : (b - a) / 2 ^ (k + 1) ≤ δ0 := by
      have h1 : (b - a) / δ0 < (2 : ℝ) ^ (k + 1) := hk.trans hk_pow
      rw [div_lt_iff₀ hδ0_pos] at h1
      rw [div_le_iff₀ hpow_pos]
      linarith
    have hstep_pos : 0 < (b - a) / 2 ^ (k + 1) := div_pos (sub_pos.2 hab) hpow_pos
    obtain ⟨⟨wd, hwd_box, hwd_u, hwd_v, hwd_dom⟩, ⟨wc, hwc_box, hwc_u, hwc_v, hwc_dom⟩⟩ := hdyadic k
    let s1 : ℝ := a + (b - a) / 2 ^ (k + 1)
    let s2 : ℝ := b - (b - a) / 2 ^ (k + 1)
    have hs1_le : s1 ≤ s := by
      have : (b - a) / 2 ^ (k + 1) ≤ s - a := hstep_le.trans (min_le_left _ _)
      dsimp [s1]; linarith
    have hs2_ge : s ≤ s2 := by
      have : (b - a) / 2 ^ (k + 1) ≤ b - s := hstep_le.trans (min_le_right _ _)
      dsimp [s2]; linarith
    have hbs1 : 0 < b - s1 := by linarith
    have hs2a : 0 < s2 - a := by linarith
    let t1 : ℝ := (s - s1) / (b - s1)
    let t2 : ℝ := (s - a) / (s2 - a)
    have ht1_0 : 0 ≤ t1 := div_nonneg (by linarith) hbs1.le
    have ht1_1 : t1 ≤ 1 := (div_le_one hbs1).2 (by linarith)
    have ht2_0 : 0 ≤ t2 := div_nonneg (by linarith) hs2a.le
    have ht2_1 : t2 ≤ 1 := (div_le_one hs2a).2 (by linarith)
    obtain ⟨hzd_box, hzd_dom⟩ := box_convex_comb hconv hwd_box hx_box hwd_dom hx ht1_0 ht1_1
    obtain ⟨hzc_box, hzc_dom⟩ := box_convex_comb hconv hy_box hwc_box hy hwc_dom ht2_0 ht2_1
    refine ⟨⟨fun w => (1 - t1) * wd w + t1 * x w, hzd_box, ?_, ?_, hzd_dom⟩,
            ⟨fun w => (1 - t2) * y w + t2 * wc w, hzc_box, ?_, ?_, hzc_dom⟩⟩
    · change (1 - t1) * wd u + t1 * x u = s
      have h1 : (1 - t1) * wd u + t1 * x u = s1 + t1 * (b - s1) := by
        rw [hwd_u]; dsimp [s1, b]; ring
      rw [h1]; dsimp [t1]
      rw [div_mul_cancel₀ _ hbs1.ne']
      ring
    · change (1 - t1) * wd v + t1 * x v = d
      rw [hwd_v]; dsimp [d]; ring
    · change (1 - t2) * y u + t2 * wc u = s
      have h1 : (1 - t2) * y u + t2 * wc u = a + t2 * (s2 - a) := by
        rw [hwc_u]; dsimp [s2, a]; ring
      rw [h1]; dsimp [t2]
      rw [div_mul_cancel₀ _ hs2a.ne']
      ring
    · change (1 - t2) * y v + t2 * wc v = c
      rw [hwc_v]; dsimp [c]; ring
  -- Step 3: sInf over Slice s d and Slice s c
  obtain ⟨M0, hM0⟩ := lsc_bddBelow_on_compact hlsc isCompact_Icc
  let S : ℝ → ℝ → Set ℝ := fun s t => (rv F) '' (Slice s t)
  have hS_bdd : ∀ s t : ℝ, BddBelow (S s t) := by
    intro s t
    refine ⟨M0, ?_⟩
    rintro _ ⟨z, ⟨hz_box, _, _, hz_dom⟩, rfl⟩
    exact hM0 z hz_box hz_dom
  have hS_ne : ∀ s : ℝ, a < s → s < b → (S s d).Nonempty ∧ (S s c).Nonempty := by
    intro s has hsb
    obtain ⟨h1, h2⟩ := hslice_ne s has hsb
    exact ⟨h1.image (rv F), h2.image (rv F)⟩
  let hd : ℝ → ℝ := fun s => sInf (S s d)
  let hc : ℝ → ℝ := fun s => sInf (S s c)
  have hmid_gen : ∀ s1 s2 : ℝ, s1 ≤ s2 →
      ∀ z2 ∈ Slice s2 d, ∀ z1 ∈ Slice s1 c,
        hd ((s1 + s2) / 2) + hc ((s1 + s2) / 2) ≤ rv F z2 + rv F z1 := by
    intro s1 s2 hs12 z2 ⟨hz2_box, hz2_u, hz2_v, hz2_dom⟩ z1 ⟨hz1_box, hz1_u, hz1_v, hz1_dom⟩
    obtain ⟨w1, w2, hw1_box, hw2_box, hw1_u, hw2_u, hw1_v, hw2_v, hw1_dom, hw2_dom, hval⟩ :=
      midpoint_pair hlsc hm huv hz2_box hz1_box hz2_dom hz1_dom
        (by rw [hz1_u, hz2_u]; exact hs12) (by rw [hz1_v, hz2_v]; exact hcd.le)
    have hmu : (z2 u + z1 u) / 2 = (s1 + s2) / 2 := by rw [hz1_u, hz2_u]; ring
    have hw1_mem : rv F w1 ∈ S ((s1 + s2) / 2) d :=
      ⟨w1, ⟨hw1_box, hw1_u.trans hmu, hw1_v.trans hz2_v, hw1_dom⟩, rfl⟩
    have hw2_mem : rv F w2 ∈ S ((s1 + s2) / 2) c :=
      ⟨w2, ⟨hw2_box, hw2_u.trans hmu, hw2_v.trans hz1_v, hw2_dom⟩, rfl⟩
    have h1 : hd ((s1 + s2) / 2) ≤ rv F w1 := csInf_le (hS_bdd _ _) hw1_mem
    have h2 : hc ((s1 + s2) / 2) ≤ rv F w2 := csInf_le (hS_bdd _ _) hw2_mem
    linarith
  have hmid_int : ∀ s1 s2 : ℝ, a < s1 → s1 ≤ s2 → s2 < b →
      hd ((s1 + s2) / 2) + hc ((s1 + s2) / 2) ≤ hd s2 + hc s1 := by
    intro s1 s2 has1 hs12 hs2b
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hlt2 : sInf (S s2 d) < hd s2 + ε / 2 := by change hd s2 < hd s2 + ε / 2; linarith
    have hlt1 : sInf (S s1 c) < hc s1 + ε / 2 := by change hc s1 < hc s1 + ε / 2; linarith
    obtain ⟨_, ⟨z2, hz2, rfl⟩, hz2_lt⟩ :=
      exists_lt_of_csInf_lt (hS_ne s2 (has1.trans_le hs12) hs2b).1 hlt2
    obtain ⟨_, ⟨z1, hz1, rfl⟩, hz1_lt⟩ :=
      exists_lt_of_csInf_lt (hS_ne s1 has1 (hs12.trans_lt hs2b)).2 hlt1
    have h1 := hmid_gen s1 s2 hs12 z2 hz2 z1 hz1
    linarith
  have hmid_left : ∀ s2 : ℝ, a < s2 → s2 < b →
      hd ((a + s2) / 2) + hc ((a + s2) / 2) ≤ hd s2 + rv F y := by
    intro s2 has2 hs2b
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hlt2 : sInf (S s2 d) < hd s2 + ε := by change hd s2 < hd s2 + ε; linarith
    obtain ⟨_, ⟨z2, hz2, rfl⟩, hz2_lt⟩ :=
      exists_lt_of_csInf_lt (hS_ne s2 has2 hs2b).1 hlt2
    have h1 := hmid_gen a s2 has2.le z2 hz2 y hy_slice
    linarith
  have hmid_right : ∀ s1 : ℝ, a < s1 → s1 < b →
      hd ((s1 + b) / 2) + hc ((s1 + b) / 2) ≤ rv F x + hc s1 := by
    intro s1 has1 hs1b
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hlt1 : sInf (S s1 c) < hc s1 + ε := by change hc s1 < hc s1 + ε; linarith
    obtain ⟨_, ⟨z1, hz1, rfl⟩, hz1_lt⟩ :=
      exists_lt_of_csInf_lt (hS_ne s1 has1 hs1b).2 hlt1
    have h1 := hmid_gen s1 b hs1b.le x hx_slice z1 hz1
    linarith
  -- Step 4: Telescoping along s k = a + k * δ for k = 1 .. m
  have hN_pos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hδ_pos : 0 < δ := div_pos (sub_pos.2 hab) hN_pos
  have hN_δ : ((m : ℝ) + 2) * δ = b - a := mul_div_cancel₀ (b - a) hN_pos.ne'
  let s : ℕ → ℝ := fun k => a + (k : ℝ) * δ
  have hs_in : ∀ k : ℕ, 1 ≤ k → k ≤ m + 1 → a < s k ∧ s k < b := by
    intro k hk1 hkm
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    have hk_lt : (k : ℝ) < (m : ℝ) + 2 := by
      have : k < m + 2 := Nat.lt_succ_of_le hkm
      exact_mod_cast this
    refine ⟨by dsimp [s]; nlinarith, ?_⟩
    dsimp [s]
    nlinarith
  have htele : ∀ k : ℕ, 1 ≤ k → k ≤ m →
      hd (s 1) + hc (s k) ≤ hd (s (k + 1)) + rv F y := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro _
      have hs2 := hs_in 2 (by omega) (by omega)
      have hm2 : (a + s 2) / 2 = s 1 := by dsimp [s]; push_cast; ring
      have h := hmid_left (s 2) hs2.1 hs2.2
      rwa [hm2] at h
    | succ k hk1 ih =>
      intro hk_le
      have ih' := ih (by omega)
      have hsk := hs_in k hk1 (by omega)
      have hsk2 := hs_in (k + 2) (by omega) (by omega)
      have hle_k : s k ≤ s (k + 2) := by
        dsimp [s]; push_cast; linarith
      have hmid_k : (s k + s (k + 2)) / 2 = s (k + 1) := by
        dsimp [s]; push_cast; ring
      have h := hmid_int (s k) (s (k + 2)) hsk.1 hle_k hsk2.2
      rw [hmid_k] at h
      linarith
  have htele_m := htele m hm_ge le_rfl
  have hsm := hs_in m hm_ge (by omega)
  have hmid_m : (s m + b) / 2 = s (m + 1) := by
    dsimp [s]; push_cast; linarith [hN_δ]
  have hright_m := hmid_right (s m) hsm.1 hsm.2
  rw [hmid_m] at hright_m
  have hsum_inf : hd (s 1) + hc (s (m + 1)) ≤ rv F x + rv F y := by linarith
  -- Step 5: Pick z1 ∈ Slice (s 1) d and z2 ∈ Slice (s (m + 1)) c within δ / 2 of infimum
  have hs1_in := hs_in 1 le_rfl (by omega)
  have hsm1_in := hs_in (m + 1) (by omega) le_rfl
  have hlt_s1 : sInf (S (s 1) d) < hd (s 1) + δ / 2 := by change hd (s 1) < hd (s 1) + δ / 2; linarith
  have hlt_sm1 : sInf (S (s (m + 1)) c) < hc (s (m + 1)) + δ / 2 := by
    change hc (s (m + 1)) < hc (s (m + 1)) + δ / 2; linarith
  obtain ⟨_, ⟨z1, ⟨_, hz1_u, hz1_v, hz1_dom⟩, rfl⟩, hz1_lt⟩ :=
    exists_lt_of_csInf_lt (hS_ne (s 1) hs1_in.1 hs1_in.2).1 hlt_s1
  obtain ⟨_, ⟨z2, ⟨_, hz2_u, hz2_v, hz2_dom⟩, rfl⟩, hz2_lt⟩ :=
    exists_lt_of_csInf_lt (hS_ne (s (m + 1)) hsm1_in.1 hsm1_in.2).2 hlt_sm1
  have hs1_eq : s 1 = y u + δ := by dsimp [s, a]; ring
  have hsm1_eq : s (m + 1) = x u - δ := by
    dsimp [s, a, b] at hN_δ ⊢; push_cast; linarith
  exact ⟨z1, z2, hz1_u.trans hs1_eq, hz2_u.trans hsm1_eq, hz1_v, hz2_v, hz1_dom, hz2_dom, by linarith⟩

def singleV (u : V) (c : ℝ) : V → ℝ := fun w => if w = u then c else 0

lemma rdot_singleV_left (u : V) (c : ℝ) (z : V → ℝ) :
    rdot (singleV u c) z = c * z u := by
  simp [rdot, singleV]

lemma rdot_add_left (p q z : V → ℝ) :
    rdot (p + q) z = rdot p z + rdot q z := by
  simp only [rdot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

noncomputable def F_tilt (f : (V → ℝ) → WithTop ℝ) (r : V → ℝ) : (V → ℝ) → WithTop ℝ :=
  fun z => f z + ((- rdot r z : ℝ) : WithTop ℝ)

lemma F_tilt_ne_top {f : (V → ℝ) → WithTop ℝ} {r z : V → ℝ} :
    F_tilt f r z ≠ ⊤ ↔ f z ≠ ⊤ := by
  unfold F_tilt
  induction f z using WithTop.recTopCoe with
  | top => simp
  | coe a => rw [← WithTop.coe_add]; simp

lemma rv_F_tilt {f : (V → ℝ) → WithTop ℝ} {r z : V → ℝ} (hz : f z ≠ ⊤) :
    rv (F_tilt f r) z = rv f z - rdot r z := by
  apply rv_of_eq
  unfold F_tilt
  rw [rv_spec hz, ← WithTop.coe_add]
  congr 1

lemma F_tilt_lsc {f : (V → ℝ) → WithTop ℝ} (hlsc : LowerSemicontinuous f) (r : V → ℝ) :
    LowerSemicontinuous (F_tilt f r) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro C
  induction C using WithTop.recTopCoe with
  | top =>
    have : F_tilt f r ⁻¹' Set.Iic ⊤ = Set.univ := by ext z; simp
    rw [this]; exact isClosed_univ
  | coe c =>
    have hcont : Continuous (fun z : V → ℝ => (z, c + rdot r z)) :=
      continuous_id.prodMk (continuous_const.add (continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)))
    have heq : F_tilt f r ⁻¹' Set.Iic (c : WithTop ℝ) =
        (fun z : V → ℝ => (z, c + rdot r z)) ⁻¹' EpiSet f := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, EpiSet, Set.mem_setOf_eq, F_tilt]
      induction f z using WithTop.recTopCoe with
      | top => simp
      | coe a =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
        constructor <;> intro h <;> linarith
    rw [heq]
    exact (epiSet_isClosed hlsc).preimage hcont

lemma F_tilt_convex {f : (V → ℝ) → WithTop ℝ} (hconv : IsConvexWithTop f) (r : V → ℝ) :
    IsConvexWithTop (F_tilt f r) := by
  intro x y t ht0 ht1
  by_cases ht_zero : t = 0
  · subst ht_zero
    have heq : (fun v => 0 * x v + (1 - 0) * y v) = y := by funext v; ring
    have hx0 : PosScalarMul 0 (F_tilt f r x) = 0 := by
      induction F_tilt f r x using WithTop.recTopCoe <;> simp [PosScalarMul]
    have hy1 : PosScalarMul (1 - 0) (F_tilt f r y) = F_tilt f r y := by
      induction F_tilt f r y using WithTop.recTopCoe <;> simp [PosScalarMul]
    rw [heq, hx0, hy1, zero_add]
  by_cases ht_one : t = 1
  · subst ht_one
    have heq : (fun v => 1 * x v + (1 - 1) * y v) = x := by funext v; ring
    have hx1 : PosScalarMul 1 (F_tilt f r x) = F_tilt f r x := by
      induction F_tilt f r x using WithTop.recTopCoe <;> simp [PosScalarMul]
    have hy0 : PosScalarMul (1 - 1) (F_tilt f r y) = 0 := by
      induction F_tilt f r y using WithTop.recTopCoe <;> simp [PosScalarMul]
    rw [heq, hx1, hy0, add_zero]
  have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
  have ht1_pos : 0 < 1 - t := by linarith [lt_of_le_of_ne ht1 ht_one]
  by_cases hx : f x = ⊤
  · have hFx : F_tilt f r x = ⊤ := by simp [F_tilt, hx]
    rw [hFx]; simp [PosScalarMul, if_neg ht_pos.ne']
  by_cases hy : f y = ⊤
  · have hFy : F_tilt f r y = ⊤ := by simp [F_tilt, hy]
    rw [hFy]; simp [PosScalarMul, if_neg ht1_pos.ne']
  have h1 := hconv x y t ht0 ht1
  have hx_le := psm_le_coe ht0 (rv_spec hx).le
  have hy_le := psm_le_coe ht1_pos.le (rv_spec hy).le
  have hle := h1.trans ((add_le_add hx_le hy_le).trans (by rw [← WithTop.coe_add]))
  have hFz_fx : F_tilt f r x = ((rv f x - rdot r x : ℝ) : WithTop ℝ) := by
    unfold F_tilt; rw [rv_spec hx, ← WithTop.coe_add]; congr 1
  have hFz_fy : F_tilt f r y = ((rv f y - rdot r y : ℝ) : WithTop ℝ) := by
    unfold F_tilt; rw [rv_spec hy, ← WithTop.coe_add]; congr 1
  rw [hFz_fx, hFz_fy]
  simp only [PosScalarMul, if_neg ht_pos.ne', if_neg ht1_pos.ne', ← WithTop.coe_add]
  unfold F_tilt
  refine (add_le_add hle le_rfl).trans ?_
  rw [← WithTop.coe_add, WithTop.coe_le_coe]
  have hrdot : rdot r (fun v => t * x v + (1 - t) * y v) = t * rdot r x + (1 - t) * rdot r y := by
    dsimp [rdot]
    have : ∀ i, r i * (t * x i + (1 - t) * y i) = t * (r i * x i) + (1 - t) * (r i * y i) :=
      fun i => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hrdot]
  linarith

lemma F_tilt_mexc {f : (V → ℝ) → WithTop ℝ} (hm : MExchangeAxiomR f) (r : V → ℝ) :
    MExchangeAxiomR (F_tilt f r) := by
  intro x hx y hy u hu
  have hx' : f x ≠ ⊤ := F_tilt_ne_top.1 hx
  have hy' : f y ≠ ⊤ := F_tilt_ne_top.1 hy
  obtain ⟨v, hv, α0, hα0, hex⟩ := hm x hx' y hy' u hu
  refine ⟨v, hv, α0, hα0, fun α hα0' hα_le => ?_⟩
  have h := hex α hα0' hα_le
  set x' : V → ℝ := fun w => x w - α * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)
  set y' : V → ℝ := fun w => y w + α * (IndicatorVec ({u} : Finset V) w - IndicatorVec ({v} : Finset V) w : ℝ)
  rw [ge_iff_le, rv_spec hx', rv_spec hy', ← WithTop.coe_add] at h
  have hx'_dom : f x' ≠ ⊤ := by
    intro htop; rw [htop, top_add] at h; exact WithTop.coe_ne_top (top_le_iff.1 h)
  have hy'_dom : f y' ≠ ⊤ := by
    intro htop; rw [htop, add_top] at h; exact WithTop.coe_ne_top (top_le_iff.1 h)
  rw [rv_spec hx'_dom, rv_spec hy'_dom, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  rw [ge_iff_le, rv_spec hx, rv_spec hy, rv_spec (F_tilt_ne_top.2 hx'_dom),
      rv_spec (F_tilt_ne_top.2 hy'_dom), ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  rw [rv_F_tilt hx', rv_F_tilt hy', rv_F_tilt hx'_dom, rv_F_tilt hy'_dom]
  have hrd1 := rdot_ex_right r x u v α
  have hrd2 := rdot_ex_right_add r y u v α
  change rdot r x' = rdot r x - α * (r u - r v) at hrd1
  change rdot r y' = rdot r y + α * (r u - r v) at hrd2
  linarith

lemma g_two_coord {f : (V → ℝ) → WithTop ℝ} (hlsc : LowerSemicontinuous f)
    (hconv : IsConvexWithTop f) (hm : MExchangeAxiomR f)
    (r : V → ℝ) {u v : V} (huv : u ≠ v) {cu dv : ℝ} (hcu : 0 ≤ cu) (hdv : 0 ≤ dv)
    (hfin_u : ConvexConjugateRW f (r + singleV u cu) ≠ ⊤)
    (hfin_v : ConvexConjugateRW f (r + singleV v dv) ≠ ⊤)
    {x y : V → ℝ} (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) :
    (rdot (r + singleV u cu + singleV v dv) x - rv f x) + (rdot r y - rv f y) ≤
      rv (ConvexConjugateRW f) (r + singleV u cu) + rv (ConvexConjugateRW f) (r + singleV v dv) := by
  let F := F_tilt f r
  have hF_lsc := F_tilt_lsc hlsc r
  have hF_conv := F_tilt_convex hconv r
  have hF_mexc := F_tilt_mexc hm r
  have hFx : F x ≠ ⊤ := F_tilt_ne_top.2 hx
  have hFy : F y ≠ ⊤ := F_tilt_ne_top.2 hy
  have hbound_pair : ∀ z1 z2 : V → ℝ, F z1 ≠ ⊤ → F z2 ≠ ⊤ →
      cu * z2 u + dv * z1 v - (rv F z1 + rv F z2) ≤
        rv (ConvexConjugateRW f) (r + singleV u cu) + rv (ConvexConjugateRW f) (r + singleV v dv) := by
    intro z1 z2 hz1 hz2
    have hz1' : f z1 ≠ ⊤ := F_tilt_ne_top.1 hz1
    have hz2' : f z2 ≠ ⊤ := F_tilt_ne_top.1 hz2
    have h1 := cc_bdd (rv_spec hfin_v) (rv_spec hz1')
    have h2 := cc_bdd (rv_spec hfin_u) (rv_spec hz2')
    change rdot (r + singleV v dv) z1 - rv f z1 ≤ rv (ConvexConjugateRW f) (r + singleV v dv) at h1
    change rdot (r + singleV u cu) z2 - rv f z2 ≤ rv (ConvexConjugateRW f) (r + singleV u cu) at h2
    rw [rdot_add_left, rdot_singleV_left] at h1 h2
    rw [rv_F_tilt hz1', rv_F_tilt hz2']
    linarith
  have hgoal_eq : (rdot (r + singleV u cu + singleV v dv) x - rv f x) + (rdot r y - rv f y) =
      cu * x u + dv * x v - (rv F x + rv F y) := by
    rw [rdot_add_left, rdot_add_left, rdot_singleV_left, rdot_singleV_left, rv_F_tilt hx, rv_F_tilt hy]
    ring
  rw [hgoal_eq]
  rcases le_or_gt (x v) (y v) with hxv | hxv
  · have h := hbound_pair y x hFy hFx
    have : dv * x v ≤ dv * y v := mul_le_mul_of_nonneg_left hxv hdv
    linarith
  rcases le_or_gt (x u) (y u) with hxu | hxu
  · have h := hbound_pair x y hFx hFy
    have : cu * x u ≤ cu * y u := mul_le_mul_of_nonneg_left hxu hcu
    linarith
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨m, hm_gt⟩ := exists_nat_gt ((cu + 1) * (x u - y u) / ε)
    let m' : ℕ := m + 1
    have hm'_ge : 1 ≤ m' := Nat.le_add_left 1 m
    obtain ⟨z1, z2, hz1_u, hz2_u, hz1_v, hz2_v, hz1_dom, hz2_dom, hval⟩ :=
      near_endpoints hF_lsc hF_conv hF_mexc huv hFx hFy hxu hxv m' hm'_ge
    let δ : ℝ := (x u - y u) / ((m' : ℝ) + 2)
    have h1 := hbound_pair z1 z2 hz1_dom hz2_dom
    rw [hz2_u, hz1_v] at h1
    have hδ_lt : (cu + 1) * δ < ε := by
      dsimp [δ, m']
      have hden_pos : (0 : ℝ) < (m : ℝ) + 1 + 2 := by positivity
      have hm_lt : (cu + 1) * (x u - y u) / ε < (m : ℝ) + 1 + 2 := by
        calc (cu + 1) * (x u - y u) / ε < (m : ℝ) := hm_gt
          _ < (m : ℝ) + 1 + 2 := by linarith
      rw [div_lt_iff₀ hε] at hm_lt
      have : (cu + 1) * ((x u - y u) / ((m : ℝ) + 1 + 2)) =
          ((cu + 1) * (x u - y u)) / ((m : ℝ) + 1 + 2) := by ring
      push_cast
      rw [this, div_lt_iff₀ hden_pos]
      linarith
    linarith

def restrictV (S : Finset V) (α : V → ℝ) : V → ℝ :=
  fun w => if w ∈ S then α w else 0

lemma restrictV_empty (α : V → ℝ) : restrictV (∅ : Finset V) α = 0 := by
  funext w; simp [restrictV]

lemma restrictV_cons {u : V} {S : Finset V} (hu : u ∉ S) (α : V → ℝ) :
    restrictV (Finset.cons u S hu) α = restrictV S α + singleV u (α u) := by
  funext w
  simp only [restrictV, singleV, Pi.add_apply, Finset.mem_cons]
  by_cases hwu : w = u
  · subst hwu; simp [hu]
  · simp [hwu]

lemma lattice_sbf_R (G : (V → ℝ) → ℝ)
    (hloc : ∀ r : V → ℝ, ∀ u v : V, u ≠ v → ∀ cu dv : ℝ, 0 ≤ cu → 0 ≤ dv →
      G (r + singleV u cu + singleV v dv) + G r ≤ G (r + singleV u cu) + G (r + singleV v dv)) :
    ∀ p q : V → ℝ, G (p ⊔ q) + G (p ⊓ q) ≤ G p + G q := by
  have step1 : ∀ (B : Finset V) (u : V), u ∉ B → ∀ (r β : V → ℝ) (cu : ℝ),
      0 ≤ cu → (∀ v ∈ B, 0 ≤ β v) →
      G (r + singleV u cu + restrictV B β) + G r ≤ G (r + singleV u cu) + G (r + restrictV B β) := by
    intro B
    induction B using Finset.cons_induction with
    | empty =>
      intro u _ r β cu _ _
      rw [restrictV_empty, add_zero, add_zero]
    | cons v B' hv ih =>
      intro u hu r β cu hcu hβ
      rw [Finset.mem_cons, not_or] at hu
      have huv : u ≠ v := hu.1
      have huB' : u ∉ B' := hu.2
      have hβv : 0 ≤ β v := hβ v (Finset.mem_cons_self v B')
      have hβB' : ∀ w ∈ B', 0 ≤ β w := fun w hw => hβ w (Finset.mem_cons.2 (Or.inr hw))
      have h1 := ih u huB' r β cu hcu hβB'
      have h2 := hloc (r + restrictV B' β) u v huv cu (β v) hcu hβv
      rw [restrictV_cons hv]
      have e1 : r + restrictV B' β + singleV u cu + singleV v (β v) =
          r + singleV u cu + (restrictV B' β + singleV v (β v)) := by
        funext w; simp only [Pi.add_apply]; ring
      have e2 : r + restrictV B' β + singleV u cu = r + singleV u cu + restrictV B' β := by
        funext w; simp only [Pi.add_apply]; ring
      have e3 : r + (restrictV B' β + singleV v (β v)) = r + restrictV B' β + singleV v (β v) := by
        funext w; simp only [Pi.add_apply]; ring
      rw [e1, e2] at h2
      rw [e3]
      linarith
  have step2 : ∀ (A B : Finset V), Disjoint A B → ∀ (r α β : V → ℝ),
      (∀ u ∈ A, 0 ≤ α u) → (∀ v ∈ B, 0 ≤ β v) →
      G (r + restrictV A α + restrictV B β) + G r ≤ G (r + restrictV A α) + G (r + restrictV B β) := by
    intro A
    induction A using Finset.cons_induction with
    | empty =>
      intro B _ r α β _ _
      rw [restrictV_empty, add_zero]
      linarith
    | cons u A' hu ih =>
      intro B hdisj r α β hα hβ
      have huB : u ∉ B := Finset.disjoint_left.1 hdisj (Finset.mem_cons_self u A')
      have hdisj' : Disjoint A' B :=
        Finset.disjoint_left.2 fun w hw => Finset.disjoint_left.1 hdisj (Finset.mem_cons.2 (Or.inr hw))
      have hαu : 0 ≤ α u := hα u (Finset.mem_cons_self u A')
      have hαA' : ∀ w ∈ A', 0 ≤ α w := fun w hw => hα w (Finset.mem_cons.2 (Or.inr hw))
      have h1 := ih B hdisj' r α β hαA' hβ
      have h2 := step1 B u huB (r + restrictV A' α) β (α u) hαu hβ
      rw [restrictV_cons hu]
      have e1 : r + (restrictV A' α + singleV u (α u)) = r + restrictV A' α + singleV u (α u) := by
        funext w; simp only [Pi.add_apply]; ring
      rw [e1]
      linarith
  intro p q
  let r : V → ℝ := p ⊓ q
  let α : V → ℝ := p - r
  let β : V → ℝ := q - r
  let A : Finset V := Finset.univ.filter (fun u => q u ≤ p u)
  let B : Finset V := Finset.univ.filter (fun v => p v < q v)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro w _ h1 h2; linarith
  have hα : ∀ u ∈ A, 0 ≤ α u := fun u _ => by
    simp only [α, r, Pi.sub_apply, Pi.inf_apply]; linarith [inf_le_left (a := p u) (b := q u)]
  have hβ : ∀ v ∈ B, 0 ≤ β v := fun v _ => by
    simp only [β, r, Pi.sub_apply, Pi.inf_apply]; linarith [inf_le_right (a := p v) (b := q v)]
  have h := step2 A B hdisj r α β hα hβ
  have ep : r + restrictV A α = p := by
    funext w
    simp only [r, α, restrictV, A, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.sub_apply, Pi.inf_apply]
    rcases le_or_gt (q w) (p w) with hle | hlt
    · rw [if_pos hle, min_eq_right hle]; ring
    · rw [if_neg (not_le.2 hlt), min_eq_left hlt.le]; ring
  have eq_q : r + restrictV B β = q := by
    funext w
    simp only [r, β, restrictV, B, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.sub_apply, Pi.inf_apply]
    rcases le_or_gt (q w) (p w) with hle | hlt
    · rw [if_neg (not_lt.2 hle), min_eq_right hle]; ring
    · rw [if_pos hlt, min_eq_left hlt.le]; ring
  have esup : r + restrictV A α + restrictV B β = p ⊔ q := by
    funext w
    have h1 := congrFun ep w
    have h2 := congrFun eq_q w
    simp only [Pi.add_apply, Pi.sup_apply, r, Pi.inf_apply] at h1 h2 ⊢
    rcases le_or_gt (q w) (p w) with hle | hlt
    · rw [max_eq_left hle]; rw [min_eq_right hle] at h1 h2 ⊢; linarith
    · rw [max_eq_right hlt.le]; rw [min_eq_left hlt.le] at h1 h2 ⊢; linarith
  rw [esup, ep, eq_q] at h
  exact h

noncomputable def truncR (N : ℝ) (f : (V → ℝ) → WithTop ℝ) : (V → ℝ) → WithTop ℝ :=
  fun z => if ∀ i, |z i| ≤ N then f z else ⊤

lemma truncR_ne_top {N : ℝ} {f : (V → ℝ) → WithTop ℝ} {z : V → ℝ} :
    truncR N f z ≠ ⊤ ↔ (∀ i, |z i| ≤ N) ∧ f z ≠ ⊤ := by
  unfold truncR; split_ifs with h <;> simp [h]

lemma truncR_eq {N : ℝ} {f : (V → ℝ) → WithTop ℝ} {z : V → ℝ} (h : ∀ i, |z i| ≤ N) :
    truncR N f z = f z := by
  unfold truncR; rw [if_pos h]

lemma truncR_val {N : ℝ} {f : (V → ℝ) → WithTop ℝ} {z : V → ℝ} {a : ℝ}
    (h : truncR N f z = (a : WithTop ℝ)) : (∀ i, |z i| ≤ N) ∧ f z = (a : WithTop ℝ) := by
  unfold truncR at h
  split_ifs at h with hb
  · exact ⟨hb, h⟩
  · exact absurd h WithTop.top_ne_coe

lemma truncR_lsc (N : ℝ) {f : (V → ℝ) → WithTop ℝ} (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous (truncR N f) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro C
  induction C using WithTop.recTopCoe with
  | top =>
    have : truncR N f ⁻¹' Set.Iic ⊤ = Set.univ := by ext z; simp
    rw [this]; exact isClosed_univ
  | coe c =>
    have heq : truncR N f ⁻¹' Set.Iic (c : WithTop ℝ) =
        (⋂ i : V, {z : V → ℝ | |z i| ≤ N}) ∩ (f ⁻¹' Set.Iic (c : WithTop ℝ)) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, truncR]
      split_ifs with h
      · simp [h]
      · simp [h]
    rw [heq]
    refine IsClosed.inter ?_ (hlsc.isClosed_preimage (c : WithTop ℝ))
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const

lemma truncR_convex (N : ℝ) {f : (V → ℝ) → WithTop ℝ} (hconv : IsConvexWithTop f) :
    IsConvexWithTop (truncR N f) := by
  intro x y t ht0 ht1
  by_cases ht_zero : t = 0
  · subst ht_zero
    have heq : (fun v => 0 * x v + (1 - 0) * y v) = y := by funext v; ring
    have hx0 : PosScalarMul 0 (truncR N f x) = 0 := by
      induction truncR N f x using WithTop.recTopCoe <;> simp [PosScalarMul]
    have hy1 : PosScalarMul (1 - 0) (truncR N f y) = truncR N f y := by
      induction truncR N f y using WithTop.recTopCoe <;> simp [PosScalarMul]
    rw [heq, hx0, hy1, zero_add]
  by_cases ht_one : t = 1
  · subst ht_one
    have heq : (fun v => 1 * x v + (1 - 1) * y v) = x := by funext v; ring
    have hx1 : PosScalarMul 1 (truncR N f x) = truncR N f x := by
      induction truncR N f x using WithTop.recTopCoe <;> simp [PosScalarMul]
    have hy0 : PosScalarMul (1 - 1) (truncR N f y) = 0 := by
      induction truncR N f y using WithTop.recTopCoe <;> simp [PosScalarMul]
    rw [heq, hx1, hy0, add_zero]
  have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
  have ht1_pos : 0 < 1 - t := by linarith [lt_of_le_of_ne ht1 ht_one]
  by_cases hx : truncR N f x = ⊤
  · rw [hx]; simp [PosScalarMul, if_neg ht_pos.ne']
  by_cases hy : truncR N f y = ⊤
  · rw [hy]; simp [PosScalarMul, if_neg ht1_pos.ne']
  obtain ⟨hbx, hx'⟩ := truncR_ne_top.1 hx
  obtain ⟨hby, hy'⟩ := truncR_ne_top.1 hy
  have hbz : ∀ i, |t * x i + (1 - t) * y i| ≤ N := fun i => by
    calc |t * x i + (1 - t) * y i|
        ≤ |t * x i| + |(1 - t) * y i| := abs_add_le _ _
      _ = t * |x i| + (1 - t) * |y i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht1_pos.le]
      _ ≤ t * N + (1 - t) * N := add_le_add (mul_le_mul_of_nonneg_left (hbx i) ht0)
          (mul_le_mul_of_nonneg_left (hby i) ht1_pos.le)
      _ = N := by ring
  rw [truncR_eq hbz, truncR_eq hbx, truncR_eq hby]
  exact hconv x y t ht0 ht1

lemma truncR_mexc (N : ℝ) {f : (V → ℝ) → WithTop ℝ} (hm : MExchangeAxiomR f) :
    MExchangeAxiomR (truncR N f) := by
  intro x hx y hy u hu
  obtain ⟨hbx, hx'⟩ := truncR_ne_top.1 hx
  obtain ⟨hby, hy'⟩ := truncR_ne_top.1 hy
  obtain ⟨v, hv, α0, hα0, hex⟩ := hm x hx' y hy' u hu
  change y u < x u at hu
  change x v < y v at hv
  have huv : u ≠ v := fun h => by subst h; linarith
  let α1 : ℝ := min α0 (min ((x u - y u) / 2) ((y v - x v) / 2))
  have hα1_pos : 0 < α1 := lt_min hα0 (lt_min (by linarith) (by linarith))
  refine ⟨v, hv, α1, hα1_pos, fun α hα0' hα_le => ?_⟩
  have hα_α0 : α ≤ α0 := hα_le.trans (min_le_left _ _)
  have htu : 2 * α ≤ x u - y u := by
    have : α ≤ (x u - y u) / 2 := hα_le.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have htv : 2 * α ≤ y v - x v := by
    have : α ≤ (y v - x v) / 2 := hα_le.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hx_box : x ∈ Set.Icc (fun _ => -N) (fun _ => N) :=
    ⟨fun i => (abs_le.1 (hbx i)).1, fun i => (abs_le.1 (hbx i)).2⟩
  have hy_box : y ∈ Set.Icc (fun _ => -N) (fun _ => N) :=
    ⟨fun i => (abs_le.1 (hby i)).1, fun i => (abs_le.1 (hby i)).2⟩
  obtain ⟨hx'_box, hy'_box, -⟩ := step_in_box huv hx_box hy_box hα0' htu htv
  have hbx' : ∀ i, |x i - α * (IndicatorVec ({u} : Finset V) i - IndicatorVec ({v} : Finset V) i : ℝ)| ≤ N :=
    fun i => abs_le.2 ⟨hx'_box.1 i, hx'_box.2 i⟩
  have hby' : ∀ i, |y i + α * (IndicatorVec ({u} : Finset V) i - IndicatorVec ({v} : Finset V) i : ℝ)| ≤ N :=
    fun i => abs_le.2 ⟨hy'_box.1 i, hy'_box.2 i⟩
  rw [truncR_eq hbx, truncR_eq hby, truncR_eq hbx', truncR_eq hby']
  exact hex α hα0' hα_α0

lemma truncR_conj_ne_top {N : ℝ} {f : (V → ℝ) → WithTop ℝ} (hlsc : LowerSemicontinuous f)
    (hne : (DomR (truncR N f)).Nonempty) (p : V → ℝ) :
    ConvexConjugateRW (truncR N f) p ≠ ⊤ := by
  have hB_compact : IsCompact (Set.Icc (fun _ : V => -N) (fun _ : V => N)) := isCompact_Icc
  obtain ⟨M0, hM0⟩ := lsc_bddBelow_on_compact hlsc hB_compact
  let C : ℝ := (∑ i : V, |p i| * N) - M0
  have hle : ConvexConjugateRW (truncR N f) p ≤ (C : WithTop ℝ) := by
    refine cc_le hne fun z a hz => ?_
    obtain ⟨hbz, hfz⟩ := truncR_val hz
    have hz_box : z ∈ Set.Icc (fun _ : V => -N) (fun _ : V => N) :=
      ⟨fun i => (abs_le.1 (hbz i)).1, fun i => (abs_le.1 (hbz i)).2⟩
    have hfz_ne : f z ≠ ⊤ := by rw [hfz]; exact WithTop.coe_ne_top
    have ha_ge : M0 ≤ a := by rw [← rv_of_eq hfz]; exact hM0 z hz_box hfz_ne
    have hsum_le : ∑ i : V, p i * z i ≤ ∑ i : V, |p i| * N := by
      refine Finset.sum_le_sum fun i _ => ?_
      calc p i * z i ≤ |p i * z i| := le_abs_self _
        _ = |p i| * |z i| := abs_mul _ _
        _ ≤ |p i| * N := mul_le_mul_of_nonneg_left (hbz i) (abs_nonneg _)
    dsimp [C]
    linarith
  exact ne_of_lt (hle.trans_lt (WithTop.coe_lt_top C))

lemma abs_le_sum3_R (a b c : V → ℝ) (i : V) :
    |a i| ≤ ∑ j, (|a j| + |b j| + |c j|) ∧ |b i| ≤ ∑ j, (|a j| + |b j| + |c j|) ∧
      |c i| ≤ ∑ j, (|a j| + |b j| + |c j|) := by
  have h := Finset.single_le_sum (f := fun j => |a j| + |b j| + |c j|)
    (fun j _ => by positivity) (Finset.mem_univ i)
  have := abs_nonneg (a i); have := abs_nonneg (b i); have := abs_nonneg (c i)
  refine ⟨by linarith, by linarith, by linarith⟩

theorem mconv_sbf {f : (V → ℝ) → WithTop ℝ} (hf : IsClosedProperConvex f)
    (hm : MExchangeAxiomR f) : SBFR (ConvexConjugateRW f) := by
  intro p q
  rw [ge_iff_le]
  by_cases hp : ConvexConjugateRW f p = ⊤
  · rw [hp, top_add]; exact le_top
  by_cases hq : ConvexConjugateRW f q = ⊤
  · rw [hq, add_top]; exact le_top
  obtain ⟨y0, hy0⟩ := hf.1
  obtain ⟨b0, hb0⟩ := WithTop.ne_top_iff_exists.1 hy0
  have key : ∀ z1 z2 : V → ℝ, ∀ a1 a2 : ℝ,
      f z1 = (a1 : WithTop ℝ) → f z2 = (a2 : WithTop ℝ) →
      ((∑ i, (p ⊔ q) i * z1 i) - a1) + ((∑ i, (p ⊓ q) i * z2 i) - a2) ≤
        rv (ConvexConjugateRW f) p + rv (ConvexConjugateRW f) q := by
    intro z1 z2 a1 a2 hz1 hz2
    let N : ℝ := ∑ j : V, (|z1 j| + |z2 j| + |y0 j|)
    have hb := fun i => abs_le_sum3_R z1 z2 y0 i
    have hbz1 : ∀ i, |z1 i| ≤ N := fun i => (hb i).1
    have hbz2 : ∀ i, |z2 i| ≤ N := fun i => (hb i).2.1
    have hby0 : ∀ i, |y0 i| ≤ N := fun i => (hb i).2.2
    have hneN : (DomR (truncR N f)).Nonempty :=
      ⟨y0, truncR_ne_top.2 ⟨hby0, hy0⟩⟩
    have hlscN := truncR_lsc N hf.2.1
    have hconvN := truncR_convex N hf.2.2
    have hmN := truncR_mexc N hm
    have hfinN : ∀ r : V → ℝ, ConvexConjugateRW (truncR N f) r ≠ ⊤ :=
      fun r => truncR_conj_ne_top hf.2.1 hneN r
    let G : (V → ℝ) → ℝ := fun r => rv (ConvexConjugateRW (truncR N f)) r
    have hlocG : ∀ r : V → ℝ, ∀ u v : V, u ≠ v → ∀ cu dv : ℝ, 0 ≤ cu → 0 ≤ dv →
        G (r + singleV u cu + singleV v dv) + G r ≤ G (r + singleV u cu) + G (r + singleV v dv) := by
      intro r u v huv cu dv hcu hdv
      have hpair : ∀ x y : V → ℝ, ∀ ax ay : ℝ,
          truncR N f x = (ax : WithTop ℝ) → truncR N f y = (ay : WithTop ℝ) →
          ((∑ i, (r + singleV u cu + singleV v dv) i * x i) - ax) + ((∑ i, r i * y i) - ay) ≤
            G (r + singleV u cu) + G (r + singleV v dv) := by
        intro x y ax ay hx hy
        have hx' : truncR N f x ≠ ⊤ := by rw [hx]; exact WithTop.coe_ne_top
        have hy' : truncR N f y ≠ ⊤ := by rw [hy]; exact WithTop.coe_ne_top
        have h := g_two_coord hlscN hconvN hmN r huv hcu hdv (hfinN _) (hfinN _) hx' hy'
        rw [rv_of_eq hx, rv_of_eq hy] at h
        exact h
      have h1 : ConvexConjugateRW (truncR N f) (r + singleV u cu + singleV v dv) ≤
          ((G (r + singleV u cu) + G (r + singleV v dv) - ((∑ i, r i * y0 i) - b0) : ℝ) : WithTop ℝ) := by
        refine cc_le hneN fun x ax hx => ?_
        have hy0_N : truncR N f y0 = (b0 : WithTop ℝ) := by rw [truncR_eq hby0, hb0]
        linarith [hpair x y0 ax b0 hx hy0_N]
      have h2 : ConvexConjugateRW (truncR N f) r ≤
          ((G (r + singleV u cu) + G (r + singleV v dv) - G (r + singleV u cu + singleV v dv) : ℝ) : WithTop ℝ) := by
        refine cc_le hneN fun y ay hy => ?_
        have h3 : ConvexConjugateRW (truncR N f) (r + singleV u cu + singleV v dv) ≤
            ((G (r + singleV u cu) + G (r + singleV v dv) - ((∑ i, r i * y i) - ay) : ℝ) : WithTop ℝ) :=
          cc_le hneN fun x ax hx => by linarith [hpair x y ax ay hx hy]
        rw [rv_spec (hfinN (r + singleV u cu + singleV v dv)), WithTop.coe_le_coe] at h3
        dsimp [G]
        linarith
      rw [rv_spec (hfinN r), WithTop.coe_le_coe] at h2
      dsimp [G] at h2 ⊢
      linarith
    have hsbfG := lattice_sbf_R G hlocG p q
    have hGe_p : G p ≤ rv (ConvexConjugateRW f) p := by
      have hle : ConvexConjugateRW (truncR N f) p ≤ ((rv (ConvexConjugateRW f) p : ℝ) : WithTop ℝ) :=
        cc_le hneN fun z a hz => cc_bdd (rv_spec hp) (truncR_val hz).2
      rw [rv_spec (hfinN p), WithTop.coe_le_coe] at hle
      exact hle
    have hGe_q : G q ≤ rv (ConvexConjugateRW f) q := by
      have hle : ConvexConjugateRW (truncR N f) q ≤ ((rv (ConvexConjugateRW f) q : ℝ) : WithTop ℝ) :=
        cc_le hneN fun z a hz => cc_bdd (rv_spec hq) (truncR_val hz).2
      rw [rv_spec (hfinN q), WithTop.coe_le_coe] at hle
      exact hle
    have hz1_N : truncR N f z1 = (a1 : WithTop ℝ) := by rw [truncR_eq hbz1, hz1]
    have hz2_N : truncR N f z2 = (a2 : WithTop ℝ) := by rw [truncR_eq hbz2, hz2]
    have hge1 := cc_bdd (rv_spec (hfinN (p ⊔ q))) hz1_N
    have hge2 := cc_bdd (rv_spec (hfinN (p ⊓ q))) hz2_N
    dsimp [G] at hsbfG hGe_p hGe_q
    linarith
  have hsup_le : ConvexConjugateRW f (p ⊔ q) ≤
      ((rv (ConvexConjugateRW f) p + rv (ConvexConjugateRW f) q - ((∑ i, (p ⊓ q) i * y0 i) - b0) : ℝ) : WithTop ℝ) :=
    cc_le hf.1 fun z1 a1 hz1 => by linarith [key z1 y0 a1 b0 hz1 hb0.symm]
  have hsup_ne : ConvexConjugateRW f (p ⊔ q) ≠ ⊤ :=
    ne_of_lt (hsup_le.trans_lt (WithTop.coe_lt_top _))
  have hinf_le : ConvexConjugateRW f (p ⊓ q) ≤
      ((rv (ConvexConjugateRW f) p + rv (ConvexConjugateRW f) q - rv (ConvexConjugateRW f) (p ⊔ q) : ℝ) : WithTop ℝ) := by
    refine cc_le hf.1 fun z2 a2 hz2 => ?_
    have h1 : ConvexConjugateRW f (p ⊔ q) ≤
        ((rv (ConvexConjugateRW f) p + rv (ConvexConjugateRW f) q - ((∑ i, (p ⊓ q) i * z2 i) - a2) : ℝ) : WithTop ℝ) :=
      cc_le hf.1 fun z1 a1 hz1 => by linarith [key z1 z2 a1 a2 hz1 hz2]
    rw [rv_spec hsup_ne, WithTop.coe_le_coe] at h1
    linarith
  rw [rv_spec hp, rv_spec hq, rv_spec hsup_ne]
  refine (add_le_add le_rfl hinf_le).trans ?_
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  linarith

end NonPolyConjAux

open DiscreteConvex.ConjugacyDualityB
open NonPolyConjAux

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℝ) → WithTop ℝ) (hf : IsClosedProperConvex f) :
    MExchangeAxiomR f ↔
      ∃ g : (V → ℝ) → WithTop ℝ,
        IsClosedProperConvex g ∧ SBFR g ∧ TRFR g ∧
          f = ConvexConjugateRW g := by
  constructor
  · intro hm
    exact ⟨ConvexConjugateRW f, closed_proper_conj hf, mconv_sbf hf hm, mconv_trf hf hm,
      (closed_proper_biconj hf).symm⟩
  · rintro ⟨g, hg, hs, ht, rfl⟩
    exact lconv_mexc hg hs ht




