-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.conjugacy_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T03:50:00.847045+00:00
-- url     : https://prove2.me/submissions/c76c29c0-d64b-4dcb-8277-3c099ecc7b8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvexR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvexR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateRW
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsPolyhedralConvex
import Theorems.Thm_DiscreteConvex_ConjugacyDualityB_nonpolyhedral_conjugacy_theorem

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ConjThmAux

open DiscreteConvex.ConjugacyDualityB
open Classical
open scoped Pointwise BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

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
      simp [ Prod.fst_sum, Prod.smul_fst]
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
      induction ConvexConjugateRW f p using WithTop.recTopCoe with
      | top => simp [PosScalarMul]
      | coe r => simp [PosScalarMul]
    have hq1 : PosScalarMul (1 - 0) (ConvexConjugateRW f q) = ConvexConjugateRW f q := by
      induction ConvexConjugateRW f q using WithTop.recTopCoe with
      | top => simp [PosScalarMul]
      | coe r => simp [PosScalarMul]
    rw [heq, hp0, hq1, zero_add]
  by_cases ht_one : t = 1
  · subst ht_one
    have heq : (fun v => 1 * p v + (1 - 1) * q v) = p := by funext v; ring
    have hp1 : PosScalarMul 1 (ConvexConjugateRW f p) = ConvexConjugateRW f p := by
      induction ConvexConjugateRW f p using WithTop.recTopCoe with
      | top => simp [PosScalarMul]
      | coe r => simp [PosScalarMul]
    have hq0 : PosScalarMul (1 - 1) (ConvexConjugateRW f q) = 0 := by
      induction ConvexConjugateRW f q using WithTop.recTopCoe with
      | top => simp [PosScalarMul]
      | coe r => simp [PosScalarMul]
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

lemma polyhedral_isClosedProper {f : (V → ℝ) → WithTop ℝ} (hf : IsPolyhedralConvex f)
    (hne : (DomR f).Nonempty) : IsClosedProperConvex f := by
  obtain ⟨m, a, b, hab⟩ := hf
  have hmem : ∀ (x : V → ℝ) (r : ℝ),
      f x ≤ (r : WithTop ℝ) ↔ ∀ i : Fin m, a i none * r + ∑ v : V, a i (some v) * x v ≤ b i := by
    intro x r
    let P : Option V → ℝ := fun o => Option.elim o r x
    have hP : f x ≤ (r : WithTop ℝ) ↔
        P ∈ {p : Option V → ℝ | f (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)} := by
      simp [P]
    rw [hP, hab]
    simp only [Set.mem_setOf_eq, Fintype.sum_option, P, Option.elim]
  refine ⟨hne, ?_, ?_⟩
  · rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro C
    induction C using WithTop.recTopCoe with
    | top =>
      have : f ⁻¹' Set.Iic ⊤ = Set.univ := by ext x; simp
      rw [this]
      exact isClosed_univ
    | coe c =>
      have heq : f ⁻¹' Set.Iic (c : WithTop ℝ) =
          ⋂ i : Fin m, {x : V → ℝ | a i none * c + ∑ v : V, a i (some v) * x v ≤ b i} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_setOf_eq]
        exact hmem x c
      rw [heq]
      refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
      refine Continuous.add continuous_const ?_
      exact continuous_finset_sum _ fun v _ => continuous_const.mul (continuous_apply v)
  · intro x y t ht0 ht1
    by_cases ht_zero : t = 0
    · subst ht_zero
      have heq : (fun v => 0 * x v + (1 - 0) * y v) = y := by funext v; ring
      have hx0 : PosScalarMul 0 (f x) = 0 := by
        induction f x using WithTop.recTopCoe <;> simp [PosScalarMul]
      have hy1 : PosScalarMul (1 - 0) (f y) = f y := by
        induction f y using WithTop.recTopCoe <;> simp [PosScalarMul]
      rw [heq, hx0, hy1, zero_add]
    by_cases ht_one : t = 1
    · subst ht_one
      have heq : (fun v => 1 * x v + (1 - 1) * y v) = x := by funext v; ring
      have hx1 : PosScalarMul 1 (f x) = f x := by
        induction f x using WithTop.recTopCoe <;> simp [PosScalarMul]
      have hy0 : PosScalarMul (1 - 1) (f y) = 0 := by
        induction f y using WithTop.recTopCoe <;> simp [PosScalarMul]
      rw [heq, hx1, hy0, add_zero]
    have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
    have ht1_pos : 0 < 1 - t := by linarith [lt_of_le_of_ne ht1 ht_one]
    induction hfx : f x using WithTop.recTopCoe with
    | top => simp only [PosScalarMul, if_neg ht_pos.ne', top_add, le_top]
    | coe rx =>
      induction hfy : f y using WithTop.recTopCoe with
      | top => simp only [PosScalarMul, if_neg ht1_pos.ne', add_top, le_top]
      | coe ry =>
        simp only [PosScalarMul, ← WithTop.coe_add]
        rw [hmem]
        have hx_le := (hmem x rx).1 (by rw [hfx])
        have hy_le := (hmem y ry).1 (by rw [hfy])
        intro i
        have hsum : ∑ v : V, a i (some v) * (t * x v + (1 - t) * y v) =
            t * (∑ v : V, a i (some v) * x v) + (1 - t) * (∑ v : V, a i (some v) * y v) := by
          have : ∀ v : V, a i (some v) * (t * x v + (1 - t) * y v) =
              t * (a i (some v) * x v) + (1 - t) * (a i (some v) * y v) := fun v => by ring
          simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsum]
        nlinarith [hx_le i, hy_le i]

lemma sSup_eq_of {S1 S2 : Set EReal} (h1 : ∀ a ∈ S1, a ≤ sSup S2) (h2 : ∀ b ∈ S2, b ≤ sSup S1) :
    sSup S1 = sSup S2 :=
  le_antisymm (sSup_le h1) (sSup_le h2)

lemma lift_M_conj (f : (V → ℝ) → WithTop ℝ) :
    ConvexConjugateRW (LiftedFunctionR f) = LiftedFunctionLR (ConvexConjugateRW f) := by
  funext P
  show ConvexConjugateRW (LiftedFunctionR f) P = ConvexConjugateRW f (fun v => P (some v) - P none)
  rw [cc_unfold, cc_unfold]
  congr 1
  apply sSup_eq_of
  · rintro t ⟨X, rfl⟩
    by_cases hX : X none = -(∑ v : V, X (some v))
    · apply le_sSup
      refine ⟨fun v => X (some v), ?_⟩
      have e1 : LiftedFunctionR f X = f (fun v => X (some v)) := by
        simp only [LiftedFunctionR, if_pos hX]
      rw [e1]
      congr 2
      rw [Fintype.sum_option, hX]
      rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    · have e1 : LiftedFunctionR f X = ⊤ := by simp only [LiftedFunctionR, if_neg hX]
      rw [term_top e1]; exact bot_le
  · rintro t ⟨x, rfl⟩
    apply le_sSup
    refine ⟨fun o => Option.elim o (-(∑ v, x v)) x, ?_⟩
    have e1 : LiftedFunctionR f (fun o => Option.elim o (-(∑ v, x v)) x) = f x := by
      simp [LiftedFunctionR]
    rw [e1]
    congr 2
    rw [Fintype.sum_option]
    simp only [Option.elim]
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring

lemma lift_L_conj (g : (V → ℝ) → WithTop ℝ) :
    ConvexConjugateRW (LiftedFunctionLR g) = LiftedFunctionR (ConvexConjugateRW g) := by
  funext X
  by_cases hX : X none = -(∑ v : V, X (some v))
  · have e0 : LiftedFunctionR (ConvexConjugateRW g) X = ConvexConjugateRW g (fun v => X (some v)) := by
      simp only [LiftedFunctionR, if_pos hX]
    rw [e0, cc_unfold, cc_unfold]
    congr 1
    apply sSup_eq_of
    · rintro t ⟨P, rfl⟩
      apply le_sSup
      refine ⟨fun v => P (some v) - P none, ?_⟩
      show _ = _ - ToEReal (g (fun v => P (some v) - P none))
      congr 2
      rw [Fintype.sum_option, hX]
      rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    · rintro t ⟨p, rfl⟩
      apply le_sSup
      refine ⟨fun o => Option.elim o 0 p, ?_⟩
      show _ = _ - ToEReal (g (fun v => p v - 0))
      have e : (fun v => p v - 0) = p := by funext v; ring
      rw [e]
      congr 2
      rw [Fintype.sum_option]
      simp
  · have e0 : LiftedFunctionR (ConvexConjugateRW g) X = ⊤ := by
      simp only [LiftedFunctionR, if_neg hX]
    rw [e0]
    by_cases hne : ∃ p, g p ≠ ⊤
    · obtain ⟨p0, hp0⟩ := hne
      obtain ⟨r0, hr0⟩ := WithTop.ne_top_iff_exists.1 hp0
      let s : ℝ := X none + ∑ v, X (some v)
      have hs : s ≠ 0 := by intro h; apply hX; simp only [s] at h; linarith
      let C0 : ℝ := ∑ v, X (some v) * p0 v
      apply cc_top_of_unbdd
      intro M
      let t : ℝ := (M - C0 + r0) / s
      refine ⟨fun o => Option.elim o t (fun v => p0 v + t), r0, ?_, ?_⟩
      · show g (fun v => (p0 v + t) - t) = (r0 : WithTop ℝ)
        have e : (fun v => (p0 v + t) - t) = p0 := by funext v; ring
        rw [e, hr0]
      · have e : (∑ o : Option V, X o * Option.elim o t (fun v => p0 v + t)) =
            s * t + C0 := by
          rw [Fintype.sum_option]
          simp only [Option.elim, s, C0]
          rw [add_mul, Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [e]
        have hst : s * t = M - C0 + r0 := mul_div_cancel₀ _ hs
        linarith
    · push_neg at hne
      exact congrFun (cc_empty (fun P => hne _)) X

lemma lift_inj :
    Function.Injective (LiftedFunctionR (V := V)) ∧ Function.Injective (LiftedFunctionLR (V := V)) := by
  constructor
  · intro f g h; funext x
    have := congrFun h (fun o => Option.elim o (-(∑ v, x v)) x)
    simpa [LiftedFunctionR] using this
  · intro f g h; funext x
    have := congrFun h (fun o => Option.elim o 0 x)
    simpa [LiftedFunctionLR] using this

lemma lift_polyhedral_M {f : (V → ℝ) → WithTop ℝ} (hf : IsPolyhedralConvex f) :
    IsPolyhedralConvex (LiftedFunctionR f) := by
  obtain ⟨m, a, b, hab⟩ := hf
  refine ⟨m + 2,
    Fin.addCases
      (fun i o => match o with
        | none => a i none
        | some none => 0
        | some (some v) => a i (some v))
      (fun j o => if j.1 = 0 then
        match o with
        | none => 0
        | some _ => 1
      else
        match o with
        | none => 0
        | some _ => -1),
    Fin.addCases b (fun _ => 0), ?_⟩
  ext P
  simp only [Set.mem_setOf_eq, LiftedFunctionR]
  let Q : Option V → ℝ := fun o => Option.elim o (P none) (fun v => P (some (some v)))
  have hQ : f (fun v => P (some (some v))) ≤ ((P none : ℝ) : WithTop ℝ) ↔
      ∀ i : Fin m, ∑ w : Option V, a i w * Q w ≤ b i := by
    have : f (fun v => P (some (some v))) ≤ ((P none : ℝ) : WithTop ℝ) ↔
        Q ∈ {p : Option V → ℝ | f (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)} := by
      simp [Q]
    rw [this, hab, Set.mem_setOf_eq]
  constructor
  · intro hP i
    by_cases hsum : P (some none) = -(∑ v : V, P (some (some v)))
    · rw [if_pos hsum] at hP
      have hQi := (hQ.1 hP)
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]
        rw [Fintype.sum_option, Fintype.sum_option]
        simpa [Q, Fintype.sum_option] using hQi i
      · simp only [Fin.addCases_right]
        fin_cases j <;>
        · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero]
          rw [Fintype.sum_option, Fintype.sum_option]
          simp only [zero_mul, one_mul, neg_mul, zero_add, Finset.sum_neg_distrib]
          linarith
    · rw [if_neg hsum] at hP
      exact absurd hP (by simp)
  · intro hall
    have hpos := hall (Fin.natAdd m ⟨0, by decide⟩)
    have hneg := hall (Fin.natAdd m ⟨1, by decide⟩)
    simp only [Fin.addCases_right, ↓reduceIte, one_ne_zero] at hpos hneg
    rw [Fintype.sum_option, Fintype.sum_option] at hpos hneg
    simp only [zero_mul, one_mul, neg_mul, zero_add, Finset.sum_neg_distrib] at hpos hneg
    have hsum : P (some none) = -(∑ v : V, P (some (some v))) := by linarith
    rw [if_pos hsum, hQ]
    intro i
    have hi := hall (Fin.castAdd 2 i)
    simp only [Fin.addCases_left] at hi
    rw [Fintype.sum_option, Fintype.sum_option] at hi
    rw [Fintype.sum_option]
    simpa [Q] using hi

lemma lift_polyhedral_L {g : (V → ℝ) → WithTop ℝ} (hg : IsPolyhedralConvex g) :
    IsPolyhedralConvex (LiftedFunctionLR g) := by
  obtain ⟨m, a, b, hab⟩ := hg
  refine ⟨m,
    fun i o => match o with
      | none => a i none
      | some none => - ∑ v : V, a i (some v)
      | some (some v) => a i (some v),
    b, ?_⟩
  ext P
  simp only [Set.mem_setOf_eq, LiftedFunctionLR]
  let Q : Option V → ℝ := fun o => Option.elim o (P none) (fun v => P (some (some v)) - P (some none))
  have hQ : g (fun v => P (some (some v)) - P (some none)) ≤ ((P none : ℝ) : WithTop ℝ) ↔
      Q ∈ {p : Option V → ℝ | g (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)} := by
    simp [Q]
  rw [hQ, hab, Set.mem_setOf_eq]
  apply forall_congr'; intro i
  rw [Fintype.sum_option, Fintype.sum_option, Fintype.sum_option]
  simp only [Q, Option.elim]
  have hsum : - (∑ v : V, a i (some v)) * P (some none) + ∑ v : V, a i (some v) * P (some (some v)) =
      ∑ v : V, a i (some v) * (P (some (some v)) - P (some none)) := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => by ring
  rw [hsum]

theorem part1 (f : (V → ℝ) → WithTop ℝ) (hf : IsPolyhedralConvex f) (hM : MExchangeAxiomR f) :
    SBFR (ConvexConjugateRW f) ∧ TRFR (ConvexConjugateRW f) ∧
      ConvexConjugateRW (ConvexConjugateRW f) = f := by
  by_cases hne : (DomR f).Nonempty
  · have hclosed : IsClosedProperConvex f := polyhedral_isClosedProper hf hne
    obtain ⟨g, hg_closed, hSBF, hTRF, rfl⟩ :=
      (nonpolyhedral_conjugacy_theorem f hclosed).1 hM
    have hbg : ConvexConjugateRW (ConvexConjugateRW g) = g := closed_proper_biconj hg_closed
    rw [hbg]
    exact ⟨hSBF, hTRF, rfl⟩
  · have htop : ∀ x, f x = ⊤ := fun x => by
      by_contra hx; exact hne ⟨x, hx⟩
    have hf_eq : f = fun _ => ⊤ := funext htop
    have hcc : ConvexConjugateRW f = fun _ => ⊤ := cc_empty htop
    rw [hcc, cc_empty (fun _ => rfl), hf_eq]
    refine ⟨fun _ _ => le_top, ⟨0, fun _ _ => by simp⟩, rfl⟩

theorem part2 (g : (V → ℝ) → WithTop ℝ) (hg : IsPolyhedralConvex g) (hL : SBFR g ∧ TRFR g) :
    MExchangeAxiomR (ConvexConjugateRW g) ∧
      ConvexConjugateRW (ConvexConjugateRW g) = g := by
  by_cases hne : (DomR g).Nonempty
  · have hg_closed : IsClosedProperConvex g := polyhedral_isClosedProper hg hne
    have hf_closed : IsClosedProperConvex (ConvexConjugateRW g) := closed_proper_conj hg_closed
    have hbg : ConvexConjugateRW (ConvexConjugateRW g) = g := closed_proper_biconj hg_closed
    have hM : MExchangeAxiomR (ConvexConjugateRW g) :=
      (nonpolyhedral_conjugacy_theorem (ConvexConjugateRW g) hf_closed).2
        ⟨g, hg_closed, hL.1, hL.2, rfl⟩
    exact ⟨hM, hbg⟩
  · have htop : ∀ p, g p = ⊤ := fun p => by
      by_contra hp; exact hne ⟨p, hp⟩
    have hg_eq : g = fun _ => ⊤ := funext htop
    have hcc : ConvexConjugateRW g = fun _ => ⊤ := cc_empty htop
    rw [hcc, cc_empty (fun _ => rfl), hg_eq]
    refine ⟨fun x hx => absurd rfl hx, rfl⟩

theorem part3 (f : (V → ℝ) → WithTop ℝ) (hf : IsPolyhedralConvex f) (hM : MNaturalConvexR f) :
    LNaturalConvexR (ConvexConjugateRW f) ∧ ConvexConjugateRW (ConvexConjugateRW f) = f := by
  have h1 := part1 (LiftedFunctionR f) (lift_polyhedral_M hf) hM
  rw [lift_M_conj] at h1
  have h2 := h1.2.2
  rw [lift_L_conj] at h2
  exact ⟨⟨h1.1, h1.2.1⟩, lift_inj.1 h2⟩

theorem part4 (g : (V → ℝ) → WithTop ℝ) (hg : IsPolyhedralConvex g) (hL : LNaturalConvexR g) :
    MNaturalConvexR (ConvexConjugateRW g) ∧ ConvexConjugateRW (ConvexConjugateRW g) = g := by
  have h1 := part2 (LiftedFunctionLR g) (lift_polyhedral_L hg) hL
  rw [lift_L_conj] at h1
  have h2 := h1.2
  rw [lift_M_conj] at h2
  exact ⟨h1.1, lift_inj.2 h2⟩

end ConjThmAux

open DiscreteConvex.ConjugacyDualityB in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℝ) → WithTop ℝ, IsPolyhedralConvex f → MExchangeAxiomR f →
      SBFR (ConvexConjugateRW f) ∧ TRFR (ConvexConjugateRW f) ∧
        ConvexConjugateRW (ConvexConjugateRW f) = f) ∧
    (∀ g : (V → ℝ) → WithTop ℝ, IsPolyhedralConvex g → (SBFR g ∧ TRFR g) →
      MExchangeAxiomR (ConvexConjugateRW g) ∧
        ConvexConjugateRW (ConvexConjugateRW g) = g) ∧
    (∀ f : (V → ℝ) → WithTop ℝ, IsPolyhedralConvex f → MNaturalConvexR f →
      LNaturalConvexR (ConvexConjugateRW f) ∧ ConvexConjugateRW (ConvexConjugateRW f) = f) ∧
    (∀ g : (V → ℝ) → WithTop ℝ, IsPolyhedralConvex g → LNaturalConvexR g →
      MNaturalConvexR (ConvexConjugateRW g) ∧ ConvexConjugateRW (ConvexConjugateRW g) = g) :=
  ⟨ConjThmAux.part1, ConjThmAux.part2, ConjThmAux.part3, ConjThmAux.part4⟩
