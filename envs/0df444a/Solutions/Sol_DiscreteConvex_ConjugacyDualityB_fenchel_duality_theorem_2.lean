-- Prove2me | solution 2 for DiscreteConvex.ConjugacyDualityB.fenchel_duality_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:01:55.920166+00:00
-- url     : https://prove2.me/submissions/015f89ab-c40e-4b99-bc90-4ea49bb0a4cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConcaveConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomERealConcave
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_InfDiff
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SupDualGap
import Theorems.Thm_DiscreteConvex_ConjugacyDualityB_m_separation_theorem
import Theorems.Thm_DiscreteConvex_ConjugacyDualityB_l_separation_theorem

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityB

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

variable {V : Type*} [Fintype V] [DecidableEq V]

private def shiftFn {α : Type*} (f : α → WithTop ℝ) (c : ℝ) : α → WithTop ℝ :=
  fun x => f x + (c : WithTop ℝ)

private lemma domZ_shift {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → ℤ) → WithTop ℝ) (c : ℝ) :
    DomZ (shiftFn f c) = DomZ f := by
  ext x
  simp [DomZ, shiftFn]

private lemma lifted_shift (f : (V → ℤ) → WithTop ℝ) (c : ℝ) :
    LiftedFunction (shiftFn f c) = shiftFn (LiftedFunction f) c := by
  ext x
  dsimp [LiftedFunction, shiftFn]
  split_ifs <;> simp

private lemma mExchange_shift {α : Type*} [Fintype α] [DecidableEq α]
    (F : (α → ℤ) → WithTop ℝ) (hF : MExchangeAxiom F) (c : ℝ) :
    MExchangeAxiom (shiftFn F c) := by
  intro x hx y hy u hu
  rw [domZ_shift] at hx hy
  rcases hF x hx y hy u hu with ⟨v, hv, hle⟩
  refine ⟨v, hv, ?_⟩
  dsimp [shiftFn]
  calc (F (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) + (c : WithTop ℝ)) +
        (F (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) + (c : WithTop ℝ))
    _ = (F (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) +
          F (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w)) +
        ((c : WithTop ℝ) + (c : WithTop ℝ)) := by ac_rfl
    _ ≤ (F x + F y) + ((c : WithTop ℝ) + (c : WithTop ℝ)) := add_le_add hle le_rfl
    _ = (F x + (c : WithTop ℝ)) + (F y + (c : WithTop ℝ)) := by ac_rfl

private lemma mnat_shift (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) (c : ℝ) :
    MNaturalConvex (shiftFn f c) := by
  unfold MNaturalConvex
  rw [lifted_shift]
  exact mExchange_shift (LiftedFunction f) hf c

private lemma sbf_shift {α : Type*} [Fintype α] [DecidableEq α]
    (G : (α → ℤ) → WithTop ℝ) (hG : SBF G) (c : ℝ) :
    SBF (shiftFn G c) := by
  intro p q
  dsimp [shiftFn]
  calc (G (p ⊔ q) + (c : WithTop ℝ)) + (G (p ⊓ q) + (c : WithTop ℝ))
    _ = (G (p ⊔ q) + G (p ⊓ q)) + ((c : WithTop ℝ) + (c : WithTop ℝ)) := by ac_rfl
    _ ≤ (G p + G q) + ((c : WithTop ℝ) + (c : WithTop ℝ)) := add_le_add (hG p q) le_rfl
    _ = (G p + (c : WithTop ℝ)) + (G q + (c : WithTop ℝ)) := by ac_rfl

private lemma trf_shift {α : Type*} [Fintype α] [DecidableEq α]
    (G : (α → ℤ) → WithTop ℝ) (hG : TRF G) (c : ℝ) :
    TRF (shiftFn G c) := by
  rcases hG with ⟨r, hr⟩
  refine ⟨r, fun p => ?_⟩
  dsimp [shiftFn]
  rw [hr p]
  ac_rfl

private lemma lnat_shift (g : (V → ℤ) → WithTop ℝ) (hg : LNaturalConvex g) (c : ℝ) :
    LNaturalConvex (shiftFn g c) :=
  ⟨sbf_shift (LiftedFunctionL g) hg.1 c, trf_shift (LiftedFunctionL g) hg.2 c⟩

private lemma toEReal_coe (r : ℝ) : ToEReal (r : WithTop ℝ) = (r : EReal) := rfl

private lemma toEReal_top : ToEReal (⊤ : WithTop ℝ) = (⊤ : EReal) := rfl

private lemma domEReal_conj_shift (f : (V → ℤ) → WithTop ℝ) (c : ℝ)
    {p : V → ℝ} (hp : p ∈ DomEReal (ConvexConjugateZR f)) :
    p ∈ DomEReal (ConvexConjugateZR (shiftFn f c)) := by
  have hne_top : ConvexConjugateZR f p ≠ ⊤ := hp
  have hex_bound : ∃ M : ℝ, ConvexConjugateZR f p ≤ (M : EReal) := by
    rcases eq_bot_or_bot_lt (ConvexConjugateZR f p) with hbot | hbot_lt
    · exact ⟨0, by rw [hbot]; exact bot_le⟩
    · lift ConvexConjugateZR f p to ℝ using ⟨hne_top, ne_of_gt hbot_lt⟩ with M hM
      exact ⟨M, le_rfl⟩
  rcases hex_bound with ⟨M, hM⟩
  have hle : ConvexConjugateZR (shiftFn f c) p ≤ ((M - c : ℝ) : EReal) := by
    unfold ConvexConjugateZR
    apply sSup_le
    rintro v ⟨x, rfl⟩
    have hx_le : ((∑ i, p i * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x) ≤ (M : EReal) := by
      refine (le_sSup ?_).trans hM
      exact ⟨x, rfl⟩
    cases hfx : f x with
    | top =>
      have htop : shiftFn f c x = ⊤ := by simp [shiftFn, hfx]
      rw [htop, toEReal_top]
      exact bot_le
    | coe rf =>
      have hsh : shiftFn f c x = ((rf + c : ℝ) : WithTop ℝ) := by
        dsimp [shiftFn]; rw [hfx, ← WithTop.coe_add]
      rw [hfx, toEReal_coe, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hx_le
      rw [hsh, toEReal_coe, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith
  intro htop
  rw [htop] at hle
  exact EReal.coe_ne_top (M - c) (top_le_iff.mp hle)

private lemma weak_duality (f h2 : (V → ℤ) → WithTop ℝ) :
    SupDualGap f h2 ≤ InfDiff f h2 := by
  unfold SupDualGap InfDiff
  apply sSup_le
  rintro u ⟨p, rfl⟩
  apply le_sInf
  rintro v ⟨x, rfl⟩
  cases hfx : f x with
  | top =>
    cases hhx : h2 x with
    | top =>
      rw [toEReal_top]; exact le_top
    | coe rh =>
      rw [toEReal_top, toEReal_coe]; exact le_top
  | coe rf =>
    cases hhx : h2 x with
    | top =>
      rw [toEReal_coe, toEReal_top]; exact le_top
    | coe rh =>
      let s : ℝ := ∑ i, p i * (x i : ℝ)
      have h1 : ((s - rf : ℝ) : EReal) ≤ ConvexConjugateZR f p := by
        unfold ConvexConjugateZR
        apply le_sSup
        refine ⟨x, ?_⟩
        rw [hfx, toEReal_coe, EReal.coe_sub]
      have h2_le : ConcaveConjugateZR h2 p ≤ ((s + rh : ℝ) : EReal) := by
        unfold ConcaveConjugateZR
        apply sInf_le
        refine ⟨x, ?_⟩
        rw [hhx, toEReal_coe, EReal.coe_add]
      have hsub : ConcaveConjugateZR h2 p - ConvexConjugateZR f p ≤
          ((s + rh : ℝ) : EReal) - ((s - rf : ℝ) : EReal) :=
        EReal.sub_le_sub h2_le h1
      refine hsub.trans ?_
      rw [toEReal_coe, toEReal_coe, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith

private lemma dual_bound_of_sep (f h2 : (V → ℤ) → WithTop ℝ) (delta alpha : ℝ) (p : V → ℝ)
    (h1 : ∀ x : V → ℤ, shiftFn f (-delta) x ≥ ((alpha + ∑ v, p v * (x v : ℝ) : ℝ) : WithTop ℝ))
    (h2_ineq : ∀ x : V → ℤ, ((alpha + ∑ v, p v * (x v : ℝ) : ℝ) : WithTop ℝ) + h2 x ≥ 0) :
    p ∈ DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2) ∧
      (delta : EReal) ≤ ConcaveConjugateZR h2 p - ConvexConjugateZR f p := by
  have hconj_le : ConvexConjugateZR f p ≤ ((-alpha - delta : ℝ) : EReal) := by
    unfold ConvexConjugateZR
    apply sSup_le
    rintro v ⟨x, rfl⟩
    have hx := h1 x
    change f x + ((-delta : ℝ) : WithTop ℝ) ≥ ((alpha + ∑ v, p v * (x v : ℝ) : ℝ) : WithTop ℝ) at hx
    cases hfx : f x with
    | top =>
      rw [toEReal_top]
      exact bot_le
    | coe rf =>
      rw [hfx, ← WithTop.coe_add] at hx
      have hx' : alpha + ∑ v, p v * (x v : ℝ) ≤ rf + -delta := by exact_mod_cast hx
      rw [toEReal_coe, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith
  have hconc_ge : ((-alpha : ℝ) : EReal) ≤ ConcaveConjugateZR h2 p := by
    unfold ConcaveConjugateZR
    apply le_sInf
    rintro v ⟨x, rfl⟩
    have hx := h2_ineq x
    cases hhx : h2 x with
    | top =>
      rw [toEReal_top]
      exact le_top
    | coe rh =>
      rw [hhx] at hx
      change (0 : WithTop ℝ) ≤ (((alpha + ∑ v, p v * (x v : ℝ)) : ℝ) : WithTop ℝ) + (rh : WithTop ℝ) at hx
      rw [← WithTop.coe_add] at hx
      have hx' : (0 : ℝ) ≤ (alpha + ∑ v, p v * (x v : ℝ)) + rh := by exact_mod_cast hx
      rw [toEReal_coe, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith
  have hp_dom1 : p ∈ DomEReal (ConvexConjugateZR f) := by
    intro htop
    rw [htop] at hconj_le
    exact EReal.coe_ne_top (-alpha - delta) (top_le_iff.mp hconj_le)
  have hp_dom2 : p ∈ DomERealConcave (ConcaveConjugateZR h2) := by
    intro hbot
    rw [hbot] at hconc_ge
    exact EReal.coe_ne_bot (-alpha) (le_bot_iff.mp hconc_ge)
  refine ⟨⟨hp_dom1, hp_dom2⟩, ?_⟩
  have hsub := EReal.sub_le_sub hconc_ge hconj_le
  have hdelta : ((-alpha : ℝ) : EReal) - ((-alpha - delta : ℝ) : EReal) = (delta : EReal) := by
    rw [← EReal.coe_sub]
    congr 1
    ring
  rw [hdelta] at hsub
  exact hsub

private lemma fenchel_from_sep (P : ((V → ℤ) → WithTop ℝ) → Prop)
    (hshift : ∀ f, P f → ∀ c : ℝ, P (shiftFn f c))
    (hsep : ∀ f h2, P f → P h2 →
      ((DomZ f ∩ DomZ h2).Nonempty ∨
        (DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2)).Nonempty) →
      (∀ x : V → ℤ, f x + h2 x ≥ 0) →
      ∃ alpha : ℝ, ∃ p : V → ℝ,
        (∀ x : V → ℤ, f x ≥ ((alpha + ∑ v, p v * (x v : ℝ) : ℝ) : WithTop ℝ)) ∧
        (∀ x : V → ℤ, ((alpha + ∑ v, p v * (x v : ℝ) : ℝ) : WithTop ℝ) + h2 x ≥ 0))
    (f h2 : (V → ℤ) → WithTop ℝ) (hf : P f) (hh2 : P h2)
    (hdom : (DomZ f ∩ DomZ h2).Nonempty ∨
      (DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2)).Nonempty) :
    InfDiff f h2 = SupDualGap f h2 ∧
    (InfDiff f h2 ≠ ⊤ → InfDiff f h2 ≠ ⊥ →
      ∃ p : V → ℝ, p ∈ DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2) ∧
        ConcaveConjugateZR h2 p - ConvexConjugateZR f p = SupDualGap f h2) := by
  have hweak : SupDualGap f h2 ≤ InfDiff f h2 := weak_duality f h2
  have h_attain_of_coe : ∀ delta : ℝ, (delta : EReal) ≤ InfDiff f h2 →
      ∃ p : V → ℝ, p ∈ DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2) ∧
        (delta : EReal) ≤ ConcaveConjugateZR h2 p - ConvexConjugateZR f p := by
    intro delta hdelta
    have hdom_shift : (DomZ (shiftFn f (-delta)) ∩ DomZ h2).Nonempty ∨
        (DomEReal (ConvexConjugateZR (shiftFn f (-delta))) ∩ DomERealConcave (ConcaveConjugateZR h2)).Nonempty := by
      rcases hdom with ⟨x₀, hx₀⟩ | ⟨p₀, hp₀⟩
      · left
        rw [domZ_shift]
        exact ⟨x₀, hx₀⟩
      · right
        exact ⟨p₀, domEReal_conj_shift f (-delta) hp₀.1, hp₀.2⟩
    have hge_shift : ∀ x : V → ℤ, shiftFn f (-delta) x + h2 x ≥ 0 := by
      intro x
      have hx_ge : (delta : EReal) ≤ ToEReal (f x) + ToEReal (h2 x) :=
        hdelta.trans (sInf_le ⟨x, rfl⟩)
      dsimp [shiftFn]
      cases hfx : f x with
      | top => simp
      | coe rf =>
        cases hhx : h2 x with
        | top => simp
        | coe rh =>
          rw [hfx, hhx, toEReal_coe, toEReal_coe, ← EReal.coe_add, EReal.coe_le_coe_iff] at hx_ge
          change (0 : WithTop ℝ) ≤ ((rf : WithTop ℝ) + ((-delta : ℝ) : WithTop ℝ)) + (rh : WithTop ℝ)
          rw [← WithTop.coe_add, ← WithTop.coe_add]
          exact_mod_cast (by linarith : (0 : ℝ) ≤ (rf + -delta) + rh)
    rcases hsep (shiftFn f (-delta)) h2 (hshift f hf (-delta)) hh2 hdom_shift hge_shift with
      ⟨alpha, p, h1, h2_ineq⟩
    rcases dual_bound_of_sep f h2 delta alpha p h1 h2_ineq with ⟨hp_dom, hp_ge⟩
    exact ⟨p, hp_dom, hp_ge⟩
  have hstrong : InfDiff f h2 = SupDualGap f h2 := by
    apply le_antisymm _ hweak
    rcases eq_bot_or_bot_lt (InfDiff f h2) with hbot | hbot_lt
    · rw [hbot]; exact bot_le
    · rcases eq_top_or_lt_top (InfDiff f h2) with htop | htop_lt
      · rw [htop, top_le_iff]
        by_contra hne_top
        have hlt_top : SupDualGap f h2 < ⊤ := lt_top_iff_ne_top.mpr hne_top
        have hex_r : ∃ r : ℝ, SupDualGap f h2 < (r : EReal) := by
          rcases eq_bot_or_bot_lt (SupDualGap f h2) with hsbot | hsbot_lt
          · exact ⟨0, by rw [hsbot]; exact EReal.bot_lt_coe 0⟩
          · lift SupDualGap f h2 to ℝ using ⟨hne_top, ne_of_gt hsbot_lt⟩ with M hM
            exact ⟨M + 1, by rw [EReal.coe_lt_coe_iff]; linarith⟩
        rcases hex_r with ⟨r, hr_gt⟩
        have hr_le : (r : EReal) ≤ InfDiff f h2 := by rw [htop]; exact le_top
        rcases h_attain_of_coe r hr_le with ⟨p, _, hp_ge⟩
        have hp_le : ConcaveConjugateZR h2 p - ConvexConjugateZR f p ≤ SupDualGap f h2 :=
          le_sSup ⟨p, rfl⟩
        exact not_le_of_gt hr_gt (hp_ge.trans hp_le)
      · lift InfDiff f h2 to ℝ using ⟨ne_of_lt htop_lt, ne_of_gt hbot_lt⟩ with delta hdelta
        rcases h_attain_of_coe delta le_rfl with ⟨p, _, hp_ge⟩
        exact hp_ge.trans (le_sSup ⟨p, rfl⟩)
  refine ⟨hstrong, fun htop hbot => ?_⟩
  lift InfDiff f h2 to ℝ using ⟨htop, hbot⟩ with delta hdelta
  rcases h_attain_of_coe delta le_rfl with ⟨p, hp_dom, hp_ge⟩
  refine ⟨p, hp_dom, ?_⟩
  exact le_antisymm (le_sSup ⟨p, rfl⟩) (hstrong ▸ hp_ge)

theorem solution :
    (∀ f h2 : (V → ℤ) → WithTop ℝ, MNaturalConvex f → MNaturalConvex h2 →
      ((DomZ f ∩ DomZ h2).Nonempty ∨
        (DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2)).Nonempty) →
      InfDiff f h2 = SupDualGap f h2 ∧
      (InfDiff f h2 ≠ ⊤ → InfDiff f h2 ≠ ⊥ →
        ∃ p : V → ℝ, p ∈ DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2) ∧
          ConcaveConjugateZR h2 p - ConvexConjugateZR f p = SupDualGap f h2)) ∧
    (∀ g k2 : (V → ℤ) → WithTop ℝ, LNaturalConvex g → LNaturalConvex k2 →
      ((DomZ g ∩ DomZ k2).Nonempty ∨
        (DomEReal (ConvexConjugateZR g) ∩ DomERealConcave (ConcaveConjugateZR k2)).Nonempty) →
      InfDiff g k2 = SupDualGap g k2 ∧
      (InfDiff g k2 ≠ ⊤ → InfDiff g k2 ≠ ⊥ →
        ∃ x : V → ℝ, x ∈ DomEReal (ConvexConjugateZR g) ∩ DomERealConcave (ConcaveConjugateZR k2) ∧
          ConcaveConjugateZR k2 x - ConvexConjugateZR g x = SupDualGap g k2)) :=
  ⟨fun f h2 hf hh2 hdom =>
    fenchel_from_sep MNaturalConvex mnat_shift
      (fun f' h2' hf' hh2' hdom' hge' => (m_separation_theorem f' h2' hf' hh2' hdom' hge').1)
      f h2 hf hh2 hdom,
   fun g k2 hg hk2 hdom =>
    fenchel_from_sep LNaturalConvex lnat_shift
      (fun g' k2' hg' hk2' hdom' hge' => (l_separation_theorem g' k2' hg' hk2' hdom' hge').1)
      g k2 hg hk2 hdom⟩
