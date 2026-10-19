-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.fenchel_duality_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:55:16.052726+00:00
-- url     : https://prove2.me/submissions/eae7936f-86e9-49ab-af66-be561fe13f9a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DiscreteConvex_ConjugacyDualityB_m_separation_theorem
import Theorems.Thm_DiscreteConvex_ConjugacyDualityB_l_separation_theorem
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_InfDiff
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SupDualGap

open DiscreteConvex.ConjugacyDualityB

namespace FenchelO18

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] private lemma toEReal_coe (a : ℝ) : ToEReal (a : WithTop ℝ) = (a : EReal) := rfl

@[simp] private lemma toEReal_top : ToEReal (⊤ : WithTop ℝ) = (⊤ : EReal) := rfl

private lemma toEReal_coe_add (a : WithTop ℝ) (c : ℝ) :
    ToEReal (a + (c : WithTop ℝ)) = ToEReal a + (c : EReal) := by
  cases a using WithTop.recTopCoe
  · exact (EReal.top_add_coe c).symm
  · exact EReal.coe_add _ c

omit [Fintype V] [DecidableEq V] in
private lemma shift_dom (f : (V → ℤ) → WithTop ℝ) (c : ℝ) :
    DomZ (fun x => f x + (c : WithTop ℝ)) = DomZ f := by
  ext x
  simp [DomZ]

private lemma exchange_shift {W : Type*} [Fintype W] [DecidableEq W]
    (f : (W → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (c : ℝ) :
    MExchangeAxiom (fun x => f x + (c : WithTop ℝ)) := by
  intro x hx y hy u hu
  rw [shift_dom] at hx hy
  obtain ⟨v, hv, he⟩ := hf x hx y hy u hu
  refine ⟨v, hv, ?_⟩
  dsimp only
  convert add_le_add_right he ((c : WithTop ℝ) + (c : WithTop ℝ)) using 1 <;> ac_rfl

private lemma mnatural_shift (f : (V → ℤ) → WithTop ℝ)
    (hf : MNaturalConvex f) (c : ℝ) :
    MNaturalConvex (fun x => f x + (c : WithTop ℝ)) := by
  have hl : LiftedFunction (fun x => f x + (c : WithTop ℝ)) =
      fun x => LiftedFunction f x + (c : WithTop ℝ) := by
    funext x
    simp only [LiftedFunction]
    split_ifs <;> simp
  unfold MNaturalConvex
  rw [hl]
  exact exchange_shift _ hf c

omit [Fintype V] [DecidableEq V] in
private lemma lnatural_shift (f : (V → ℤ) → WithTop ℝ)
    (hf : LNaturalConvex f) (c : ℝ) :
    LNaturalConvex (fun x => f x + (c : WithTop ℝ)) := by
  constructor
  · intro x y
    have he := hf.1 x y
    change _ + _ ≤ _ + _
    dsimp only [LiftedFunctionL] at he ⊢
    convert add_le_add_right he ((c : WithTop ℝ) + (c : WithTop ℝ)) using 1 <;> ac_rfl
  · obtain ⟨r, hr⟩ := hf.2
    refine ⟨r, fun x => ?_⟩
    change LiftedFunctionL f (x + 1) + (c : WithTop ℝ) =
      (LiftedFunctionL f x + (c : WithTop ℝ)) + (r : WithTop ℝ)
    rw [hr]
    ac_rfl

omit [DecidableEq V] in
private lemma shifted_dual_domain (f h : (V → ℤ) → WithTop ℝ) (c : ℝ)
    (hd : (DomZ f ∩ DomZ h).Nonempty ∨
      (DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h)).Nonempty) :
    (DomZ f ∩ DomZ (fun x => h x + (c : WithTop ℝ))).Nonempty ∨
      (DomEReal (ConvexConjugateZR f) ∩
        DomERealConcave (ConcaveConjugateZR (fun x => h x + (c : WithTop ℝ)))).Nonempty := by
  rcases hd with hd | ⟨p, hpf, hph⟩
  · exact Or.inl (by simpa only [shift_dom] using hd)
  · refine Or.inr ⟨p, hpf, ?_⟩
    have hn : ConcaveConjugateZR h p ≠ ⊥ := hph
    have hb := EReal.coe_toReal_le hn
    have hl : ((ConcaveConjugateZR h p).toReal + c : ℝ) ≤
        ConcaveConjugateZR (fun x => h x + (c : WithTop ℝ)) p := by
      apply le_sInf
      rintro z ⟨x, rfl⟩
      have hx : ConcaveConjugateZR h p ≤
          ((∑ i, p i * (x i : ℝ) : ℝ) : EReal) + ToEReal (h x) :=
        sInf_le ⟨x, rfl⟩
      simpa only [EReal.coe_add, toEReal_coe_add, add_assoc] using
        add_le_add (hb.trans hx) (le_refl (c : EReal))
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl

omit [DecidableEq V] in
private lemma weak_duality (f h : (V → ℤ) → WithTop ℝ) :
    SupDualGap f h ≤ InfDiff f h := by
  apply sSup_le
  rintro z ⟨p, rfl⟩
  apply le_sInf
  rintro z ⟨x, rfl⟩
  have hc : ((∑ i, p i * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x) ≤
      ConvexConjugateZR f p := le_sSup ⟨x, rfl⟩
  have hh : ConcaveConjugateZR h p ≤
      ((∑ i, p i * (x i : ℝ) : ℝ) : EReal) + ToEReal (h x) := sInf_le ⟨x, rfl⟩
  generalize hf : f x = a at *
  generalize hhx : h x = b at *
  cases a using WithTop.recTopCoe
  · cases b using WithTop.recTopCoe <;> exact le_top
  cases b using WithTop.recTopCoe
  · exact le_top
  rename_i a b
  have he := EReal.sub_le_sub hh hc
  convert he using 1
  simp only [toEReal_coe, ← EReal.coe_add, ← EReal.coe_sub]
  congr 1
  ring

omit [DecidableEq V] in
private lemma separator_certificate (f h : (V → ℤ) → WithTop ℝ) (r beta : ℝ) (p : V → ℝ)
    (hf : ∀ x : V → ℤ, f x ≥ ((beta + ∑ i, p i * (x i : ℝ) : ℝ) : WithTop ℝ))
    (hh : ∀ x : V → ℤ, ((beta + ∑ i, p i * (x i : ℝ) : ℝ) : WithTop ℝ) +
      (h x + ((-r : ℝ) : WithTop ℝ)) ≥ 0) :
    ConvexConjugateZR f p ≤ ((-beta : ℝ) : EReal) ∧
      ((r - beta : ℝ) : EReal) ≤ ConcaveConjugateZR h p := by
  constructor
  · apply sSup_le
    rintro z ⟨x, rfl⟩
    have he := hf x
    generalize f x = a at *
    cases a using WithTop.recTopCoe
    · simp only [toEReal_top, EReal.sub_top, bot_le]
    rename_i a
    have hreal : beta + ∑ i, p i * (x i : ℝ) ≤ a := by exact_mod_cast he
    simp only [toEReal_coe, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith
  · apply le_sInf
    rintro z ⟨x, rfl⟩
    have he := hh x
    generalize h x = a at *
    cases a using WithTop.recTopCoe
    · simp only [toEReal_top, EReal.coe_add_top, le_top]
    rename_i a
    have hreal : 0 ≤ (beta + ∑ i, p i * (x i : ℝ)) + (a + -r) := by
      exact_mod_cast he
    simp only [toEReal_coe, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

private lemma generic_fenchel
    (C : ((V → ℤ) → WithTop ℝ) → Prop)
    (hshift : ∀ h, C h → ∀ c : ℝ, C (fun x => h x + (c : WithTop ℝ)))
    (hsep : ∀ f h : (V → ℤ) → WithTop ℝ, C f → C h →
      ((DomZ f ∩ DomZ h).Nonempty ∨
        (DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h)).Nonempty) →
      (∀ x, f x + h x ≥ 0) →
      ∃ beta : ℝ, ∃ p : V → ℝ,
        (∀ x : V → ℤ, f x ≥ ((beta + ∑ i, p i * (x i : ℝ) : ℝ) : WithTop ℝ)) ∧
        (∀ x : V → ℤ, ((beta + ∑ i, p i * (x i : ℝ) : ℝ) : WithTop ℝ) + h x ≥ 0))
    (f h : (V → ℤ) → WithTop ℝ) (hf : C f) (hh : C h)
    (hd : (DomZ f ∩ DomZ h).Nonempty ∨
      (DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h)).Nonempty) :
    InfDiff f h = SupDualGap f h ∧
      (InfDiff f h ≠ ⊤ → InfDiff f h ≠ ⊥ →
        ∃ p : V → ℝ, p ∈ DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h) ∧
          ConcaveConjugateZR h p - ConvexConjugateZR f p = SupDualGap f h) := by
  have certificate : ∀ r : ℝ, (r : EReal) ≤ InfDiff f h →
      ∃ p : V → ℝ, p ∈ DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h) ∧
        (r : EReal) ≤ ConcaveConjugateZR h p - ConvexConjugateZR f p := by
    intro r hr
    have hnonneg : ∀ x, f x + (h x + ((-r : ℝ) : WithTop ℝ)) ≥ 0 := by
      intro x
      have hx : (r : EReal) ≤ ToEReal (f x) + ToEReal (h x) :=
        hr.trans (sInf_le ⟨x, rfl⟩)
      generalize f x = a at *
      generalize h x = b at *
      cases a using WithTop.recTopCoe
      · simp
      cases b using WithTop.recTopCoe
      · simp
      rename_i a b
      have hreal : r ≤ a + b := by
        simpa only [toEReal_coe, ← EReal.coe_add, EReal.coe_le_coe_iff] using hx
      have : 0 ≤ a + (b + -r) := by linarith
      exact_mod_cast this
    obtain ⟨beta, p, hpf, hph⟩ := hsep f (fun x => h x + ((-r : ℝ) : WithTop ℝ)) hf
      (hshift h hh (-r)) (shifted_dual_domain f h (-r) hd) hnonneg
    obtain ⟨hu, hl⟩ := separator_certificate f h r beta p hpf hph
    refine ⟨p, ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hu,
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl⟩, ?_⟩
    have he := EReal.sub_le_sub hl hu
    convert he using 1
    rw [← EReal.coe_sub]
    congr 1
    ring
  have hweak := weak_duality f h
  have heq : InfDiff f h = SupDualGap f h := by
    apply le_antisymm _ hweak
    apply EReal.ge_of_forall_gt_iff_ge.mp
    intro r hr
    obtain ⟨p, _, hp⟩ := certificate r hr.le
    exact hp.trans (le_sSup ⟨p, rfl⟩)
  refine ⟨heq, fun ht hb => ?_⟩
  have hcoe := EReal.coe_toReal ht hb
  obtain ⟨p, hpdom, hp⟩ := certificate (InfDiff f h).toReal hcoe.le
  refine ⟨p, hpdom, le_antisymm (le_sSup ⟨p, rfl⟩) ?_⟩
  rwa [← heq, ← hcoe]

end FenchelO18

open DiscreteConvex.ConjugacyDualityB

theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
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
          ConcaveConjugateZR k2 x - ConvexConjugateZR g x = SupDualGap g k2)) := by
  constructor
  · exact FenchelO18.generic_fenchel MNaturalConvex FenchelO18.mnatural_shift
      (fun f h hf hh hd hge => (m_separation_theorem f h hf hh hd hge).1)
  · exact FenchelO18.generic_fenchel LNaturalConvex FenchelO18.lnatural_shift
      (fun f h hf hh hd hge => (l_separation_theorem f h hf hh hd hge).1)
