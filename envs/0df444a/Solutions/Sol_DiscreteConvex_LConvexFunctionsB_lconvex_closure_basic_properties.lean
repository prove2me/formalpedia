-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.lconvex_closure_basic_properties
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:23:27.119271+00:00
-- url     : https://prove2.me/submissions/2119e6fc-be05-4d3b-b51a-960dca817a7e

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ConvexClosureValOn
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ConvexClosureVal
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IntegralNeighborhoodFinset
import Theorems.Thm_DiscreteConvex_ConjugacyDualityC_lnat2_convex_is_integrally_convex

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsB

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma add_coe_inj {a b : WithTop ℝ} {r : ℝ}
    (h : a + (r : WithTop ℝ) = b + (r : WithTop ℝ)) : a = b := by
  cases a <;> cases b <;> simp [← WithTop.coe_add] at h ⊢
  exact h

private lemma coe_untopD_of_ne_top {a : WithTop ℝ} (ha : a ≠ ⊤) :
    ((a.untopD 0 : ℝ) : WithTop ℝ) = a := by
  lift a to ℝ using ha
  rfl

private lemma trf_shift {g : (V → ℤ) → WithTop ℝ} {r : ℝ}
    (hr : ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ))
    (k : ℤ) (p : V → ℤ) :
    g (fun v => p v + k) = g p + (((k : ℝ) * r : ℝ) : WithTop ℝ) := by
  induction k using Int.induction_on with
  | zero =>
    simp
  | succ i ih =>
    have h1 : (fun v => p v + ((i : ℤ) + 1)) = (fun v => p v + (i : ℤ)) + 1 := by
      ext v; simp [Pi.add_apply, add_assoc]
    rw [h1, hr, ih, add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast
    ring
  | pred i ih =>
    apply add_coe_inj (r := r)
    have h1 := hr (fun v => p v + (-(i : ℤ) - 1))
    have h2 : (fun v => p v + (-(i : ℤ) - 1)) + 1 = (fun v => p v + (-(i : ℤ))) := by
      ext v; simp [Pi.add_apply]; ring
    rw [h2, ih] at h1
    rw [← h1, add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast
    ring

private lemma sbf_trf_imp_lnatC (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    DiscreteConvex.ConjugacyDualityC.LNaturalConvex g := by
  rcases hg with ⟨hSBF, r, hr⟩
  constructor
  · intro x y
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL
    have hx : g (fun v => x (some v) - x none) =
        g (fun v => x (some v)) + (((-(x none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      simpa [sub_eq_add_neg] using trf_shift hr (-x none) (fun v => x (some v))
    have hy : g (fun v => y (some v) - y none) =
        g (fun v => y (some v)) + (((-(y none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      simpa [sub_eq_add_neg] using trf_shift hr (-y none) (fun v => y (some v))
    have hsup : g (fun v => (x ⊔ y) (some v) - (x ⊔ y) none) =
        g ((fun v => x (some v)) ⊔ (fun v => y (some v))) +
          (((-((x ⊔ y) none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      have h0 := trf_shift hr (-(x ⊔ y) none) (fun v => (x ⊔ y) (some v))
      have h1 : (fun v => (x ⊔ y) (some v) + -(x ⊔ y) none) =
          (fun v => (x ⊔ y) (some v) - (x ⊔ y) none) := by
        ext v; ring
      have h2 : (fun v => (x ⊔ y) (some v)) = (fun v => x (some v)) ⊔ (fun v => y (some v)) := rfl
      rw [h1, h2] at h0
      simpa using h0
    have hinf : g (fun v => (x ⊓ y) (some v) - (x ⊓ y) none) =
        g ((fun v => x (some v)) ⊓ (fun v => y (some v))) +
          (((-((x ⊓ y) none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      have h0 := trf_shift hr (-(x ⊓ y) none) (fun v => (x ⊓ y) (some v))
      have h1 : (fun v => (x ⊓ y) (some v) + -(x ⊓ y) none) =
          (fun v => (x ⊓ y) (some v) - (x ⊓ y) none) := by
        ext v; ring
      have h2 : (fun v => (x ⊓ y) (some v)) = (fun v => x (some v)) ⊓ (fun v => y (some v)) := rfl
      rw [h1, h2] at h0
      simpa using h0
    rw [hx, hy, hsup, hinf]
    have hadd_lhs :
        (g (fun v => x (some v)) + (((-(x none : ℝ)) * r : ℝ) : WithTop ℝ)) +
        (g (fun v => y (some v)) + (((-(y none : ℝ)) * r : ℝ) : WithTop ℝ)) =
        (g (fun v => x (some v)) + g (fun v => y (some v))) +
        (((-(x none : ℝ)) * r + (-(y none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add]
      ac_rfl
    have hadd_rhs :
        (g ((fun v => x (some v)) ⊔ (fun v => y (some v))) +
          (((-((x ⊔ y) none : ℝ)) * r : ℝ) : WithTop ℝ)) +
        (g ((fun v => x (some v)) ⊓ (fun v => y (some v))) +
          (((-((x ⊓ y) none : ℝ)) * r : ℝ) : WithTop ℝ)) =
        (g ((fun v => x (some v)) ⊔ (fun v => y (some v))) +
          g ((fun v => x (some v)) ⊓ (fun v => y (some v)))) +
        (((-((x ⊔ y) none : ℝ)) * r + (-((x ⊓ y) none : ℝ)) * r : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add]
      ac_rfl
    rw [hadd_lhs, hadd_rhs]
    have hnone :
        ((-(x none : ℝ)) * r + (-(y none : ℝ)) * r : ℝ) =
        ((-((x ⊔ y) none : ℝ)) * r + (-((x ⊓ y) none : ℝ)) * r : ℝ) := by
      have hmm : ((x ⊔ y) none : ℤ) + ((x ⊓ y) none : ℤ) = x none + y none :=
        max_add_min (x none) (y none)
      have hmmR : (((x ⊔ y) none : ℝ) + ((x ⊓ y) none : ℝ)) =
          (x none : ℝ) + (y none : ℝ) := by
        exact_mod_cast hmm
      calc (-(x none : ℝ)) * r + (-(y none : ℝ)) * r
        _ = -((x none : ℝ) + (y none : ℝ)) * r := by ring
        _ = -(((x ⊔ y) none : ℝ) + ((x ⊓ y) none : ℝ)) * r := by rw [hmmR]
        _ = (-((x ⊔ y) none : ℝ)) * r + (-((x ⊓ y) none : ℝ)) * r := by ring
    rw [hnone]
    exact add_le_add (hSBF (fun v => x (some v)) (fun v => y (some v))) le_rfl
  · refine ⟨0, fun x => ?_⟩
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL
    have h1 : (fun v => (x + 1) (some v) - (x + 1) none) = (fun v => x (some v) - x none) := by
      ext v
      simp [Pi.add_apply]
    rw [h1]
    simp

private noncomputable def zeroInd : (V → ℤ) → WithTop ℝ :=
  fun p => if p = 0 then 0 else ⊤

private lemma zeroInd_lnatC : DiscreteConvex.ConjugacyDualityC.LNaturalConvex (zeroInd (V := V)) := by
  constructor
  · intro x y
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL zeroInd
    by_cases hx : (fun v => x (some v) - x none) = 0
    · by_cases hy : (fun v => y (some v) - y none) = 0
      · have hsup : (fun v => (x ⊔ y) (some v) - (x ⊔ y) none) = 0 := by
          ext v
          have hxv : x (some v) = x none := sub_eq_zero.mp (congr_fun hx v)
          have hyv : y (some v) = y none := sub_eq_zero.mp (congr_fun hy v)
          simp [Pi.sup_apply, hxv, hyv]
        have hinf : (fun v => (x ⊓ y) (some v) - (x ⊓ y) none) = 0 := by
          ext v
          have hxv : x (some v) = x none := sub_eq_zero.mp (congr_fun hx v)
          have hyv : y (some v) = y none := sub_eq_zero.mp (congr_fun hy v)
          simp [Pi.inf_apply, hxv, hyv]
        rw [if_pos hx, if_pos hy, if_pos hsup, if_pos hinf]
      · rw [if_neg hy, add_top]
        exact le_top
    · rw [if_neg hx, top_add]
      exact le_top
  · refine ⟨0, fun x => ?_⟩
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL zeroInd
    have h1 : (fun v => (x + 1) (some v) - (x + 1) none) = (fun v => x (some v) - x none) := by
      ext v; simp [Pi.add_apply]
    rw [h1]
    simp

private lemma sbf_trf_imp_ic (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    DiscreteConvex.ConjugacyDualityC.IsIntegrallyConvexFunction g := by
  apply DiscreteConvex.ConjugacyDualityC.lnat2_convex_is_integrally_convex.1
  refine ⟨g, zeroInd, sbf_trf_imp_lnatC g hg, zeroInd_lnatC, ?_, ?_⟩
  · intro p
    have hle : DiscreteConvex.ConjugacyDualityC.ToEReal (g p) ≤
        DiscreteConvex.ConjugacyDualityC.InfConvE g zeroInd p := by
      apply le_sInf
      rintro L ⟨p1, p2, rfl, rfl⟩
      by_cases hp2 : p2 = 0
      · subst hp2
        have h0 : DiscreteConvex.ConjugacyDualityC.ToEReal (zeroInd (0 : V → ℤ)) = 0 := by
          change WithBot.some (if (0 : V → ℤ) = 0 then (0 : WithTop ℝ) else ⊤) = 0
          rw [if_pos rfl]
          rfl
        rw [add_zero, h0, add_zero]
      · have htop : DiscreteConvex.ConjugacyDualityC.ToEReal (zeroInd p2) = ⊤ := by
          change WithBot.some (if p2 = 0 then (0 : WithTop ℝ) else ⊤) = ⊤
          rw [if_neg hp2]
          rfl
        have hgp1 : DiscreteConvex.ConjugacyDualityC.ToEReal (g p1) + ⊤ = ⊤ := by
          cases g p1 <;> rfl
        rw [htop, hgp1]
        exact le_top
    intro hbot
    rw [hbot] at hle
    have hne : DiscreteConvex.ConjugacyDualityC.ToEReal (g p) ≠ ⊥ := WithBot.coe_ne_bot
    exact hne (le_bot_iff.mp hle)
  · ext p
    unfold DiscreteConvex.ConjugacyDualityC.InfConv
    symm
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨p, 0, by simp, ?_⟩
      simp [zeroInd]
    · rintro L ⟨p1, p2, rfl, rfl⟩
      by_cases hp2 : p2 = 0
      · subst hp2
        simp [zeroInd]
      · simp [zeroInd, hp2]

private lemma bddBelow_of_sInf_ne_top {S : Set (WithTop ℝ)} (h : sInf S ≠ ⊤) : BddBelow S := by
  by_contra hnb
  apply h
  change (if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else _) = ⊤
  exact if_pos (Or.inr hnb)

private lemma bddBelow_convexClosureValOn (g : (V → ℤ) → WithTop ℝ)
    (S : Finset (V → ℤ)) (x : V → ℝ) :
    BddBelow {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
      (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ g) ∧
      (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
      L = ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)} := by
  refine ⟨((∑ y ∈ S, -|(g y).untopD 0| : ℝ) : WithTop ℝ), ?_⟩
  rintro L ⟨lam, h0, h1, _, _, rfl⟩
  rw [WithTop.coe_le_coe]
  apply Finset.sum_le_sum
  intro y hy
  have hlam0 : 0 ≤ lam y := h0 y hy
  have hlam1 : lam y ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum h0 hy
  have habs : -|(g y).untopD 0| ≤ (g y).untopD 0 := neg_abs_le ((g y).untopD 0)
  have habs0 : 0 ≤ |(g y).untopD 0| := abs_nonneg ((g y).untopD 0)
  nlinarith

private lemma convexClosureValOn_le_of_weights (g : (V → ℤ) → WithTop ℝ)
    (S : Finset (V → ℤ)) (x : V → ℝ) (lam : (V → ℤ) → ℝ)
    (h0 : ∀ y ∈ S, 0 ≤ lam y) (h1 : ∑ y ∈ S, lam y = 1)
    (hdom : ∀ y ∈ S, y ∈ DomZ g) (hx : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) :
    ConvexClosureValOn g S x ≤ ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ) := by
  exact csInf_le (bddBelow_convexClosureValOn g S x) ⟨lam, h0, h1, hdom, hx, rfl⟩

private noncomputable def indDom (g : (V → ℤ) → WithTop ℝ) : (V → ℤ) → WithTop ℝ :=
  fun p => if g p = ⊤ then ⊤ else 0

private lemma indDom_sbf_trf (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    SBF (indDom g) ∧ TRF (indDom g) := by
  rcases hg with ⟨hSBF, r, hr⟩
  constructor
  · intro p q
    unfold indDom
    by_cases hp : g p = ⊤
    · simp [hp]
    by_cases hq : g q = ⊤
    · simp [hq]
    have hineq := hSBF p q
    have hadd_ne : g p + g q ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hp, hq⟩
    have hsup_inf_ne : g (p ⊔ q) + g (p ⊓ q) ≠ ⊤ := ne_top_of_le_ne_top hadd_ne hineq
    rcases WithTop.add_ne_top.mp hsup_inf_ne with ⟨hsup, hinf⟩
    simp [hp, hq, hsup, hinf]
  · refine ⟨0, fun p => ?_⟩
    unfold indDom
    have htop : g (p + 1) = ⊤ ↔ g p = ⊤ := by
      rw [hr p]
      exact WithTop.add_eq_top.trans (or_iff_left (WithTop.coe_ne_top))
    by_cases hp : g p = ⊤
    · simp [hp, htop.mpr hp]
    · have hp1 : g (p + 1) ≠ ⊤ := mt htop.mp hp
      simp [hp, hp1]

private lemma convexClosureVal_le_of_weights (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g)
    (S' : Finset (V → ℤ)) (x : V → ℝ) (lam' : (V → ℤ) → ℝ)
    (h0 : ∀ z ∈ S', 0 ≤ lam' z) (h1 : ∑ z ∈ S', lam' z = 1)
    (hdom : ∀ z ∈ S', z ∈ DomZ g) (hx : ∀ v, ∑ z ∈ S', lam' z * (z v : ℝ) = x v) :
    ConvexClosureVal g x ≤ ((∑ z ∈ S', lam' z * (g z).untopD 0 : ℝ) : WithTop ℝ) := by
  have hdom_ind : DomZ (indDom g) = DomZ g := by
    ext p; simp [DomZ, indDom]
  have hdom' : ∀ z ∈ S', z ∈ DomZ (indDom g) := by
    intro z hz; rw [hdom_ind]; exact hdom z hz
  have h_on_ind := convexClosureValOn_le_of_weights (indDom g) S' x lam' h0 h1 hdom' hx
  have h_bdd_ind : BddBelow {L : WithTop ℝ | ∃ S : Finset (V → ℤ),
      (∀ y ∈ S, y ∈ DomZ (indDom g)) ∧ L = ConvexClosureValOn (indDom g) S x} := by
    refine ⟨(0 : WithTop ℝ), ?_⟩
    rintro L ⟨S, _, rfl⟩
    unfold ConvexClosureValOn
    rcases Set.eq_empty_or_nonempty {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
        (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ (indDom g)) ∧
        (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
        L = ((∑ y ∈ S, lam y * (indDom g y).untopD 0 : ℝ) : WithTop ℝ)} with he | hne
    · rw [he, WithTop.sInf_empty]; exact le_top
    · apply le_csInf hne
      rintro L' ⟨lam, _, _, _, _, rfl⟩
      have hzero : ∀ y ∈ S, (indDom g y).untopD 0 = 0 := by
        intro y _
        unfold indDom
        split_ifs <;> simp
      have hsum0 : ∑ y ∈ S, lam y * (indDom g y).untopD 0 = 0 :=
        Finset.sum_eq_zero (fun y hy => by rw [hzero y hy, mul_zero])
      rw [hsum0, WithTop.coe_zero]
  have h_val_ind_le : ConvexClosureVal (indDom g) x ≤ ConvexClosureValOn (indDom g) S' x :=
    csInf_le h_bdd_ind ⟨S', hdom', rfl⟩
  have h_val_ind_ne_top : ConvexClosureVal (indDom g) x ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top h_on_ind) h_val_ind_le
  have hIC_ind := sbf_trf_imp_ic (indDom g) (indDom_sbf_trf g hg) x
  change ConvexClosureVal (indDom g) x =
    ConvexClosureValOn (indDom g) (Finset.filter (fun y => y ∈ DomZ (indDom g))
      (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x)) x at hIC_ind
  rw [hIC_ind] at h_val_ind_ne_top
  let S_x := Finset.filter (fun y => y ∈ DomZ g)
    (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x)
  have hSx_eq : Finset.filter (fun y => y ∈ DomZ (indDom g))
      (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x) = S_x := by
    simp [S_x, hdom_ind]
  rw [hSx_eq] at h_val_ind_ne_top
  have hne_Sx : {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
      (∀ y ∈ S_x, 0 ≤ lam y) ∧ (∑ y ∈ S_x, lam y = 1) ∧ (∀ y ∈ S_x, y ∈ DomZ (indDom g)) ∧
      (∀ v, ∑ y ∈ S_x, lam y * (y v : ℝ) = x v) ∧
      L = ((∑ y ∈ S_x, lam y * (indDom g y).untopD 0 : ℝ) : WithTop ℝ)}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply h_val_ind_ne_top
    unfold ConvexClosureValOn
    rw [hemp, WithTop.sInf_empty]
  rcases hne_Sx with ⟨_, lam_x, h0x, h1x, hdomx, hxx, _⟩
  have hdomx' : ∀ y ∈ S_x, y ∈ DomZ g := by
    intro y hy; rw [← hdom_ind]; exact hdomx y hy
  have h_on_g := convexClosureValOn_le_of_weights g S_x x lam_x h0x h1x hdomx' hxx
  have hIC_g := sbf_trf_imp_ic g hg x
  change ConvexClosureVal g x = ConvexClosureValOn g S_x x at hIC_g
  have h_val_g_ne_top : ConvexClosureVal g x ≠ ⊤ := by
    rw [hIC_g]
    exact ne_top_of_le_ne_top WithTop.coe_ne_top h_on_g
  have h_bdd_g : BddBelow {L : WithTop ℝ | ∃ S : Finset (V → ℤ),
      (∀ y ∈ S, y ∈ DomZ g) ∧ L = ConvexClosureValOn g S x} :=
    bddBelow_of_sInf_ne_top h_val_g_ne_top
  calc ConvexClosureVal g x
    _ ≤ ConvexClosureValOn g S' x := csInf_le h_bdd_g ⟨S', hdom, rfl⟩
    _ ≤ ((∑ z ∈ S', lam' z * (g z).untopD 0 : ℝ) : WithTop ℝ) :=
      convexClosureValOn_le_of_weights g S' x lam' h0 h1 hdom hx

private lemma sum_shift_lam₀ {S S' : Finset (V → ℤ)} (lam : (V → ℤ) → ℝ) (m : ℤ)
    (F : (V → ℤ) → ℝ) (hsub : S.image (fun y v => y v + m) ⊆ S') :
    let lam₀ : (V → ℤ) → ℝ := fun y => if y ∈ S then lam y else 0
    ∑ z ∈ S', lam₀ (fun v => z v - m) * F z = ∑ y ∈ S, lam y * F (fun v => y v + m) := by
  intro lam₀
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro y hy
      simp [lam₀, hy]
    · intro y₁ _ y₂ _ h
      ext v
      have := congr_fun h v
      dsimp at this
      omega
  · intro z _ hz
    have hnot : (fun v => z v - m) ∉ S := by
      intro hmem
      apply hz
      rw [Finset.mem_image]
      refine ⟨fun v => z v - m, hmem, ?_⟩
      ext v; ring
    simp [lam₀, hnot]

private lemma convexClosureVal_shift_le (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g)
    {r : ℝ} (hr : ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ))
    (q : V → ℝ) (alpha : ℝ) :
    ConvexClosureVal g (fun v => q v + alpha) ≤
      ConvexClosureVal g q + ((alpha * r : ℝ) : WithTop ℝ) := by
  have hIC := sbf_trf_imp_ic g hg q
  let S_q := Finset.filter (fun y => y ∈ DomZ g)
    (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset q)
  change ConvexClosureVal g q = ConvexClosureValOn g S_q q at hIC
  rw [hIC]
  let A := {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
    (∀ y ∈ S_q, 0 ≤ lam y) ∧ (∑ y ∈ S_q, lam y = 1) ∧ (∀ y ∈ S_q, y ∈ DomZ g) ∧
    (∀ v, ∑ y ∈ S_q, lam y * (y v : ℝ) = q v) ∧
    L = ((∑ y ∈ S_q, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)}
  change ConvexClosureVal g (fun v => q v + alpha) ≤ sInf A + ((alpha * r : ℝ) : WithTop ℝ)
  have h1 : ConvexClosureVal g (fun v => q v + alpha) + ((-(alpha * r) : ℝ) : WithTop ℝ) ≤ sInf A := by
    rcases A.eq_empty_or_nonempty with he | hne
    · rw [he, WithTop.sInf_empty]; exact le_top
    · apply le_csInf hne
      rintro L ⟨lam, h0, h1, hdom, hq, rfl⟩
      let k : ℤ := ⌊alpha⌋
      let θ : ℝ := alpha - (k : ℝ)
      have hθ0 : 0 ≤ θ := sub_nonneg.mpr (Int.floor_le alpha)
      have hθ1 : 0 ≤ 1 - θ := by
        have hlt : alpha < (k : ℝ) + 1 := Int.lt_floor_add_one alpha
        dsimp [θ]
        linarith
      let S₁ := S_q.image (fun y v => y v + k)
      let S₂ := S_q.image (fun y v => y v + (k + 1))
      let S' := S₁ ∪ S₂
      let lam₀ : (V → ℤ) → ℝ := fun y => if y ∈ S_q then lam y else 0
      let lam' : (V → ℤ) → ℝ := fun z =>
        (1 - θ) * lam₀ (fun v => z v - k) + θ * lam₀ (fun v => z v - (k + 1))
      have hlam0_nonneg : ∀ y, 0 ≤ lam₀ y := by
        intro y; dsimp [lam₀]; split_ifs with hy
        · exact h0 y hy
        · exact le_rfl
      have h0' : ∀ z ∈ S', 0 ≤ lam' z := by
        intro z _
        exact add_nonneg (mul_nonneg hθ1 (hlam0_nonneg _)) (mul_nonneg hθ0 (hlam0_nonneg _))
      have hsub₁ : S₁ ⊆ S' := Finset.subset_union_left
      have hsub₂ : S₂ ⊆ S' := Finset.subset_union_right
      have h1' : ∑ z ∈ S', lam' z = 1 := by
        have h_one : ∑ z ∈ S', lam' z * (1 : ℝ) = 1 := by
          have hsplit : ∑ z ∈ S', lam' z * (1 : ℝ) =
              (1 - θ) * (∑ z ∈ S', lam₀ (fun v => z v - k) * (1 : ℝ)) +
              θ * (∑ z ∈ S', lam₀ (fun v => z v - (k + 1)) * (1 : ℝ)) := by
            simp only [lam', add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [hsplit, sum_shift_lam₀ lam k (fun _ => 1) hsub₁,
            sum_shift_lam₀ lam (k + 1) (fun _ => 1) hsub₂]
          simp only [mul_one, h1]
          ring
        simpa using h_one
      have hdom' : ∀ z ∈ S', z ∈ DomZ g := by
        intro z hz
        rcases Finset.mem_union.mp hz with hz1 | hz2
        · rcases Finset.mem_image.mp hz1 with ⟨y, hy, rfl⟩
          change g (fun v => y v + k) ≠ ⊤
          rw [trf_shift hr k y]
          exact WithTop.add_ne_top.mpr ⟨hdom y hy, WithTop.coe_ne_top⟩
        · rcases Finset.mem_image.mp hz2 with ⟨y, hy, rfl⟩
          change g (fun v => y v + (k + 1)) ≠ ⊤
          rw [trf_shift hr (k + 1) y]
          exact WithTop.add_ne_top.mpr ⟨hdom y hy, WithTop.coe_ne_top⟩
      have hx' : ∀ v, ∑ z ∈ S', lam' z * (z v : ℝ) = q v + alpha := by
        intro v
        have hsplit : ∑ z ∈ S', lam' z * (z v : ℝ) =
            (1 - θ) * (∑ z ∈ S', lam₀ (fun w => z w - k) * (z v : ℝ)) +
            θ * (∑ z ∈ S', lam₀ (fun w => z w - (k + 1)) * (z v : ℝ)) := by
          simp only [lam', add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsplit, sum_shift_lam₀ lam k (fun z => (z v : ℝ)) hsub₁,
          sum_shift_lam₀ lam (k + 1) (fun z => (z v : ℝ)) hsub₂]
        have hsum_k : ∑ y ∈ S_q, lam y * ((y v + k : ℤ) : ℝ) = q v + (k : ℝ) := by
          calc ∑ y ∈ S_q, lam y * ((y v + k : ℤ) : ℝ)
            _ = ∑ y ∈ S_q, (lam y * (y v : ℝ) + lam y * (k : ℝ)) := by
              apply Finset.sum_congr rfl; intro y _; push_cast; ring
            _ = (∑ y ∈ S_q, lam y * (y v : ℝ)) + (∑ y ∈ S_q, lam y) * (k : ℝ) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul]
            _ = q v + (k : ℝ) := by rw [hq v, h1, one_mul]
        have hsum_k1 : ∑ y ∈ S_q, lam y * ((y v + (k + 1) : ℤ) : ℝ) = q v + ((k : ℝ) + 1) := by
          calc ∑ y ∈ S_q, lam y * ((y v + (k + 1) : ℤ) : ℝ)
            _ = ∑ y ∈ S_q, (lam y * (y v : ℝ) + lam y * ((k : ℝ) + 1)) := by
              apply Finset.sum_congr rfl; intro y _; push_cast; ring
            _ = (∑ y ∈ S_q, lam y * (y v : ℝ)) + (∑ y ∈ S_q, lam y) * ((k : ℝ) + 1) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul]
            _ = q v + ((k : ℝ) + 1) := by rw [hq v, h1, one_mul]
        rw [hsum_k, hsum_k1]
        dsimp [θ]
        ring
      have hval_le := convexClosureVal_le_of_weights g hg S' (fun v => q v + alpha) lam' h0' h1' hdom' hx'
      have hval_eq : ∑ z ∈ S', lam' z * (g z).untopD 0 =
          (∑ y ∈ S_q, lam y * (g y).untopD 0) + alpha * r := by
        have hsplit : ∑ z ∈ S', lam' z * (g z).untopD 0 =
            (1 - θ) * (∑ z ∈ S', lam₀ (fun w => z w - k) * (g z).untopD 0) +
            θ * (∑ z ∈ S', lam₀ (fun w => z w - (k + 1)) * (g z).untopD 0) := by
          simp only [lam', add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsplit, sum_shift_lam₀ lam k (fun z => (g z).untopD 0) hsub₁,
          sum_shift_lam₀ lam (k + 1) (fun z => (g z).untopD 0) hsub₂]
        have huntop : ∀ (m : ℤ) (y : V → ℤ), y ∈ S_q →
            (g (fun v => y v + m)).untopD 0 = (g y).untopD 0 + (m : ℝ) * r := by
          intro m y hy
          have hgy : g y ≠ ⊤ := hdom y hy
          lift g y to ℝ using hgy with gy hgy_eq
          have hshift := trf_shift hr m y
          rw [← hgy_eq, ← WithTop.coe_add] at hshift
          rw [hshift]
          rfl
        have hsum_gk : ∑ y ∈ S_q, lam y * (g (fun v => y v + k)).untopD 0 =
            (∑ y ∈ S_q, lam y * (g y).untopD 0) + (k : ℝ) * r := by
          calc ∑ y ∈ S_q, lam y * (g (fun v => y v + k)).untopD 0
            _ = ∑ y ∈ S_q, (lam y * (g y).untopD 0 + lam y * ((k : ℝ) * r)) := by
              apply Finset.sum_congr rfl; intro y hy; rw [huntop k y hy]; ring
            _ = (∑ y ∈ S_q, lam y * (g y).untopD 0) + (∑ y ∈ S_q, lam y) * ((k : ℝ) * r) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul]
            _ = (∑ y ∈ S_q, lam y * (g y).untopD 0) + (k : ℝ) * r := by rw [h1, one_mul]
        have hsum_gk1 : ∑ y ∈ S_q, lam y * (g (fun v => y v + (k + 1))).untopD 0 =
            (∑ y ∈ S_q, lam y * (g y).untopD 0) + ((k : ℝ) + 1) * r := by
          calc ∑ y ∈ S_q, lam y * (g (fun v => y v + (k + 1))).untopD 0
            _ = ∑ y ∈ S_q, (lam y * (g y).untopD 0 + lam y * (((k : ℝ) + 1) * r)) := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [huntop (k + 1) y hy]
              push_cast
              ring
            _ = (∑ y ∈ S_q, lam y * (g y).untopD 0) + (∑ y ∈ S_q, lam y) * (((k : ℝ) + 1) * r) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul]
            _ = (∑ y ∈ S_q, lam y * (g y).untopD 0) + ((k : ℝ) + 1) * r := by rw [h1, one_mul]
        rw [hsum_gk, hsum_gk1]
        dsimp [θ]
        ring
      rw [hval_eq] at hval_le
      have h_add := add_le_add hval_le (le_refl ((-(alpha * r) : ℝ) : WithTop ℝ))
      rw [← WithTop.coe_add, add_neg_cancel_right] at h_add
      exact h_add
  have h2 := add_le_add h1 (le_refl ((alpha * r : ℝ) : WithTop ℝ))
  rw [add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, add_zero] at h2
  exact h2

theorem solution (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    (∀ p : V → ℤ, ConvexClosureVal g (fun v => (p v : ℝ)) = g p) ∧
    (∃ r : ℝ, (∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)) ∧
      ∀ q : V → ℝ, ∀ alpha : ℝ,
        ConvexClosureVal g (fun v => q v + alpha) = ConvexClosureVal g q + (alpha * r : WithTop ℝ)) := by
  constructor
  · intro p
    let x : V → ℝ := fun v => (p v : ℝ)
    have hIC := sbf_trf_imp_ic g hg x
    let S₀ := Finset.filter (fun y => y ∈ DomZ g)
      (DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x)
    change ConvexClosureVal g x = ConvexClosureValOn g S₀ x at hIC
    rw [hIC]
    have hN : DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset x = {p} := by
      ext y
      simp only [DiscreteConvex.ConjugacyDualityC.IntegralNeighborhoodFinset,
        Fintype.mem_piFinset, Finset.mem_Icc, x, Int.floor_intCast, Int.ceil_intCast,
        Finset.mem_singleton, funext_iff]
      constructor
      · intro h v; have := h v; omega
      · intro h v; have := h v; omega
    by_cases hp : g p = ⊤
    · have hS₀ : S₀ = ∅ := by
        dsimp [S₀]
        rw [hN, Finset.filter_singleton, if_neg]
        simp [DomZ, hp]
      rw [hS₀]
      unfold ConvexClosureValOn
      have hemp : {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
          (∀ y ∈ (∅ : Finset (V → ℤ)), 0 ≤ lam y) ∧
          (∑ y ∈ (∅ : Finset (V → ℤ)), lam y = 1) ∧
          (∀ y ∈ (∅ : Finset (V → ℤ)), y ∈ DomZ g) ∧
          (∀ v, ∑ y ∈ (∅ : Finset (V → ℤ)), lam y * (y v : ℝ) = x v) ∧
          L = ((∑ y ∈ (∅ : Finset (V → ℤ)), lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)} = ∅ := by
        ext L
        simp
      rw [hemp, WithTop.sInf_empty, hp]
    · have hS₀ : S₀ = {p} := by
        dsimp [S₀]
        rw [hN, Finset.filter_singleton, if_pos]
        exact hp
      rw [hS₀]
      unfold ConvexClosureValOn
      apply IsLeast.csInf_eq
      constructor
      · refine ⟨fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
        · intro y _; norm_num
        · simp
        · intro y hy; rw [Finset.mem_singleton.mp hy]; exact hp
        · intro v; simp [x]
        · simp [coe_untopD_of_ne_top hp]
      · rintro L ⟨lam, _, h1, _, _, rfl⟩
        rw [Finset.sum_singleton] at h1
        simp [h1, coe_untopD_of_ne_top hp]
  · rcases hg.2 with ⟨r, hr⟩
    refine ⟨r, hr, fun q alpha => ?_⟩
    apply le_antisymm
    · exact convexClosureVal_shift_le g hg hr q alpha
    · have hle := convexClosureVal_shift_le g hg hr (fun v => q v + alpha) (-alpha)
      have hq : (fun v => q v + alpha + -alpha) = q := by ext v; ring
      rw [hq] at hle
      have h2 := add_le_add hle (le_refl ((alpha * r : ℝ) : WithTop ℝ))
      rw [add_assoc, ← WithTop.coe_add] at h2
      have hzero : (-alpha * r + alpha * r : ℝ) = 0 := by ring
      rw [hzero, WithTop.coe_zero, add_zero] at h2
      exact h2
