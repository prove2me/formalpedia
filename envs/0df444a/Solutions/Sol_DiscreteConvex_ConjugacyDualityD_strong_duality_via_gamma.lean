-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.strong_duality_via_gamma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:01:20.704181+00:00
-- url     : https://prove2.me/submissions/76a82aa1-7dba-41f2-b86d-e8cdfb2882c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConcaveConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SubDifferentialZEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GammaR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_OptP
import Theorems.Thm_DiscreteConvex_ConjugacyDualityD_m_convex_strong_duality
import Theorems.Thm_DiscreteConvex_ConjugacyDualityD_dual_optimal_value_properties

set_option linter.unusedSectionVars false

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityD

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma fr_zero_eq (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hr0 : r (fun _ => (0 : ℤ)) = 0) (x : V → ℤ) :
    Fr c r B x (fun _ => 0) = if x ∈ B then c x else ⊤ := by
  simp only [Fr, F0, IndicatorWT, add_zero, hr0]
  split_ifs <;> simp

private lemma grBig_zero_eq (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (y : V → ℤ) :
    GRBig c r B y (fun _ => 0) = GRSmall c r B y := by
  simp only [GRBig, GRSmall, Int.cast_zero, mul_zero, Finset.sum_const_zero,
    EReal.coe_zero, sub_zero]

private lemma gammaR_zero_eq (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) :
    GammaR c r B (fun _ => 0) = sSup {t : EReal | ∃ y, t = GRSmall c r B y} := by
  simp only [GammaR, grBig_zero_eq]

private lemma exists_opt_of_finite (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hBbdd : B.Finite) (hr0 : r (fun _ => (0 : ℤ)) = 0) (hfeas : ∃ x ∈ B, c x ≠ ⊤) :
    ∃ (x_opt : V → ℤ) (v_opt : ℝ),
      x_opt ∈ B ∧ c x_opt = (v_opt : WithTop ℝ) ∧
      PhiR c r B (fun _ => 0) = (v_opt : EReal) ∧
      x_opt ∈ OptP c B (PhiR c r B (fun _ => 0)) := by
  rcases hfeas with ⟨x0, hx0B, hx0c⟩
  have hne : hBbdd.toFinset.Nonempty := ⟨x0, hBbdd.mem_toFinset.mpr hx0B⟩
  rcases Finset.exists_min_image hBbdd.toFinset (fun x => ToEReal (c x)) hne with
    ⟨x_opt, hx_opt_mem, hx_opt_min⟩
  have hx_optB : x_opt ∈ B := hBbdd.mem_toFinset.mp hx_opt_mem
  have hx_opt_le_x0 : ToEReal (c x_opt) ≤ ToEReal (c x0) :=
    hx_opt_min x0 (hBbdd.mem_toFinset.mpr hx0B)
  have hc_x0_lt : ToEReal (c x0) < ⊤ := by
    cases hcx0 : c x0 with
    | top => exact False.elim (hx0c hcx0)
    | coe v0 =>
      have h_eq : ToEReal ((v0 : ℝ) : WithTop ℝ) = (v0 : EReal) := rfl
      rw [h_eq]
      exact EReal.coe_lt_top v0
  have hc_opt_ne_top : c x_opt ≠ ⊤ := by
    intro htop
    have h_eq : ToEReal (c x_opt) = ⊤ := by
      rw [htop]
      rfl
    rw [h_eq] at hx_opt_le_x0
    exact not_lt_of_ge hx_opt_le_x0 hc_x0_lt
  cases hc_opt : c x_opt with
  | top => exact False.elim (hc_opt_ne_top hc_opt)
  | coe v_opt =>
    have h_toEReal_opt : ToEReal (c x_opt) = (v_opt : EReal) := by
      rw [hc_opt]
      rfl
    have h_phi_eq : PhiR c r B (fun _ => 0) = (v_opt : EReal) := by
      unfold PhiR
      apply le_antisymm
      · apply sInf_le
        refine ⟨x_opt, ?_⟩
        rw [fr_zero_eq c r B hr0 x_opt, if_pos hx_optB, h_toEReal_opt]
      · apply le_sInf
        rintro t ⟨x, rfl⟩
        rw [fr_zero_eq c r B hr0 x]
        split_ifs with hxB
        · rw [← h_toEReal_opt]
          exact hx_opt_min x (hBbdd.mem_toFinset.mpr hxB)
        · exact le_top
    refine ⟨x_opt, v_opt, hx_optB, hc_opt, h_phi_eq, ?_⟩
    simp [OptP, hx_optB, h_toEReal_opt, h_phi_eq]

private lemma eReal_subdiff_step (a : EReal) (v s : ℝ) :
    -a - -(v : EReal) ≥ (s : EReal) ↔ ((-v : ℝ) : EReal) ≤ ((-s : ℝ) : EReal) - a := by
  rw [ge_iff_le]
  cases a using EReal.rec with
  | bot =>
    change (s : EReal) ≤ ⊤ - -(v : EReal) ↔ ((-v : ℝ) : EReal) ≤ ((-s : ℝ) : EReal) - ⊥
    rw [← EReal.coe_neg v, EReal.top_sub_coe, EReal.sub_bot (EReal.coe_ne_bot (-s))]
    simp
  | top =>
    change (s : EReal) ≤ ⊥ - -(v : EReal) ↔ ((-v : ℝ) : EReal) ≤ ((-s : ℝ) : EReal) - ⊤
    rw [← EReal.coe_neg v, EReal.bot_sub, EReal.sub_top]
    simp [not_le_of_gt (EReal.bot_lt_coe s)]
  | coe g =>
    rw [← EReal.coe_neg g, ← EReal.coe_neg v, ← EReal.coe_sub, ← EReal.coe_sub,
      EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

private lemma eReal_neg_coe_le_iff (b : EReal) (v : ℝ) :
    ((-v : ℝ) : EReal) ≤ b ↔ -b ≤ (v : EReal) := by
  cases b using EReal.rec with
  | bot =>
    simp [not_le_of_gt (EReal.coe_lt_top v)]
  | top =>
    simp
  | coe g =>
    rw [← EReal.coe_neg g, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

theorem solution (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hBbdd : B.Finite) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r)
    (hr0 : r (fun _ => (0 : ℤ)) = 0) (hfeas : ∃ x ∈ B, c x ≠ ⊤) :
    PhiR c r B (fun _ => 0) = GammaR c r B (fun _ => 0) ∧
    GammaR c r B (fun _ => 0) = ConcaveConjE (ConcaveConjE (GammaR c r B)) (fun _ => 0) ∧
    ConcaveConjE (ConcaveConjE (GammaR c r B)) (fun _ => 0) =
      sSup {t : EReal | ∃ y, t = GRSmall c r B y} ∧
    OptP c B (PhiR c r B (fun _ => 0)) =
      SubDifferentialZEReal (fun x => -GammaR c r B x) (fun _ => 0) ∧
    (SubDifferentialZEReal (fun x => -GammaR c r B x) (fun _ => 0)).Nonempty := by
  rcases exists_opt_of_finite c r B hBbdd hr0 hfeas with
    ⟨x_opt, v_opt, hx_optB, hc_opt, h_phi_val, hx_opt_in⟩
  have hbdd : PhiR c r B (fun _ => 0) ≠ ⊥ := by
    rw [h_phi_val]
    exact EReal.coe_ne_bot v_opt
  have h_sd := m_convex_strong_duality c r B hcZ hrZ hB hc hr hr0 hfeas hbdd
  have h_phi_eq_sup : PhiR c r B (fun _ => 0) = sSup {t : EReal | ∃ y, t = GRSmall c r B y} :=
    h_sd.1.trans h_sd.2.1
  have h_gamma0 := gammaR_zero_eq c r B
  have h1 : PhiR c r B (fun _ => 0) = GammaR c r B (fun _ => 0) :=
    h_phi_eq_sup.trans h_gamma0.symm
  have h_rec := (dual_optimal_value_properties c r B hcZ hrZ hB hBbdd hc hr hr0).1
  have h_cc0 : ConcaveConjE (ConcaveConjE (GammaR c r B)) (fun _ => 0) = PhiR c r B (fun _ => 0) := by
    unfold ConcaveConjE PhiR
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Int.cast_zero, zero_mul, Finset.sum_const_zero,
      EReal.coe_zero, zero_sub]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨fun v => -y v, ?_⟩
      have h := h_rec (fun v => -y v)
      simp only [neg_neg] at h
      exact h.symm
    · rintro ⟨x, rfl⟩
      refine ⟨fun v => -x v, ?_⟩
      exact h_rec x
  have h2 : GammaR c r B (fun _ => 0) = ConcaveConjE (ConcaveConjE (GammaR c r B)) (fun _ => 0) :=
    h1.symm.trans h_cc0.symm
  have h3 : ConcaveConjE (ConcaveConjE (GammaR c r B)) (fun _ => 0) =
      sSup {t : EReal | ∃ y, t = GRSmall c r B y} :=
    h_cc0.trans h_phi_eq_sup
  have h_gamma_val : GammaR c r B (fun _ => 0) = (v_opt : EReal) :=
    h1.symm.trans h_phi_val
  have h4 : OptP c B (PhiR c r B (fun _ => 0)) =
      SubDifferentialZEReal (fun x => -GammaR c r B x) (fun _ => 0) := by
    ext x
    have h_sub_iff :
        x ∈ SubDifferentialZEReal (fun v => -GammaR c r B v) (fun _ => 0) ↔
          ToEReal (Fr c r B x (fun _ => 0)) ≤ (v_opt : EReal) := by
      simp only [SubDifferentialZEReal, Set.mem_setOf_eq, h_gamma_val, Int.cast_zero, sub_zero]
      have h_forall :
          (∀ w : V → ℤ,
            -GammaR c r B w - -(v_opt : EReal) ≥ ↑(∑ i, (x i : ℝ) * (w i : ℝ))) ↔
          ((-v_opt : ℝ) : EReal) ≤ ConcaveConjE (GammaR c r B) (fun v => -x v) := by
        rw [ConcaveConjE, le_sInf_iff]
        constructor
        · intro hw t ht
          rcases ht with ⟨w, rfl⟩
          have hw' := (eReal_subdiff_step (GammaR c r B w) v_opt (∑ i, (x i : ℝ) * (w i : ℝ))).mp (hw w)
          have h_sum_neg :
              (∑ i, ((-x i : ℤ) : ℝ) * (w i : ℝ)) = -(∑ i, (x i : ℝ) * (w i : ℝ)) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            push_cast
            ring
          rwa [h_sum_neg]
        · intro hle w
          have h_sum_neg :
              (∑ i, ((-x i : ℤ) : ℝ) * (w i : ℝ)) = -(∑ i, (x i : ℝ) * (w i : ℝ)) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            push_cast
            ring
          have hw' : ((-v_opt : ℝ) : EReal) ≤
              ((-(∑ i, (x i : ℝ) * (w i : ℝ)) : ℝ) : EReal) - GammaR c r B w := by
            rw [← h_sum_neg]
            exact hle _ ⟨w, rfl⟩
          exact (eReal_subdiff_step (GammaR c r B w) v_opt (∑ i, (x i : ℝ) * (w i : ℝ))).mpr hw'
      rw [h_forall, eReal_neg_coe_le_iff, ← h_rec x]
    rw [h_sub_iff]
    simp only [OptP, Set.mem_setOf_eq, h_phi_val]
    constructor
    · rintro ⟨hxB, hcx⟩
      rw [fr_zero_eq c r B hr0 x, if_pos hxB, hcx]
    · intro hle
      have hge : (v_opt : EReal) ≤ ToEReal (Fr c r B x (fun _ => 0)) := by
        rw [← h_phi_val]
        exact sInf_le ⟨x, rfl⟩
      have heq : ToEReal (Fr c r B x (fun _ => 0)) = (v_opt : EReal) := le_antisymm hle hge
      rw [fr_zero_eq c r B hr0 x] at heq
      split_ifs at heq with hxB
      · exact ⟨hxB, heq⟩
      · exfalso
        have : ToEReal (⊤ : WithTop ℝ) = ⊤ := rfl
        rw [this] at heq
        exact EReal.coe_ne_top v_opt heq.symm
  have h5 : (SubDifferentialZEReal (fun x => -GammaR c r B x) (fun _ => 0)).Nonempty := by
    rw [← h4]
    exact ⟨x_opt, hx_opt_in⟩
  exact ⟨h1, h2, h3, h4, h5⟩
