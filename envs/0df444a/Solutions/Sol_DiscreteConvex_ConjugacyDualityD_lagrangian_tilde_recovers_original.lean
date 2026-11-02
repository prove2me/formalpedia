-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.lagrangian_tilde_recovers_original
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:17:14.188573+00:00
-- url     : https://prove2.me/submissions/4b7e410f-0c34-4b60-a0dd-5c6af6eca9e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KTildeR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_FTildeR
import Theorems.Thm_DiscreteConvex_ConjugacyDualityD_lagrangian_kernel_convexity
import Theorems.Thm_DiscreteConvex_ConjugacyDualityD_m2_l2_conjugacy_correspondence

set_option linter.unusedSectionVars false

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityD

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma toEReal_coe (r : ℝ) : ToEReal (r : WithTop ℝ) = (r : EReal) := rfl

private lemma toEReal_top : ToEReal (⊤ : WithTop ℝ) = (⊤ : EReal) := rfl

private lemma toEReal_injective : Function.Injective ToEReal := by
  intro a b h
  cases a with
  | top =>
    cases b with
    | top => rfl
    | coe rb =>
      exact False.elim (EReal.coe_ne_top rb h.symm)
  | coe ra =>
    cases b with
    | top =>
      exact False.elim (EReal.coe_ne_top ra h)
    | coe rb =>
      change (ra : EReal) = (rb : EReal) at h
      rw [EReal.coe_eq_coe_iff] at h
      subst h
      rfl

private lemma toEReal_fromEReal_of_ne_bot {x : EReal} (hx : x ≠ ⊥) :
    ToEReal (FromEReal x) = x := by
  cases x using EReal.rec with
  | bot => exact False.elim (hx rfl)
  | top => rfl
  | coe r => rfl

private lemma eReal_sInf_neg_eq_neg_sSup {α : Type*} (f : α → EReal) :
    sInf {t : EReal | ∃ a : α, t = -f a} = -sSup {s : EReal | ∃ a : α, s = f a} := by
  apply le_antisymm
  · rw [← EReal.neg_le_neg_iff, neg_neg]
    apply sSup_le
    rintro s ⟨a, rfl⟩
    rw [← EReal.neg_le_neg_iff, neg_neg]
    exact sInf_le ⟨a, rfl⟩
  · apply le_sInf
    rintro t ⟨a, rfl⟩
    rw [EReal.neg_le_neg_iff]
    exact le_sSup ⟨a, rfl⟩

private lemma eReal_neg_sub_coe (a : EReal) (r : ℝ) :
    -(a - (r : EReal)) = (r : EReal) - a := by
  cases a using EReal.rec with
  | bot =>
    rw [EReal.bot_sub, EReal.neg_bot, EReal.sub_bot (EReal.coe_ne_bot r)]
  | top =>
    rw [EReal.top_sub_coe, EReal.neg_top, EReal.sub_top]
  | coe z =>
    rw [← EReal.coe_sub, ← EReal.coe_neg, ← EReal.coe_sub]
    congr 1
    ring

private lemma eReal_neg_add_coe (a : EReal) (r : ℝ) :
    -(a + (r : EReal)) = -(r : EReal) - a := by
  cases a using EReal.rec with
  | bot =>
    rw [EReal.bot_add, EReal.neg_bot, ← EReal.coe_neg, EReal.sub_bot (EReal.coe_ne_bot (-r))]
  | top =>
    rw [EReal.top_add_coe, EReal.neg_top, EReal.sub_top]
  | coe z =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_sub]
    congr 1
    ring

private lemma eReal_neg_coe_sub (a : EReal) (r : ℝ) :
    -((r : EReal) - a) = a - (r : EReal) := by
  rw [← eReal_neg_sub_coe a r, neg_neg]

private lemma eReal_neg_neg_coe_sub (a : EReal) (r : ℝ) :
    -(((-r : ℝ) : EReal) - a) = a + (r : EReal) := by
  rw [EReal.coe_neg, ← eReal_neg_add_coe a r, neg_neg]

private lemma kr_term_int_or_top (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r) (x y u : V → ℤ) :
    ToEReal (Fr c r B x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal) = ⊤ ∨
      ∃ k : ℤ,
        ToEReal (Fr c r B x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal) = ((k : ℝ) : EReal) := by
  unfold Fr F0 IndicatorWT
  rcases hcZ x with hcx | ⟨kc, hcx⟩
  · left
    simp [hcx, toEReal_top]
  · rcases hrZ u with hru | ⟨kr, hru⟩
    · left
      simp [hru, toEReal_top]
    · by_cases hmem : (fun v => x v + u v) ∈ B
      · right
        refine ⟨kc + kr + ∑ i, u i * y i, ?_⟩
        rw [if_pos hmem, hcx, hru, add_zero, ← WithTop.coe_add, toEReal_coe, ← EReal.coe_add]
        congr 1
        push_cast
        ring
      · left
        simp [if_neg hmem, toEReal_top]

private lemma kr_int_or_top (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r) (hBbdd : B.Finite)
    (x y : V → ℤ) :
    KR c r B x y = ⊤ ∨ ∃ k : ℤ, KR c r B x y = ((k : ℝ) : EReal) := by
  let term : (V → ℤ) → EReal := fun u =>
    ToEReal (Fr c r B x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)
  let U : Finset (V → ℤ) := hBbdd.toFinset.image (fun z v => z v - x v)
  have h_not_mem_U : ∀ u : V → ℤ, u ∉ U → term u = ⊤ := by
    intro u hu
    have hnotB : (fun v => x v + u v) ∉ B := by
      intro hmem
      apply hu
      rw [Finset.mem_image]
      refine ⟨fun v => x v + u v, hBbdd.mem_toFinset.mpr hmem, ?_⟩
      funext v
      dsimp
      omega
    dsimp [term]
    unfold Fr F0 IndicatorWT
    rw [if_neg hnotB, add_top, top_add, toEReal_top, EReal.top_add_coe]
  let UF : Finset (V → ℤ) := U.filter (fun u => term u ≠ ⊤)
  by_cases hne : UF.Nonempty
  · rcases Finset.exists_min_image UF term hne with ⟨u0, hu0_mem, hu0_min⟩
    have hu0_ne_top : term u0 ≠ ⊤ := (Finset.mem_filter.mp hu0_mem).2
    have h_kr_eq : KR c r B x y = term u0 := by
      unfold KR
      apply le_antisymm
      · exact sInf_le ⟨u0, rfl⟩
      · apply le_sInf
        rintro t ⟨u, rfl⟩
        change term u0 ≤ term u
        by_cases htu : term u = ⊤
        · rw [htu]
          exact le_top
        · have huU : u ∈ U := by
            by_contra huU
            exact htu (h_not_mem_U u huU)
          exact hu0_min u (Finset.mem_filter.mpr ⟨huU, htu⟩)
    rcases kr_term_int_or_top c r B hcZ hrZ x y u0 with htop | ⟨k, hk⟩
    · exact False.elim (hu0_ne_top htop)
    · right
      exact ⟨k, h_kr_eq.trans hk⟩
  · left
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold KR
    apply le_antisymm le_top
    apply le_sInf
    rintro t ⟨u, rfl⟩
    change ⊤ ≤ term u
    have htu : term u = ⊤ := by
      by_contra htu
      have huU : u ∈ U := by
        by_contra huU
        exact htu (h_not_mem_U u huU)
      have huUF : u ∈ UF := Finset.mem_filter.mpr ⟨huU, htu⟩
      rw [hne] at huUF
      simp at huUF
    rw [htu]

private lemma m2Convex_top : M2Convex (fun _ : V → ℤ => (⊤ : WithTop ℝ)) := by
  refine ⟨fun _ => ⊤, fun _ => ⊤, ?_, ?_, ?_⟩
  · intro x hx
    simp [DomZ] at hx
  · intro x hx
    simp [DomZ] at hx
  · funext x
    rfl

private lemma mExchangeAxiom_const_add_indicator_shift (c_val : WithTop ℝ) (B : Set (V → ℤ))
    (hB : ExchangeAxiomB B) (x : V → ℤ) :
    MExchangeAxiom (fun u => c_val + IndicatorWT B (fun v => x v + u v)) := by
  intro u1 hu1 u2 hu2 i hi
  simp only [DomZ, Set.mem_setOf_eq] at hu1 hu2
  have hu1B : (fun v => x v + u1 v) ∈ B := by
    by_contra hnot
    apply hu1
    simp [IndicatorWT, hnot]
  have hu2B : (fun v => x v + u2 v) ∈ B := by
    by_contra hnot
    apply hu2
    simp [IndicatorWT, hnot]
  have hi' : i ∈ SuppPos (fun v => x v + u1 v) (fun v => x v + u2 v) := by
    simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  rcases hB _ hu1B _ hu2B i hi' with ⟨j, hj', hj1B, hj2B⟩
  have hj : j ∈ SuppNeg u1 u2 := by
    simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hj' ⊢
    omega
  refine ⟨j, hj, ?_⟩
  have heq1 : (fun v => x v + (u1 v - IndicatorVec {i} v + IndicatorVec {j} v)) =
      (fun w => (x w + u1 w) - IndicatorVec {i} w + IndicatorVec {j} w) := by
    funext w
    ring
  have heq2 : (fun v => x v + (u2 v + IndicatorVec {i} v - IndicatorVec {j} v)) =
      (fun w => (x w + u2 w) + IndicatorVec {i} w - IndicatorVec {j} w) := by
    funext w
    ring
  dsimp only []
  rw [heq1, heq2]
  simp [IndicatorWT, hu1B, hu2B, hj1B, hj2B]

private lemma biconjugate_recovery_aux (h : (V → ℤ) → WithTop ℝ)
    (h_biconj : ConvexConjugate (ConvexConjugate h) = h)
    (h_nontop : ∃ x0, h x0 ≠ ⊤) :
    (∀ p : V → ℤ, sSup {v : EReal | ∃ z : V → ℤ,
      v = ((∑ i, (p i : ℝ) * (z i : ℝ) : ℝ) : EReal) - ToEReal (h z)} ≠ ⊥) ∧
    (∃ p0, ConvexConjugate h p0 ≠ ⊤) := by
  rcases h_nontop with ⟨x0, hx0⟩
  have h_sup_ne_bot : ∀ p : V → ℤ, sSup {v : EReal | ∃ z : V → ℤ,
      v = ((∑ i, (p i : ℝ) * (z i : ℝ) : ℝ) : EReal) - ToEReal (h z)} ≠ ⊥ := by
    intro p hbot
    cases hhx0 : h x0 with
    | top => exact hx0 hhx0
    | coe r0 =>
      have hle : (((∑ i, (p i : ℝ) * (x0 i : ℝ) : ℝ) : EReal) - ToEReal (h x0)) ≤ ⊥ := by
        rw [← hbot]
        exact le_sSup ⟨x0, rfl⟩
      rw [hhx0, toEReal_coe, ← EReal.coe_sub] at hle
      exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
  refine ⟨h_sup_ne_bot, ?_⟩
  by_contra h_all_top
  push_neg at h_all_top
  have h_cc_top : ConvexConjugate (ConvexConjugate h) x0 = ⊤ := by
    change FromEReal (sSup {v : EReal | ∃ z : V → ℤ,
      v = ((∑ i, (x0 i : ℝ) * (z i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate h z)}) = ⊤
    have h_set : {v : EReal | ∃ z : V → ℤ,
        v = ((∑ i, (x0 i : ℝ) * (z i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate h z)} = {⊥} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, rfl⟩
        rw [h_all_top z, toEReal_top, EReal.sub_top]
      · rintro rfl
        refine ⟨fun _ => 0, ?_⟩
        rw [h_all_top (fun _ => 0), toEReal_top, EReal.sub_top]
    rw [h_set, sSup_singleton]
    rfl
  rw [h_biconj] at h_cc_top
  exact hx0 h_cc_top

theorem solution (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hBbdd : B.Finite) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r)
    (hr0 : r (fun _ => (0 : ℤ)) = 0) :
    (∀ x y, KTildeR c r B x y = KR c r B x y) ∧
    (∀ x, FTildeR c r B x = ToEReal (Fr c r B x (fun _ => 0))) := by
  have h1 : ∀ x y, KTildeR c r B x y = KR c r B x y := by
    intro x y
    have h_lkc := (lagrangian_kernel_convexity c r B hB hr).2.2.2 hc y
    have h_embed : ∃ h : (V → ℤ) → WithTop ℝ, M2Convex h ∧ ∀ z, KR c r B z y = ToEReal (h z) := by
      rcases h_lkc with ⟨h, hM2, hh⟩ | h_inf
      · exact ⟨h, hM2, hh⟩
      · refine ⟨fun _ => ⊤, m2Convex_top, fun z => ?_⟩
        rcases kr_int_or_top c r B hcZ hrZ hBbdd z y with htop | ⟨k, hk⟩
        · exact htop
        · rcases h_inf z with htop | hbot
          · exact htop
          · rw [hk] at hbot
            exact False.elim (EReal.coe_ne_bot _ hbot)
    rcases h_embed with ⟨h, hM2, hh⟩
    have hZ : IsIntegerValuedFn h := by
      intro z
      rcases kr_int_or_top c r B hcZ hrZ hBbdd z y with htop | ⟨k, hk⟩
      · left
        apply toEReal_injective
        rw [← hh z, htop, toEReal_top]
      · right
        refine ⟨k, ?_⟩
        apply toEReal_injective
        rw [← hh z, hk, toEReal_coe]
    have h_biconj : ConvexConjugate (ConvexConjugate h) = h :=
      ((m2_l2_conjugacy_correspondence).1 h hM2 hZ).2
    by_cases h_nontop : ∃ z0, h z0 ≠ ⊤
    · rcases biconjugate_recovery_aux h h_biconj h_nontop with ⟨h_sup_ne_bot, ⟨p0, hp0⟩⟩
      have h_grBig : ∀ v, GRBig c r B y v = -ToEReal (ConvexConjugate h v) := by
        intro v
        unfold GRBig
        have h_set : {t : EReal | ∃ z : V → ℤ,
            t = KR c r B z y - ((∑ i, (z i : ℝ) * (v i : ℝ) : ℝ) : EReal)} =
            {t : EReal | ∃ z : V → ℤ,
              t = -(((∑ i, (v i : ℝ) * (z i : ℝ) : ℝ) : EReal) - ToEReal (h z))} := by
          ext t
          simp only [Set.mem_setOf_eq]
          constructor
          · rintro ⟨z, rfl⟩
            refine ⟨z, ?_⟩
            rw [hh z, eReal_neg_coe_sub]
            congr 2
            refine Finset.sum_congr rfl fun i _ => mul_comm _ _
          · rintro ⟨z, rfl⟩
            refine ⟨z, ?_⟩
            rw [hh z, eReal_neg_coe_sub]
            congr 2
            refine Finset.sum_congr rfl fun i _ => mul_comm _ _
        rw [h_set, eReal_sInf_neg_eq_neg_sSup]
        unfold ConvexConjugate
        rw [toEReal_fromEReal_of_ne_bot (h_sup_ne_bot v)]
      have h_ktilde_set : {t : EReal | ∃ v : V → ℤ,
          t = GRBig c r B y v + ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal)} =
          {t : EReal | ∃ v : V → ℤ,
            t = ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate h v)} := by
        ext t
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨v, rfl⟩
          refine ⟨v, ?_⟩
          rw [h_grBig v, sub_eq_add_neg, add_comm]
        · rintro ⟨v, rfl⟩
          refine ⟨v, ?_⟩
          rw [h_grBig v, sub_eq_add_neg, add_comm]
      have h_outer_ne_bot : sSup {t : EReal | ∃ v : V → ℤ,
          t = ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate h v)} ≠ ⊥ := by
        intro hbot
        cases hcp0 : ConvexConjugate h p0 with
        | top => exact hp0 hcp0
        | coe rp0 =>
          have hle : (((∑ i, (x i : ℝ) * (p0 i : ℝ) : ℝ) : EReal) -
              ToEReal (ConvexConjugate h p0)) ≤ ⊥ := by
            rw [← hbot]
            exact le_sSup ⟨p0, rfl⟩
          rw [hcp0, toEReal_coe, ← EReal.coe_sub] at hle
          exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
      unfold KTildeR
      rw [h_ktilde_set, ← toEReal_fromEReal_of_ne_bot h_outer_ne_bot]
      change ToEReal (ConvexConjugate (ConvexConjugate h) x) = KR c r B x y
      rw [h_biconj, hh x]
    · push_neg at h_nontop
      have h_kr_top : ∀ z, KR c r B z y = ⊤ := by
        intro z
        rw [hh z, h_nontop z, toEReal_top]
      have h_gr_top : ∀ v, GRBig c r B y v = ⊤ := by
        intro v
        unfold GRBig
        apply le_antisymm le_top
        apply le_sInf
        rintro t ⟨z, rfl⟩
        rw [h_kr_top z, EReal.top_sub_coe]
      unfold KTildeR
      rw [h_kr_top x]
      apply le_antisymm le_top
      have : (⊤ : EReal) = GRBig c r B y (fun _ => 0) +
          ((∑ i, (x i : ℝ) * ((0 : ℤ) : ℝ) : ℝ) : EReal) := by
        rw [h_gr_top, EReal.top_add_coe]
      exact le_sSup ⟨fun _ => 0, this⟩
  refine ⟨h1, ?_⟩
  intro x
  have h_ftilde_eq : FTildeR c r B x = sSup {t : EReal | ∃ y, t = KR c r B x y} := by
    unfold FTildeR
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, h1 x]
  rw [h_ftilde_eq]
  let φ : (V → ℤ) → WithTop ℝ := fun u => Fr c r B x u
  have hφ_M2 : M2Convex φ := by
    refine ⟨fun u => c x + IndicatorWT B (fun v => x v + u v), r, ?_, hr, rfl⟩
    exact mExchangeAxiom_const_add_indicator_shift (c x) B hB x
  have hφ_Z : IsIntegerValuedFn φ := by
    intro u
    dsimp [φ]
    unfold Fr F0 IndicatorWT
    rcases hcZ x with hcx | ⟨kc, hcx⟩
    · left
      simp [hcx]
    · rcases hrZ u with hru | ⟨kr, hru⟩
      · left
        simp [hru]
      · by_cases hmem : (fun v => x v + u v) ∈ B
        · right
          refine ⟨kc + kr, ?_⟩
          rw [if_pos hmem, hcx, hru, add_zero, ← WithTop.coe_add]
          push_cast
          rfl
        · left
          simp [if_neg hmem]
  have hφ_biconj : ConvexConjugate (ConvexConjugate φ) = φ :=
    ((m2_l2_conjugacy_correspondence).1 φ hφ_M2 hφ_Z).2
  by_cases hφ_nontop : ∃ u0, φ u0 ≠ ⊤
  · rcases biconjugate_recovery_aux φ hφ_biconj hφ_nontop with ⟨h_sup_ne_bot, ⟨p0, hp0⟩⟩
    have h_kr_eq : ∀ y, KR c r B x y = -ToEReal (ConvexConjugate φ (fun v => -y v)) := by
      intro y
      unfold KR
      have h_set : {t : EReal | ∃ u : V → ℤ,
          t = ToEReal (Fr c r B x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)} =
          {t : EReal | ∃ u : V → ℤ,
            t = -(((∑ i, ((-y i : ℤ) : ℝ) * (u i : ℝ) : ℝ) : EReal) - ToEReal (φ u))} := by
        ext t
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨u, rfl⟩
          refine ⟨u, ?_⟩
          have h_sum : (∑ i, ((-y i : ℤ) : ℝ) * (u i : ℝ)) = -(∑ i, (u i : ℝ) * (y i : ℝ)) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            push_cast
            ring
          rw [h_sum, eReal_neg_neg_coe_sub]
        · rintro ⟨u, rfl⟩
          refine ⟨u, ?_⟩
          have h_sum : (∑ i, ((-y i : ℤ) : ℝ) * (u i : ℝ)) = -(∑ i, (u i : ℝ) * (y i : ℝ)) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            push_cast
            ring
          rw [h_sum, eReal_neg_neg_coe_sub]
      rw [h_set, eReal_sInf_neg_eq_neg_sSup]
      unfold ConvexConjugate
      rw [toEReal_fromEReal_of_ne_bot (h_sup_ne_bot (fun v => -y v))]
    have h_sup_set : {t : EReal | ∃ y : V → ℤ, t = KR c r B x y} =
        {t : EReal | ∃ p : V → ℤ,
          t = ((∑ i, ((0 : ℤ) : ℝ) * (p i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate φ p)} := by
      ext t
      simp only [Set.mem_setOf_eq, Int.cast_zero, zero_mul, Finset.sum_const_zero,
        EReal.coe_zero, zero_sub]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨fun v => -y v, h_kr_eq y⟩
      · rintro ⟨p, rfl⟩
        refine ⟨fun v => -p v, ?_⟩
        have h := h_kr_eq (fun v => -p v)
        simp only [neg_neg] at h
        exact h.symm
    have h_outer_ne_bot : sSup {t : EReal | ∃ p : V → ℤ,
        t = ((∑ i, ((0 : ℤ) : ℝ) * (p i : ℝ) : ℝ) : EReal) -
          ToEReal (ConvexConjugate φ p)} ≠ ⊥ := by
      intro hbot
      cases hcp0 : ConvexConjugate φ p0 with
      | top => exact hp0 hcp0
      | coe rp0 =>
        have hle : (((∑ i, ((0 : ℤ) : ℝ) * (p0 i : ℝ) : ℝ) : EReal) -
            ToEReal (ConvexConjugate φ p0)) ≤ ⊥ := by
          rw [← hbot]
          exact le_sSup ⟨p0, rfl⟩
        rw [hcp0, toEReal_coe, ← EReal.coe_sub] at hle
        exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
    rw [h_sup_set, ← toEReal_fromEReal_of_ne_bot h_outer_ne_bot]
    change ToEReal (ConvexConjugate (ConvexConjugate φ) (fun _ => 0)) =
      ToEReal (Fr c r B x (fun _ => 0))
    rw [hφ_biconj]
  · push_neg at hφ_nontop
    have h_kr_top : ∀ y, KR c r B x y = ⊤ := by
      intro y
      unfold KR
      apply le_antisymm le_top
      apply le_sInf
      rintro t ⟨u, rfl⟩
      have hu : Fr c r B x u = ⊤ := hφ_nontop u
      rw [hu, toEReal_top, EReal.top_add_coe]
    have h_fr0 : Fr c r B x (fun _ => 0) = ⊤ := hφ_nontop (fun _ => 0)
    rw [h_fr0, toEReal_top]
    apply le_antisymm le_top
    have : (⊤ : EReal) = KR c r B x (fun _ => 0) := (h_kr_top (fun _ => 0)).symm
    exact le_sSup ⟨fun _ => 0, this⟩
