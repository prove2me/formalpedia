-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.dual_optimal_value_properties
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:29:16.411869+00:00
-- url     : https://prove2.me/submissions/7f052aa1-0cf2-41b0-8111-54272b82ca35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConcaveConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsNegOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GammaR
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

private lemma mExchangeAxiom_indicator (B : Set (V → ℤ)) (hB : ExchangeAxiomB B) :
    MExchangeAxiom (IndicatorWT B) := by
  intro u1 hu1 u2 hu2 i hi
  simp only [DomZ, Set.mem_setOf_eq] at hu1 hu2
  have hu1B : u1 ∈ B := by
    by_contra hnot
    apply hu1
    simp [IndicatorWT, hnot]
  have hu2B : u2 ∈ B := by
    by_contra hnot
    apply hu2
    simp [IndicatorWT, hnot]
  rcases hB u1 hu1B u2 hu2B i hi with ⟨j, hj, hj1B, hj2B⟩
  refine ⟨j, hj, ?_⟩
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

private def LinearTilt (v x : V → ℤ) : ℝ := -∑ i, (x i : ℝ) * (v i : ℝ)

private lemma mExchangeAxiom_add_linear (c : (V → ℤ) → WithTop ℝ)
    (hc : MExchangeAxiom c) (v : V → ℤ) :
    MExchangeAxiom (fun x => c x + (LinearTilt v x : WithTop ℝ)) := by
  have h_dom : DomZ (fun x => c x + (LinearTilt v x : WithTop ℝ)) = DomZ c := by
    ext x
    simp only [DomZ, Set.mem_setOf_eq]
    cases c x with
    | top => simp
    | coe r =>
      rw [← WithTop.coe_add]
      simp
  intro x hx y hy u hu
  rw [h_dom] at hx hy
  rcases hc x hx y hy u hu with ⟨w0, hw0, h_ineq⟩
  refine ⟨w0, hw0, ?_⟩
  dsimp only []
  let x' : V → ℤ := fun w => x w - IndicatorVec {u} w + IndicatorVec {w0} w
  let y' : V → ℤ := fun w => y w + IndicatorVec {u} w - IndicatorVec {w0} w
  have hL_sum : LinearTilt v x + LinearTilt v y = LinearTilt v x' + LinearTilt v y' := by
    dsimp [LinearTilt, x', y']
    rw [← neg_add, ← neg_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  cases hcx : c x with
  | top => exact False.elim (hx hcx)
  | coe rcx =>
    cases hcy : c y with
    | top => exact False.elim (hy hcy)
    | coe rcy =>
      cases hcx' : c x' with
      | top =>
        change c x + c y ≥ c x' + c y' at h_ineq
        rw [hcx, hcy, hcx', top_add, ← WithTop.coe_add] at h_ineq
        exact False.elim (WithTop.coe_ne_top (top_le_iff.mp h_ineq))
      | coe rcx' =>
        cases hcy' : c y' with
        | top =>
          change c x + c y ≥ c x' + c y' at h_ineq
          rw [hcx, hcy, hcy', add_top, ← WithTop.coe_add] at h_ineq
          exact False.elim (WithTop.coe_ne_top (top_le_iff.mp h_ineq))
        | coe rcy' =>
          change c x + c y ≥ c x' + c y' at h_ineq
          rw [ge_iff_le, hcx, hcy, hcx', hcy', ← WithTop.coe_add, ← WithTop.coe_add,
            WithTop.coe_le_coe] at h_ineq
          rw [ge_iff_le]
          change ((rcx' : WithTop ℝ) + (LinearTilt v x' : WithTop ℝ)) +
              ((rcy' : WithTop ℝ) + (LinearTilt v y' : WithTop ℝ)) ≤
            ((rcx : WithTop ℝ) + (LinearTilt v x : WithTop ℝ)) +
              ((rcy : WithTop ℝ) + (LinearTilt v y : WithTop ℝ))
          repeat rw [← WithTop.coe_add]
          rw [WithTop.coe_le_coe]
          linarith

private lemma eReal_add_coe_le_iff (a b : EReal) (r : ℝ) :
    a + (r : EReal) ≤ b ↔ a ≤ b - (r : EReal) := by
  cases a using EReal.rec with
  | bot =>
    rw [EReal.bot_add]
    simp
  | top =>
    rw [EReal.top_add_coe, top_le_iff, top_le_iff]
    cases b using EReal.rec with
    | bot => simp
    | top => simp
    | coe rb =>
      rw [← EReal.coe_sub]
      constructor <;> intro h <;> exact False.elim (EReal.coe_ne_top _ h)
  | coe ra =>
    cases b using EReal.rec with
    | bot =>
      rw [← EReal.coe_add, EReal.bot_sub, le_bot_iff, le_bot_iff]
      simp [EReal.coe_ne_bot]
    | top =>
      simp
    | coe rb =>
      rw [← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith

private lemma eReal_le_add_coe_iff (a b : EReal) (r : ℝ) :
    a ≤ b + (r : EReal) ↔ a - (r : EReal) ≤ b := by
  cases a using EReal.rec with
  | bot =>
    rw [EReal.bot_sub]
    simp
  | top =>
    rw [EReal.top_sub_coe, top_le_iff, top_le_iff]
    cases b using EReal.rec with
    | bot => simp
    | top => simp
    | coe rb =>
      rw [← EReal.coe_add]
      constructor <;> intro h <;> exact False.elim (EReal.coe_ne_top _ h)
  | coe ra =>
    cases b using EReal.rec with
    | bot =>
      rw [← EReal.coe_sub, EReal.bot_add, le_bot_iff, le_bot_iff]
      constructor <;> intro h <;> exact False.elim (EReal.coe_ne_bot _ h)
    | top =>
      rw [EReal.top_add_coe]
      simp
    | coe rb =>
      rw [← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith

private lemma eReal_le_sub_coe_iff (a b : EReal) (r : ℝ) :
    a ≤ b - (r : EReal) ↔ a + (r : EReal) ≤ b :=
  (eReal_add_coe_le_iff a b r).symm

private lemma eReal_swap_step1 (A K F : EReal) (rv ry : ℝ)
    (h1 : A ≤ K - (rv : EReal)) (h2 : K ≤ F + (ry : EReal)) :
    A - (ry : EReal) ≤ F - (rv : EReal) := by
  rw [← eReal_le_add_coe_iff]
  apply le_trans h1
  rw [← eReal_le_add_coe_iff]
  apply le_trans h2
  cases F using EReal.rec with
  | bot => simp
  | top => simp [EReal.top_add_coe, EReal.top_sub_coe]
  | coe rf =>
    repeat rw [← EReal.coe_add]
    repeat rw [← EReal.coe_sub]
    repeat rw [← EReal.coe_add]
    rw [EReal.coe_le_coe_iff]
    linarith

private lemma eReal_swap_step2 (A K F : EReal) (rv ry : ℝ)
    (h1 : A ≤ K + (ry : EReal)) (h2 : K ≤ F - (rv : EReal)) :
    A + (rv : EReal) ≤ F + (ry : EReal) := by
  rw [eReal_add_coe_le_iff]
  apply le_trans h1
  rw [eReal_add_coe_le_iff]
  apply le_trans h2
  cases F using EReal.rec with
  | bot => simp
  | top => simp [EReal.top_add_coe, EReal.top_sub_coe]
  | coe rf =>
    repeat rw [← EReal.coe_sub]
    repeat rw [← EReal.coe_add]
    repeat rw [← EReal.coe_sub]
    rw [EReal.coe_le_coe_iff]
    linarith

theorem solution (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hcZ : IsIntegerValuedFn c) (hrZ : IsIntegerValuedFn r)
    (hB : ExchangeAxiomB B) (hBbdd : B.Finite) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r)
    (hr0 : r (fun _ => (0 : ℤ)) = 0) :
    (∀ x, ToEReal (Fr c r B x (fun _ => 0)) = -(ConcaveConjE (GammaR c r B) (fun v => -x v))) ∧
    (IsNegOf L2Convex (GammaR c r B) ∨ ∀ v, GammaR c r B v = ⊤) := by
  have h_gamma_eq : ∀ v : V → ℤ,
      GammaR c r B v = sInf {t : EReal | ∃ x : V → ℤ,
        t = ToEReal (Fr c r B x (fun _ => 0)) - ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal)} := by
    intro v
    let c_v : (V → ℤ) → WithTop ℝ := fun x => c x + (LinearTilt v x : WithTop ℝ)
    have hc_v : MExchangeAxiom c_v := mExchangeAxiom_add_linear c hc v
    have hc_v_Z : IsIntegerValuedFn c_v := by
      intro x
      dsimp [c_v]
      rcases hcZ x with hcx | ⟨kc, hcx⟩
      · left
        simp [hcx]
      · right
        refine ⟨kc - ∑ i, x i * v i, ?_⟩
        rw [hcx, ← WithTop.coe_add]
        congr 1
        dsimp [LinearTilt]
        push_cast
        ring
    have h_fr_eq : ∀ x u : V → ℤ,
        ToEReal (Fr r c_v B u x) =
          ToEReal (Fr c r B x u) - ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal) := by
      intro x u
      have h_add_comm : (fun w => u w + x w) = (fun w => x w + u w) := by
        funext w
        omega
      unfold Fr F0
      dsimp [c_v]
      rw [h_add_comm]
      cases hcx : c x with
      | top => simp [toEReal_top]
      | coe rcx =>
        cases hru : r u with
        | top => simp [toEReal_top]
        | coe rru =>
          unfold IndicatorWT
          split_ifs with hmem
          · rw [add_zero, add_zero, ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add,
              toEReal_coe, toEReal_coe, ← EReal.coe_sub]
            congr 1
            dsimp [LinearTilt]
            ring
          · simp [toEReal_top]
    have h_kr_cv0 : ∀ u : V → ℤ,
        KR r c_v B u (fun _ => 0) =
          sInf {t : EReal | ∃ x : V → ℤ,
            t = ToEReal (Fr c r B x u) - ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal)} := by
      intro u
      unfold KR
      congr 1
      ext t
      simp only [Set.mem_setOf_eq, Int.cast_zero, mul_zero, Finset.sum_const_zero,
        EReal.coe_zero, add_zero, h_fr_eq]
    have h_grBig_swap : ∀ y : V → ℤ,
        GRBig c r B y v =
          sInf {t : EReal | ∃ u : V → ℤ,
            t = KR r c_v B u (fun _ => 0) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)} := by
      intro y
      unfold GRBig
      apply le_antisymm
      · apply le_sInf
        rintro t ⟨u, rfl⟩
        rw [eReal_le_add_coe_iff, h_kr_cv0 u]
        apply le_sInf
        rintro s ⟨x, rfl⟩
        have h_le1 : sInf {t : EReal | ∃ z, t = KR c r B z y - ((∑ i, (z i : ℝ) * (v i : ℝ) : ℝ) : EReal)} ≤
            KR c r B x y - ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal) :=
          sInf_le ⟨x, rfl⟩
        have h_le2 : KR c r B x y ≤
            ToEReal (Fr c r B x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal) :=
          sInf_le ⟨u, rfl⟩
        exact eReal_swap_step1 _ _ _ _ _ h_le1 h_le2
      · apply le_sInf
        rintro t ⟨x, rfl⟩
        rw [eReal_le_sub_coe_iff]
        unfold KR
        apply le_sInf
        rintro s ⟨u, rfl⟩
        have h_le1 : sInf {t : EReal | ∃ u',
            t = KR r c_v B u' (fun _ => 0) + ((∑ i, (u' i : ℝ) * (y i : ℝ) : ℝ) : EReal)} ≤
            KR r c_v B u (fun _ => 0) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal) :=
          sInf_le ⟨u, rfl⟩
        have h_le2 : KR r c_v B u (fun _ => 0) ≤
            ToEReal (Fr c r B x u) - ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal) := by
          rw [h_kr_cv0 u]
          exact sInf_le ⟨x, rfl⟩
        exact eReal_swap_step2 _ _ _ _ _ h_le1 h_le2
    have h_lkc := (lagrangian_kernel_convexity r c_v B hB hc_v).2.2.2 hr (fun _ => 0)
    have h_embed : ∃ φ : (V → ℤ) → WithTop ℝ,
        M2Convex φ ∧ ∀ u, KR r c_v B u (fun _ => 0) = ToEReal (φ u) := by
      rcases h_lkc with ⟨φ, hφ_M2, hφ_eq⟩ | h_inf
      · exact ⟨φ, hφ_M2, hφ_eq⟩
      · refine ⟨fun _ => ⊤, m2Convex_top, fun u => ?_⟩
        rcases kr_int_or_top r c_v B hrZ hc_v_Z hBbdd u (fun _ => 0) with htop | ⟨k, hk⟩
        · exact htop
        · rcases h_inf u with htop | hbot
          · exact htop
          · rw [hk] at hbot
            exact False.elim (EReal.coe_ne_bot _ hbot)
    rcases h_embed with ⟨φ, hφ_M2, hφ_eq⟩
    have hφ_Z : IsIntegerValuedFn φ := by
      intro u
      rcases kr_int_or_top r c_v B hrZ hc_v_Z hBbdd u (fun _ => 0) with htop | ⟨k, hk⟩
      · left
        apply toEReal_injective
        rw [← hφ_eq u, htop, toEReal_top]
      · right
        refine ⟨k, ?_⟩
        apply toEReal_injective
        rw [← hφ_eq u, hk, toEReal_coe]
    have hφ_biconj : ConvexConjugate (ConvexConjugate φ) = φ :=
      ((m2_l2_conjugacy_correspondence).1 φ hφ_M2 hφ_Z).2
    rw [← h_kr_cv0 (fun _ => 0), hφ_eq (fun _ => 0)]
    by_cases hφ_nontop : ∃ u0, φ u0 ≠ ⊤
    · rcases biconjugate_recovery_aux φ hφ_biconj hφ_nontop with ⟨h_sup_ne_bot, ⟨p0, hp0⟩⟩
      have h_gr_eq : ∀ y, GRBig c r B y v = -ToEReal (ConvexConjugate φ (fun w => -y w)) := by
        intro y
        rw [h_grBig_swap y]
        have h_set : {t : EReal | ∃ u : V → ℤ,
            t = KR r c_v B u (fun _ => 0) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)} =
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
            rw [hφ_eq u, h_sum, eReal_neg_neg_coe_sub]
          · rintro ⟨u, rfl⟩
            refine ⟨u, ?_⟩
            have h_sum : (∑ i, ((-y i : ℤ) : ℝ) * (u i : ℝ)) = -(∑ i, (u i : ℝ) * (y i : ℝ)) := by
              rw [← Finset.sum_neg_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              push_cast
              ring
            rw [hφ_eq u, h_sum, eReal_neg_neg_coe_sub]
        rw [h_set, eReal_sInf_neg_eq_neg_sSup]
        unfold ConvexConjugate
        rw [toEReal_fromEReal_of_ne_bot (h_sup_ne_bot (fun w => -y w))]
      have h_sup_set : {t : EReal | ∃ y : V → ℤ, t = GRBig c r B y v} =
          {t : EReal | ∃ p : V → ℤ,
            t = ((∑ i, ((0 : ℤ) : ℝ) * (p i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate φ p)} := by
        ext t
        simp only [Set.mem_setOf_eq, Int.cast_zero, zero_mul, Finset.sum_const_zero,
          EReal.coe_zero, zero_sub]
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨fun w => -y w, h_gr_eq y⟩
        · rintro ⟨p, rfl⟩
          refine ⟨fun w => -p w, ?_⟩
          have h := h_gr_eq (fun w => -p w)
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
      unfold GammaR
      rw [h_sup_set, ← toEReal_fromEReal_of_ne_bot h_outer_ne_bot]
      change ToEReal (ConvexConjugate (ConvexConjugate φ) (fun _ => 0)) = ToEReal (φ (fun _ => 0))
      rw [hφ_biconj]
    · push_neg at hφ_nontop
      have h_gr_top : ∀ y, GRBig c r B y v = ⊤ := by
        intro y
        rw [h_grBig_swap y]
        apply le_antisymm le_top
        apply le_sInf
        rintro t ⟨u, rfl⟩
        rw [hφ_eq u, hφ_nontop u, toEReal_top, EReal.top_add_coe]
      rw [hφ_nontop (fun _ => 0), toEReal_top]
      unfold GammaR
      apply le_antisymm le_top
      have : (⊤ : EReal) = GRBig c r B (fun _ => 0) v := (h_gr_top (fun _ => 0)).symm
      exact le_sSup ⟨fun _ => 0, this⟩
  let ψ : (V → ℤ) → WithTop ℝ := fun x => Fr c r B x (fun _ => 0)
  have hψ_eq : ∀ x, ψ x = c x + IndicatorWT B x := by
    intro x
    dsimp [ψ]
    unfold Fr F0
    have h_add_zero : (fun v => x v + (0 : ℤ)) = x := by
      funext v
      omega
    rw [h_add_zero, hr0, add_zero]
  have hψ_M2 : M2Convex ψ := by
    refine ⟨c, IndicatorWT B, hc, mExchangeAxiom_indicator B hB, ?_⟩
    funext x
    exact hψ_eq x
  have hψ_Z : IsIntegerValuedFn ψ := by
    intro x
    rw [hψ_eq x]
    unfold IndicatorWT
    rcases hcZ x with hcx | ⟨kc, hcx⟩
    · left
      simp [hcx]
    · by_cases hmem : x ∈ B
      · right
        refine ⟨kc, ?_⟩
        rw [if_pos hmem, hcx, add_zero]
      · left
        simp [if_neg hmem]
  have hψ_corr := (m2_l2_conjugacy_correspondence).1 ψ hψ_M2 hψ_Z
  have hψ_L2 : L2Convex (ConvexConjugate ψ) := hψ_corr.1
  have hψ_biconj : ConvexConjugate (ConvexConjugate ψ) = ψ := hψ_corr.2
  by_cases hψ_nontop : ∃ x0, ψ x0 ≠ ⊤
  · rcases biconjugate_recovery_aux ψ hψ_biconj hψ_nontop with ⟨h_sup_ne_bot, ⟨p0, hp0⟩⟩
    have h_gamma_cc : ∀ v, GammaR c r B v = -ToEReal (ConvexConjugate ψ v) := by
      intro v
      rw [h_gamma_eq v]
      have h_set : {t : EReal | ∃ x : V → ℤ,
          t = ToEReal (Fr c r B x (fun _ => 0)) - ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal)} =
          {t : EReal | ∃ x : V → ℤ,
            t = -(((∑ i, (v i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (ψ x))} := by
        ext t
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨x, rfl⟩
          refine ⟨x, ?_⟩
          rw [eReal_neg_coe_sub]
          congr 2
          refine Finset.sum_congr rfl fun i _ => mul_comm _ _
        · rintro ⟨x, rfl⟩
          refine ⟨x, ?_⟩
          rw [eReal_neg_coe_sub]
          congr 2
          refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [h_set, eReal_sInf_neg_eq_neg_sSup]
      unfold ConvexConjugate
      rw [toEReal_fromEReal_of_ne_bot (h_sup_ne_bot v)]
    refine ⟨?_, Or.inl ⟨ConvexConjugate ψ, hψ_L2, h_gamma_cc⟩⟩
    intro x
    unfold ConcaveConjE
    have h_set : {t : EReal | ∃ v : V → ℤ,
        t = ((∑ i, ((-x i : ℤ) : ℝ) * (v i : ℝ) : ℝ) : EReal) - GammaR c r B v} =
        {t : EReal | ∃ v : V → ℤ,
          t = -(((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate ψ v))} := by
      ext t
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨v, ?_⟩
        have h_sum : (∑ i, ((-x i : ℤ) : ℝ) * (v i : ℝ)) = -(∑ i, (x i : ℝ) * (v i : ℝ)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          push_cast
          ring
        rw [h_gamma_cc v, h_sum, eReal_neg_coe_sub, sub_eq_add_neg, sub_eq_add_neg,
          neg_neg, EReal.coe_neg, add_comm]
      · rintro ⟨v, rfl⟩
        refine ⟨v, ?_⟩
        have h_sum : (∑ i, ((-x i : ℤ) : ℝ) * (v i : ℝ)) = -(∑ i, (x i : ℝ) * (v i : ℝ)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          push_cast
          ring
        rw [h_gamma_cc v, h_sum, eReal_neg_coe_sub, sub_eq_add_neg, sub_eq_add_neg,
          neg_neg, EReal.coe_neg, add_comm]
    have h_outer_ne_bot : sSup {s : EReal | ∃ v : V → ℤ,
        s = ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal) - ToEReal (ConvexConjugate ψ v)} ≠ ⊥ := by
      intro hbot
      cases hcp0 : ConvexConjugate ψ p0 with
      | top => exact hp0 hcp0
      | coe rp0 =>
        have hle : (((∑ i, (x i : ℝ) * (p0 i : ℝ) : ℝ) : EReal) -
            ToEReal (ConvexConjugate ψ p0)) ≤ ⊥ := by
          rw [← hbot]
          exact le_sSup ⟨p0, rfl⟩
        rw [hcp0, toEReal_coe, ← EReal.coe_sub] at hle
        exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
    rw [h_set, eReal_sInf_neg_eq_neg_sSup, neg_neg, ← toEReal_fromEReal_of_ne_bot h_outer_ne_bot]
    change ToEReal (Fr c r B x (fun _ => 0)) = ToEReal (ConvexConjugate (ConvexConjugate ψ) x)
    rw [hψ_biconj]
  · push_neg at hψ_nontop
    have h_gamma_top : ∀ v, GammaR c r B v = ⊤ := by
      intro v
      rw [h_gamma_eq v]
      apply le_antisymm le_top
      apply le_sInf
      rintro t ⟨x, rfl⟩
      have hx : Fr c r B x (fun _ => 0) = ⊤ := hψ_nontop x
      rw [hx, toEReal_top, EReal.top_sub_coe]
    refine ⟨?_, Or.inr h_gamma_top⟩
    intro x
    have hx : Fr c r B x (fun _ => 0) = ⊤ := hψ_nontop x
    rw [hx, toEReal_top]
    have h_cc_bot : ConcaveConjE (GammaR c r B) (fun v => -x v) = ⊥ := by
      unfold ConcaveConjE
      apply le_antisymm _ bot_le
      have : sInf {t : EReal | ∃ v : V → ℤ,
          t = ((∑ i, ((-x i : ℤ) : ℝ) * (v i : ℝ) : ℝ) : EReal) - GammaR c r B v} ≤
          ((∑ i, ((-x i : ℤ) : ℝ) * ((0 : ℤ) : ℝ) : ℝ) : EReal) - GammaR c r B (fun _ => 0) :=
        sInf_le ⟨fun _ => 0, rfl⟩
      rwa [h_gamma_top (fun _ => 0), EReal.sub_top] at this
    rw [h_cc_bot, EReal.neg_bot]
