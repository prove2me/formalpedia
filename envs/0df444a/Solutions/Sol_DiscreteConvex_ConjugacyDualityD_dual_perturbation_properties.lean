-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.dual_perturbation_properties
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:26:44.117657+00:00
-- url     : https://prove2.me/submissions/31f9e0d6-ec5b-4112-bdf3-1d4532a45c47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsNegOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRBig
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

private lemma sbf_comp_neg (g : (V → ℤ) → WithTop ℝ) (hg : SBF g) :
    SBF (fun y => g (fun w => -y w)) := by
  intro p q
  have h1 : (fun w => -(p ⊔ q) w) = (fun w => -p w) ⊓ (fun w => -q w) := by
    funext w
    change -(max (p w) (q w)) = min (-p w) (-q w)
    omega
  have h2 : (fun w => -(p ⊓ q) w) = (fun w => -p w) ⊔ (fun w => -q w) := by
    funext w
    change -(min (p w) (q w)) = max (-p w) (-q w)
    omega
  dsimp only []
  rw [h1, h2, add_comm (g ((fun w => -p w) ⊓ (fun w => -q w)))]
  exact hg (fun w => -p w) (fun w => -q w)

private lemma trf_comp_neg (g : (V → ℤ) → WithTop ℝ) (hg : TRF g) :
    TRF (fun y => g (fun w => -y w)) := by
  rcases hg with ⟨r, hr⟩
  refine ⟨-r, fun p => ?_⟩
  dsimp only []
  have h_eq : (fun w => -p w) = (fun w => -(p + 1) w) + 1 := by
    funext w
    change -p w = -(p w + 1) + 1
    omega
  have hr' := hr (fun w => -(p + 1) w)
  rw [← h_eq] at hr'
  cases hgp : g (fun w => -(p + 1) w) with
  | top =>
    rw [hgp, top_add] at hr'
    rw [hr', top_add]
  | coe v =>
    rw [hgp, ← WithTop.coe_add] at hr'
    rw [hr', ← WithTop.coe_add]
    congr 1
    ring

private lemma l2Convex_comp_neg (g : (V → ℤ) → WithTop ℝ) (hg : L2Convex g) :
    L2Convex (fun y => g (fun w => -y w)) := by
  rcases hg with ⟨g1, g2, ⟨hsbf1, htrf1⟩, ⟨hsbf2, htrf2⟩, rfl⟩
  refine ⟨fun y => g1 (fun w => -y w), fun y => g2 (fun w => -y w),
    ⟨sbf_comp_neg g1 hsbf1, trf_comp_neg g1 htrf1⟩,
    ⟨sbf_comp_neg g2 hsbf2, trf_comp_neg g2 htrf2⟩, ?_⟩
  funext p
  unfold InfConv
  congr 1
  ext L
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨p1, p2, hp, rfl⟩
    refine ⟨fun w => -p1 w, fun w => -p2 w, ?_, ?_⟩
    · funext w
      have hw := congr_fun hp w
      simp only [Pi.add_apply] at hw ⊢
      omega
    · simp only [neg_neg]
  · rintro ⟨p1, p2, hp, rfl⟩
    refine ⟨fun w => -p1 w, fun w => -p2 w, ?_, rfl⟩
    funext w
    have hw := congr_fun hp w
    simp only [Pi.add_apply] at hw ⊢
    omega

private lemma sInf_int_or_top_of_ne_bot (S : Set EReal)
    (hS : ∀ t ∈ S, t = ⊤ ∨ ∃ k : ℤ, t = ((k : ℝ) : EReal))
    (h_ne_bot : sInf S ≠ ⊥) :
    sInf S = ⊤ ∨ ∃ k : ℤ, sInf S = ((k : ℝ) : EReal) := by
  cases h_inf : sInf S using EReal.rec with
  | bot => exact False.elim (h_ne_bot h_inf)
  | top => exact Or.inl rfl
  | coe r_val =>
    right
    have h_ex : ∃ k : ℤ, ((k : ℝ) : EReal) ∈ S ∧ (k : ℝ) < r_val + 1 := by
      have hlt : sInf S < ((r_val + 1 : ℝ) : EReal) := by
        rw [h_inf, EReal.coe_lt_coe_iff]
        linarith
      rcases (sInf_lt_iff).mp hlt with ⟨t, htS, ht_lt⟩
      rcases hS t htS with rfl | ⟨k, rfl⟩
      · exact False.elim (not_lt_of_ge le_top ht_lt)
      · rw [EReal.coe_lt_coe_iff] at ht_lt
        exact ⟨k, htS, ht_lt⟩
    rcases h_ex with ⟨k0, hk0S, _⟩
    have h_bdd : ∀ k : ℤ, ((k : ℝ) : EReal) ∈ S → ⌊r_val⌋ ≤ k := by
      intro k hkS
      have hle : (r_val : EReal) ≤ ((k : ℝ) : EReal) := by
        rw [← h_inf]
        exact sInf_le hkS
      rw [EReal.coe_le_coe_iff] at hle
      exact Int.floor_le_iff.mpr (by linarith)
    let F : Finset ℤ := (Finset.Icc ⌊r_val⌋ k0).filter (fun k => ((k : ℝ) : EReal) ∈ S)
    have hF_ne : F.Nonempty := by
      refine ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h_bdd k0 hk0S, le_rfl⟩, hk0S⟩⟩
    rcases Finset.exists_min_image F (fun k : ℤ => k) hF_ne with ⟨k_min, hk_min_mem, hk_min_le⟩
    have hk_min_S : ((k_min : ℝ) : EReal) ∈ S := (Finset.mem_filter.mp hk_min_mem).2
    refine ⟨k_min, ?_⟩
    rw [← h_inf]
    apply le_antisymm
    · exact sInf_le hk_min_S
    · apply le_sInf
      intro t htS
      rcases hS t htS with rfl | ⟨k, rfl⟩
      · exact le_top
      · rw [EReal.coe_le_coe_iff, Int.cast_le]
        by_cases hk_le : k ≤ k0
        · exact hk_min_le k (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h_bdd k htS, hk_le⟩, htS⟩)
        · have hk_min_le_k0 : k_min ≤ k0 :=
            hk_min_le k0 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h_bdd k0 hk0S, le_rfl⟩, hk0S⟩)
          omega

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
    (_hr0 : r (fun _ => (0 : ℤ)) = 0) :
    (∀ y, GRBig c r B y (fun _ => 0) = GRSmall c r B y) ∧
    (∀ y, IsNegOf L2Convex (fun v => GRBig c r B y v) ∨ ∀ v, GRBig c r B y v = ⊤) ∧
    (∀ v, IsNegOf L2Convex (fun y => GRBig c r B y v) ∨ (∀ y, GRBig c r B y v = ⊥) ∨
      (∀ y, GRBig c r B y v = ⊤)) := by
  have h1 : ∀ y, GRBig c r B y (fun _ => 0) = GRSmall c r B y := by
    intro y
    simp only [GRBig, GRSmall, Int.cast_zero, mul_zero, Finset.sum_const_zero,
      EReal.coe_zero, sub_zero]
  have h2 : ∀ y, IsNegOf L2Convex (fun v => GRBig c r B y v) ∨ ∀ v, GRBig c r B y v = ⊤ := by
    intro y
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
    have h_L2 : L2Convex (ConvexConjugate h) :=
      ((m2_l2_conjugacy_correspondence).1 h hM2 hZ).1
    by_cases h_nontop : ∃ z0, h z0 ≠ ⊤
    · left
      rcases h_nontop with ⟨z0, hz0⟩
      have h_sup_ne_bot : ∀ v : V → ℤ, sSup {s : EReal | ∃ z : V → ℤ,
          s = ((∑ i, (v i : ℝ) * (z i : ℝ) : ℝ) : EReal) - ToEReal (h z)} ≠ ⊥ := by
        intro v hbot
        cases hhz0 : h z0 with
        | top => exact hz0 hhz0
        | coe r0 =>
          have hle : (((∑ i, (v i : ℝ) * (z0 i : ℝ) : ℝ) : EReal) - ToEReal (h z0)) ≤ ⊥ := by
            rw [← hbot]
            exact le_sSup ⟨z0, rfl⟩
          rw [hhz0, toEReal_coe, ← EReal.coe_sub] at hle
          exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
      refine ⟨ConvexConjugate h, h_L2, fun v => ?_⟩
      dsimp only []
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
    · right
      push_neg at h_nontop
      intro v
      unfold GRBig
      apply le_antisymm le_top
      apply le_sInf
      rintro t ⟨z, rfl⟩
      rw [hh z, h_nontop z, toEReal_top, EReal.top_sub_coe]
  refine ⟨h1, h2, ?_⟩
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
  rcases h_lkc with ⟨φ, hφ_M2, hφ_eq⟩ | h_inf
  · dsimp only [] at hφ_eq
    have hφ_Z : IsIntegerValuedFn φ := by
      intro u
      have h_ne_bot : KR r c_v B u (fun _ => 0) ≠ ⊥ := by
        rw [hφ_eq u]
        cases φ u with
        | top => exact top_ne_bot
        | coe rφ => exact EReal.coe_ne_bot rφ
      have hS_int : ∀ t ∈ {t : EReal | ∃ x : V → ℤ,
          t = ToEReal (Fr r c_v B u x) + ((∑ i, (x i : ℝ) * ((0 : ℤ) : ℝ) : ℝ) : EReal)},
          t = ⊤ ∨ ∃ k : ℤ, t = ((k : ℝ) : EReal) := by
        rintro t ⟨x, rfl⟩
        exact kr_term_int_or_top r c_v B hrZ hc_v_Z u (fun _ => 0) x
      rcases sInf_int_or_top_of_ne_bot _ hS_int h_ne_bot with htop | ⟨k, hk⟩
      · left
        apply toEReal_injective
        rw [← hφ_eq u]
        exact htop
      · right
        refine ⟨k, ?_⟩
        apply toEReal_injective
        rw [← hφ_eq u, toEReal_coe]
        exact hk
    have hφ_L2 : L2Convex (ConvexConjugate φ) :=
      ((m2_l2_conjugacy_correspondence).1 φ hφ_M2 hφ_Z).1
    by_cases hφ_nontop : ∃ u0, φ u0 ≠ ⊤
    · left
      rcases hφ_nontop with ⟨u0, hu0⟩
      have h_sup_ne_bot : ∀ p : V → ℤ, sSup {s : EReal | ∃ u : V → ℤ,
          s = ((∑ i, (p i : ℝ) * (u i : ℝ) : ℝ) : EReal) - ToEReal (φ u)} ≠ ⊥ := by
        intro p hbot
        cases hφu0 : φ u0 with
        | top => exact hu0 hφu0
        | coe r0 =>
          have hle : (((∑ i, (p i : ℝ) * (u0 i : ℝ) : ℝ) : EReal) - ToEReal (φ u0)) ≤ ⊥ := by
            rw [← hbot]
            exact le_sSup ⟨u0, rfl⟩
          rw [hφu0, toEReal_coe, ← EReal.coe_sub] at hle
          exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
      refine ⟨fun y => ConvexConjugate φ (fun w => -y w), l2Convex_comp_neg _ hφ_L2, fun y => ?_⟩
      dsimp only []
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
    · right
      right
      push_neg at hφ_nontop
      intro y
      rw [h_grBig_swap y]
      apply le_antisymm le_top
      apply le_sInf
      rintro t ⟨u, rfl⟩
      rw [hφ_eq u, hφ_nontop u, toEReal_top, EReal.top_add_coe]
  · by_cases h_ex_bot : ∃ u0, KR r c_v B u0 (fun _ => 0) = ⊥
    · right
      left
      rcases h_ex_bot with ⟨u0, hu0⟩
      intro y
      rw [h_grBig_swap y]
      apply le_antisymm _ bot_le
      have : sInf {t : EReal | ∃ u : V → ℤ,
          t = KR r c_v B u (fun _ => 0) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)} ≤
          KR r c_v B u0 (fun _ => 0) + ((∑ i, (u0 i : ℝ) * (y i : ℝ) : ℝ) : EReal) :=
        sInf_le ⟨u0, rfl⟩
      rwa [hu0, EReal.bot_add] at this
    · right
      right
      push_neg at h_ex_bot
      intro y
      rw [h_grBig_swap y]
      apply le_antisymm le_top
      apply le_sInf
      rintro t ⟨u, rfl⟩
      rcases h_inf u with htop | hbot
      · rw [htop, EReal.top_add_coe]
      · exact False.elim (h_ex_bot u hbot)
