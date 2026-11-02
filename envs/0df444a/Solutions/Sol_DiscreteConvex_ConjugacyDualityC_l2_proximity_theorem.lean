-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityC.l2_proximity_theorem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T04:34:57.762872+00:00
-- url     : https://prove2.me/submissions/5c37ecdc-ab45-4785-8b62-ce6c243bb27a

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

private theorem l2p_gap_or_bound (s : Finset ℤ) (α : ℤ) (hα : 0 < α)
    (hs0 : 0 ∈ s) (hspos : ∀ z ∈ s, 0 ≤ z) :
    (∀ z ∈ s, z ≤ ((s.card : ℤ) - 1) * (α - 1)) ∨
    ∃ b ∈ s, 0 ≤ b ∧ (∃ c ∈ s, b + α ≤ c) ∧
      ∀ z ∈ s, z ≤ b ∨ b + α ≤ z := by
  classical
  revert hs0 hspos
  refine Finset.strongInductionOn s ?_
  intro s ih hs0 hspos
  let m := s.max' ⟨0, hs0⟩
  have hm : m ∈ s := Finset.max'_mem s ⟨0, hs0⟩
  have hmax (z : ℤ) (hz : z ∈ s) : z ≤ m := Finset.le_max' s z hz
  have hmpos : 0 ≤ m := hspos m hm
  have hapos : 0 ≤ α - 1 := by omega
  have hcardpos : 0 ≤ (s.card : ℤ) - 1 := by
    have h := Finset.card_pos.mpr ⟨0, hs0⟩
    omega
  by_cases hm0 : m = 0
  · left
    intro z hz
    have hz0 : z ≤ 0 := by simpa only [hm0] using hmax z hz
    exact hz0.trans (mul_nonneg hcardpos hapos)
  let t := s.erase m
  have ht0 : 0 ∈ t := Finset.mem_erase.mpr ⟨Ne.symm hm0, hs0⟩
  have htpos : ∀ z ∈ t, 0 ≤ z := fun z hz => hspos z (Finset.mem_of_mem_erase hz)
  have htss : t ⊂ s := Finset.erase_ssubset hm
  rcases ih t htss ht0 htpos with htbound | ⟨b, hbt, hb0, ⟨c, hct, hbc⟩, hgap⟩
  · let b := t.max' ⟨0, ht0⟩
    have hbt : b ∈ t := Finset.max'_mem t ⟨0, ht0⟩
    have hbs : b ∈ s := Finset.mem_of_mem_erase hbt
    have hbmax (z : ℤ) (hz : z ∈ t) : z ≤ b := Finset.le_max' t z hz
    by_cases hmb : m ≤ b + (α - 1)
    · left
      intro z hz
      have hbtbound := htbound b hbt
      have hcard : (t.card : ℤ) + 1 = (s.card : ℤ) := by
        exact_mod_cast Finset.card_erase_add_one hm
      have hzmax := hmax z hz
      nlinarith
    · right
      have hbm : b + α ≤ m := by omega
      refine ⟨b, hbs, hspos b hbs, ⟨m, hm, hbm⟩, ?_⟩
      intro z hz
      by_cases hzm : z = m
      · exact Or.inr (hzm ▸ hbm)
      · exact Or.inl (hbmax z (Finset.mem_erase.mpr ⟨hzm, hz⟩))
  · right
    refine ⟨b, Finset.mem_of_mem_erase hbt, hb0, ⟨c, Finset.mem_of_mem_erase hct, hbc⟩, ?_⟩
    intro z hz
    by_cases hzm : z = m
    · right
      rw [hzm]
      exact hbc.trans (hmax c (Finset.mem_of_mem_erase hct))
    · exact hgap z (Finset.mem_erase.mpr ⟨hzm, hz⟩)

lemma l2p_toE_add (x y : WithTop ℝ) : ToEReal (x + y) = ToEReal x + ToEReal y := by
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe <;> rfl

lemma l2p_trf_iter (g : (V → ℤ) → WithTop ℝ) (r : ℝ)
    (hr : ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)) (z : V → ℤ) (k : ℤ) :
    g (fun v => z v + k) = g z + ((k * r : ℝ) : WithTop ℝ) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have : (fun v => z v + ((i : ℤ) + 1)) = (fun v => z v + (i : ℤ)) + 1 := by
      funext v; simp only [Pi.add_apply, Pi.one_apply]; ring
    rw [this, hr, ih, add_assoc, ← WithTop.coe_add]; congr 2; push_cast; ring
  | pred i ih =>
    have hw : (fun v => z v + (-(i : ℤ) - 1)) + 1 = (fun v => z v + -(i : ℤ)) := by
      funext v; simp only [Pi.add_apply, Pi.one_apply]; ring
    have h := hr (fun v => z v + (-(i : ℤ) - 1))
    rw [hw, ih] at h
    have h2 : g z + ((((-(i : ℤ)) : ℤ) * r : ℝ) : WithTop ℝ)
        = (g z + (((((-(i : ℤ) - 1) : ℤ)) * r : ℝ) : WithTop ℝ)) + (r : WithTop ℝ) := by
      rw [add_assoc, ← WithTop.coe_add]; congr 2; push_cast; ring
    rw [h2] at h
    exact ((WithTop.add_right_inj (WithTop.coe_ne_top)).mp h).symm

lemma l2p_bdd (g1 g2 : (V → ℤ) → WithTop ℝ) (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥) (x : V → ℤ) :
    BddBelow {L : WithTop ℝ | ∃ p1 p2 : V → ℤ, x = p1 + p2 ∧ L = g1 p1 + g2 p2} := by
  have h := hE x
  unfold InfConvE at h
  obtain ⟨β, hβ⟩ := WithBot.ne_bot_iff_exists.mp h
  refine ⟨β, ?_⟩
  rintro L ⟨a, b, hx, rfl⟩
  have : sInf {L : EReal | ∃ p1 p2 : V → ℤ, x = p1 + p2 ∧
      L = ToEReal (g1 p1) + ToEReal (g2 p2)} ≤ ToEReal (g1 a) + ToEReal (g2 b) :=
    sInf_le ⟨a, b, hx, rfl⟩
  rw [← l2p_toE_add, ← hβ] at this
  exact WithBot.coe_le_coe.mp this

lemma l2p_lb (g1 g2 : (V → ℤ) → WithTop ℝ) (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥) (x a b : V → ℤ)
    (h : x = a + b) : InfConv g1 g2 x ≤ g1 a + g2 b :=
  csInf_le (l2p_bdd g1 g2 hE x) ⟨a, b, h, rfl⟩

lemma l2p_glb (g1 g2 : (V → ℤ) → WithTop ℝ) (x : V → ℤ) (c : WithTop ℝ)
    (h : ∀ a b : V → ℤ, x = a + b → c ≤ g1 a + g2 b) : c ≤ InfConv g1 g2 x :=
  le_csInf ⟨_, x, 0, by simp, rfl⟩ (by rintro L ⟨a, b, hx, rfl⟩; exact h a b hx)

lemma l2p_approx (g1 g2 : (V → ℤ) → WithTop ℝ) (x : V → ℤ) (m : ℝ)
    (hm : InfConv g1 g2 x = (m : WithTop ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : V → ℤ, x = a + b ∧ g1 a + g2 b < ((m + ε : ℝ) : WithTop ℝ) := by
  have hlt : InfConv g1 g2 x < ((m + ε : ℝ) : WithTop ℝ) := by
    rw [hm]; exact WithTop.coe_lt_coe.mpr (by linarith)
  unfold InfConv at hlt
  have hne : ({L : WithTop ℝ | ∃ p1 p2 : V → ℤ, x = p1 + p2 ∧ L = g1 p1 + g2 p2}).Nonempty :=
    ⟨g1 x + g2 0, x, 0, by simp, rfl⟩
  obtain ⟨L, ⟨a, b, hx, rfl⟩, hL⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨a, b, hx, hL⟩

lemma l2p_cut_zero (g : (V → ℤ) → WithTop ℝ) (hs : SBF g)
    (hshift : ∀ (q : V → ℤ) (k : ℤ), g (fun v => q v + k) = g q)
    (h0 : g 0 ≠ ⊤) (α : ℤ) (hα : 0 ≤ α) (q : V → ℤ) (hq : g q ≠ ⊤) (Y : Finset V)
    (hhigh : ∀ v ∈ Y, α ≤ q v) (hlow : ∀ v ∉ Y, q v ≤ 0) :
    g (fun v => q v - α * IndicatorVec Y v) + g (fun v => α * IndicatorVec Y v) ≤ g q + g 0 := by
  let A : V → ℤ := fun v => max (q v) 0
  let C : V → ℤ := fun v => A v - α * IndicatorVec Y v
  let D : V → ℤ := fun v => α * IndicatorVec Y v
  have hA : g A ≠ ⊤ := by
    have he := hs q 0
    have hsum : g (q ⊔ 0) + g (q ⊓ 0) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hq, h0⟩) he
    exact (WithTop.add_ne_top.mp hsum).1
  have hsup : (fun v => A v - α) ⊔ 0 = C := by
    funext v
    by_cases hv : v ∈ Y
    · have hh := hhigh v hv
      simp [C, A, IndicatorVec, hv] <;> omega
    · have hl := hlow v hv
      simp [C, A, IndicatorVec, hv] <;> omega
  have hinf : (fun v => A v - α) ⊓ 0 = fun v => D v - α := by
    funext v
    by_cases hv : v ∈ Y
    · have hh := hhigh v hv
      simp [D, A, IndicatorVec, hv] <;> omega
    · have hl := hlow v hv
      simp [D, A, IndicatorVec, hv] <;> omega
  have he1 : g C + g D ≤ g A + g 0 := by
    have he := hs (fun v => A v - α) 0
    rw [hsup, hinf] at he
    simpa only [sub_eq_add_neg, hshift] using he
  have hC : g C ≠ ⊤ := (WithTop.add_ne_top.mp
    (ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hA, h0⟩) he1)).1
  have hsup2 : q ⊔ C = A := by
    funext v
    by_cases hv : v ∈ Y
    · have hh := hhigh v hv
      simp [C, A, IndicatorVec, hv] <;> omega
    · have hl := hlow v hv
      simp [C, A, IndicatorVec, hv] <;> omega
  have hinf2 : q ⊓ C = fun v => q v - α * IndicatorVec Y v := by
    funext v
    by_cases hv : v ∈ Y
    · have hh := hhigh v hv
      simp [C, A, IndicatorVec, hv] <;> omega
    · have hl := hlow v hv
      simp [C, A, IndicatorVec, hv] <;> omega
  have he2 : g A + g (fun v => q v - α * IndicatorVec Y v) ≤ g q + g C := by
    simpa only [hsup2, hinf2] using hs q C
  have he := add_le_add he1 he2
  have hreorder : (g (fun v => q v - α * IndicatorVec Y v) + g D) + (g A + g C) ≤
      (g q + g 0) + (g A + g C) := by
    simpa only [add_assoc, add_comm, add_left_comm] using he
  exact (add_le_add_iff_left_of_ne_top (WithTop.add_ne_top.mpr ⟨hA, hC⟩)).mp hreorder

lemma l2p_cut_shift (g : (V → ℤ) → WithTop ℝ) (hs : SBF g)
    (hshift : ∀ (q : V → ℤ) (k : ℤ), g (fun v => q v + k) = g q)
    (a q : V → ℤ) (ha : g a ≠ ⊤) (hq : g q ≠ ⊤) (α : ℤ) (hα : 0 ≤ α) (k : ℤ) (Y : Finset V)
    (hhigh : ∀ v ∈ Y, k + α ≤ q v - a v) (hlow : ∀ v ∉ Y, q v - a v ≤ k) :
    g (fun v => q v - α * IndicatorVec Y v) + g (fun v => a v + α * IndicatorVec Y v) ≤
      g q + g a := by
  let F : (V → ℤ) → WithTop ℝ := fun x => g (fun v => a v + x v)
  have hFs : SBF F := by
    intro x y
    have hh := hs (fun v => a v + x v) (fun v => a v + y v)
    have hsup : (fun v => a v + x v) ⊔ (fun v => a v + y v) = fun v => a v + (x ⊔ y) v := by
      funext v; change max (a v + x v) (a v + y v) = a v + max (x v) (y v); omega
    have hinf : (fun v => a v + x v) ⊓ (fun v => a v + y v) = fun v => a v + (x ⊓ y) v := by
      funext v; change min (a v + x v) (a v + y v) = a v + min (x v) (y v); omega
    simpa only [F, hsup, hinf] using hh
  have hFshift (x : V → ℤ) (c : ℤ) : F (fun v => x v + c) = F x := by
    simpa only [F, add_assoc] using hshift (fun v => a v + x v) c
  have hF0 : F 0 ≠ ⊤ := by
    have : (fun v => a v + (0 : V → ℤ) v) = a := by funext v; simp
    simpa only [F, this] using ha
  let x : V → ℤ := fun v => q v - a v - k
  have hFx_eq : F x = g q := by
    have : (fun v => a v + x v) = fun v => q v + (-k) := by funext v; dsimp [x]; omega
    simpa only [F, this] using hshift q (-k)
  have hFx : F x ≠ ⊤ := by rwa [hFx_eq]
  have hhx : ∀ v ∈ Y, α ≤ x v := fun v hv => by have := hhigh v hv; dsimp [x]; omega
  have hlx : ∀ v ∉ Y, x v ≤ 0 := fun v hv => by have := hlow v hv; dsimp [x]; omega
  have hmain := l2p_cut_zero F hFs hFshift hF0 α hα x hFx Y hhx hlx
  have h1 : F (fun v => x v - α * IndicatorVec Y v) = g (fun v => q v - α * IndicatorVec Y v) := by
    have : (fun v => a v + (x v - α * IndicatorVec Y v)) =
        fun v => (q v - α * IndicatorVec Y v) + (-k) := by funext v; dsimp [x]; omega
    simpa only [F, this] using hshift (fun v => q v - α * IndicatorVec Y v) (-k)
  have h2 : F (fun v => α * IndicatorVec Y v) = g (fun v => a v + α * IndicatorVec Y v) := rfl
  have h3 : F 0 = g a := by
    dsimp [F]; congr 1; funext v; simp
  rw [h1, h2, hFx_eq, h3] at hmain
  exact hmain

lemma l2p_cut_neg_shift (g : (V → ℤ) → WithTop ℝ) (hs : SBF g)
    (hshift : ∀ (q : V → ℤ) (k : ℤ), g (fun v => q v + k) = g q)
    (b q : V → ℤ) (hb : g b ≠ ⊤) (hq : g q ≠ ⊤) (α : ℤ) (hα : 0 ≤ α) (k : ℤ) (Y2 : Finset V)
    (hhigh : ∀ v ∈ Y2, k + α ≤ -(q v - b v)) (hlow : ∀ v ∉ Y2, -(q v - b v) ≤ k) :
    g (fun v => q v + α * IndicatorVec Y2 v) + g (fun v => b v - α * IndicatorVec Y2 v) ≤
      g q + g b := by
  let Y2c : Finset V := Finset.univ.filter (fun v => v ∉ Y2)
  have hh' : ∀ v ∈ Y2c, (-k - α) + α ≤ q v - b v := by
    intro v hv
    have hv' : v ∉ Y2 := (Finset.mem_filter.mp hv).2
    have := hlow v hv'
    omega
  have hl' : ∀ v ∉ Y2c, q v - b v ≤ -k - α := by
    intro v hv
    have hv' : v ∈ Y2 := by
      by_contra hnot
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hnot⟩)
    have := hhigh v hv'
    omega
  have hmain := l2p_cut_shift g hs hshift b q hb hq α hα (-k - α) Y2c hh' hl'
  have e1 : g (fun v => q v - α * IndicatorVec Y2c v) =
      g (fun v => q v + α * IndicatorVec Y2 v) := by
    have : (fun v => q v + α * IndicatorVec Y2 v) =
        fun v => (q v - α * IndicatorVec Y2c v) + α := by
      funext v
      by_cases hv : v ∈ Y2 <;> simp [Y2c, IndicatorVec, hv] <;> omega
    rw [this, hshift]
  have e2 : g (fun v => b v + α * IndicatorVec Y2c v) =
      g (fun v => b v - α * IndicatorVec Y2 v) := by
    have : (fun v => b v - α * IndicatorVec Y2 v) =
        fun v => (b v + α * IndicatorVec Y2c v) + (-α) := by
      funext v
      by_cases hv : v ∈ Y2 <;> simp [Y2c, IndicatorVec, hv] <;> omega
    rw [this, hshift]
  rw [← e1, ← e2]
  exact hmain

lemma l2p_exists_joint_gap [Nonempty V] (δ1 δ2 d : V → ℤ) (α : ℤ) (hα : 0 < α)
    (hd : ∀ v, δ1 v + δ2 v = d v) (hd0 : ∀ v, 0 ≤ d v)
    (u : V) (hdu1 : δ1 u = 0) (hdu2 : δ2 u = 0)
    (v0 : V) (hv0 : 2 * ((Fintype.card V : ℤ) - 1) * (α - 1) < d v0) :
    ∃ k : ℤ, -δ2 v0 ≤ k ∧ k + α ≤ δ1 v0 ∧
      (∀ v, δ1 v ≤ k ∨ k + α ≤ δ1 v) ∧
      (∀ v, -δ2 v ≤ k ∨ k + α ≤ -δ2 v) := by
  classical
  let A1 : Finset ℤ := Finset.univ.image δ1
  let A2 : Finset ℤ := (Finset.univ.erase u).image (fun v => -δ2 v)
  let S : Finset ℤ := A1 ∪ A2
  have hmem1 : ∀ v : V, δ1 v ∈ S := fun v =>
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)
  have hmem2 : ∀ v : V, -δ2 v ∈ S := by
    intro v
    by_cases hvu : v = u
    · subst hvu
      have : -δ2 v = δ1 v := by omega
      rw [this]
      exact hmem1 v
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩, rfl⟩)
  have hScard : (S.card : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 1 := by
    have h1 : S.card ≤ A1.card + A2.card := Finset.card_union_le A1 A2
    have h2 : A1.card ≤ Fintype.card V := Finset.card_image_le
    have h3 : A2.card ≤ (Finset.univ.erase u).card := Finset.card_image_le
    have h4 : (Finset.univ.erase u).card + 1 = Fintype.card V :=
      Finset.card_erase_add_one (Finset.mem_univ u)
    omega
  let Sf : Finset ℤ := S.filter (fun z => -δ2 v0 ≤ z ∧ z ≤ δ1 v0)
  let S0 : Finset ℤ := Sf.image (fun z => z - (-δ2 v0))
  have hd_v0 := hd v0
  have hd0_v0 := hd0 v0
  have hs0 : 0 ∈ S0 := by
    refine Finset.mem_image.mpr ⟨-δ2 v0, Finset.mem_filter.mpr ⟨hmem2 v0, ?_⟩, by omega⟩
    omega
  have hspos : ∀ z ∈ S0, 0 ≤ z := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have := (Finset.mem_filter.mp hw).2.1
    omega
  have hsmax : ∀ z ∈ S0, z ≤ d v0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have := (Finset.mem_filter.mp hw).2.2
    omega
  have hdv0_mem : d v0 ∈ S0 := by
    refine Finset.mem_image.mpr ⟨δ1 v0, Finset.mem_filter.mpr ⟨hmem1 v0, ?_⟩, by omega⟩
    omega
  have hS0card : (S0.card : ℤ) - 1 ≤ 2 * ((Fintype.card V : ℤ) - 1) := by
    have h1 : S0.card ≤ Sf.card := Finset.card_image_le
    have h2 : Sf.card ≤ S.card := Finset.card_filter_le _ _
    omega
  rcases l2p_gap_or_bound S0 α hα hs0 hspos with hbound | ⟨b0, hb0, hb0_nonneg, ⟨c0, hc0, hbc⟩, hgap⟩
  · have hle := hbound (d v0) hdv0_mem
    have hapos : 0 ≤ α - 1 := by omega
    have hmul := mul_le_mul_of_nonneg_right hS0card hapos
    omega
  · have hc0_le : c0 ≤ d v0 := hsmax c0 hc0
    refine ⟨b0 - δ2 v0, by omega, by omega, ?_, ?_⟩
    · intro v
      have hzS : δ1 v ∈ S := hmem1 v
      by_cases h1 : δ1 v < -δ2 v0
      · left; omega
      · by_cases h2 : δ1 v0 < δ1 v
        · right; omega
        · have hz0 : δ1 v - (-δ2 v0) ∈ S0 :=
            Finset.mem_image.mpr ⟨δ1 v, Finset.mem_filter.mpr ⟨hzS, by omega, by omega⟩, rfl⟩
          rcases hgap (δ1 v - (-δ2 v0)) hz0 with hle | hge
          · left; omega
          · right; omega
    · intro v
      have hzS : -δ2 v ∈ S := hmem2 v
      by_cases h1 : -δ2 v < -δ2 v0
      · left; omega
      · by_cases h2 : δ1 v0 < -δ2 v
        · right; omega
        · have hz0 : -δ2 v - (-δ2 v0) ∈ S0 :=
            Finset.mem_image.mpr ⟨-δ2 v, Finset.mem_filter.mpr ⟨hzS, by omega, by omega⟩, rfl⟩
          rcases hgap (-δ2 v - (-δ2 v0)) hz0 with hle | hge
          · left; omega
          · right; omega

lemma l2p_key [Nonempty V] (g1 g2 : (V → ℤ) → WithTop ℝ)
    (h1S : SBF g1) (h1shift : ∀ (q : V → ℤ) (k : ℤ), g1 (fun v => q v + k) = g1 q)
    (h2S : SBF g2) (h2shift : ∀ (q : V → ℤ) (k : ℤ), g2 (fun v => q v + k) = g2 q)
    (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥) (palpha : V → ℤ) (m0 mstar : ℝ)
    (hm0 : InfConv g1 g2 palpha = (m0 : WithTop ℝ))
    (α : ℤ) (hα : 0 < α)
    (hcond : ∀ Y : Finset V, (m0 : WithTop ℝ) ≤ InfConv g1 g2 (fun v => palpha v + α * IndicatorVec Y v))
    (hB : ∀ d : V → ℤ, (∀ v, 0 ≤ d v) →
      (∀ v, d v ≤ 2 * ((Fintype.card V : ℤ) - 1) * (α - 1)) →
      (mstar : WithTop ℝ) ≤ InfConv g1 g2 (fun v => palpha v + d v)) :
    ∀ N : ℕ, ∀ d : V → ℤ, (∀ v, 0 ≤ d v) → (∃ u, d u = 0) → ∑ v, d v ≤ (N : ℤ) →
      ∀ q1 q2 : V → ℤ, (fun v => palpha v + d v) = q1 + q2 →
        (mstar : WithTop ℝ) ≤ g1 q1 + g2 q2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro d hd0 ⟨u, hdu⟩ hdN q1 q2 hq
  by_cases hsmall : ∀ v, d v ≤ 2 * ((Fintype.card V : ℤ) - 1) * (α - 1)
  · exact (hB d hd0 hsmall).trans (l2p_lb g1 g2 hE _ q1 q2 hq)
  push_neg at hsmall
  obtain ⟨v0, hv0⟩ := hsmall
  by_contra hcon
  push_neg at hcon
  have hq_fin : g1 q1 + g2 q2 ≠ ⊤ := ne_top_of_lt hcon
  have hq1_fin : g1 q1 ≠ ⊤ := (WithTop.add_ne_top.mp hq_fin).1
  have hq2_fin : g2 q2 ≠ ⊤ := (WithTop.add_ne_top.mp hq_fin).2
  obtain ⟨φ, hφ⟩ := WithTop.ne_top_iff_exists.mp hq_fin
  rw [← hφ] at hcon
  have hφm : φ < mstar := WithTop.coe_lt_coe.mp hcon
  obtain ⟨a0, b0, hab0, hablt⟩ := l2p_approx g1 g2 palpha m0 hm0 (mstar - φ) (by linarith)
  let c : ℤ := q1 u - a0 u
  let a : V → ℤ := fun v => a0 v + c
  let b : V → ℤ := fun v => b0 v + (-c)
  have hab : palpha = a + b := by
    funext v
    have := congrFun hab0 v
    simp only [Pi.add_apply] at this
    simp only [Pi.add_apply, a, b]; omega
  have ha_eq : g1 a = g1 a0 := h1shift a0 c
  have hb_eq : g2 b = g2 b0 := h2shift b0 (-c)
  rw [ ← ha_eq, ← hb_eq] at hablt
  have hab_fin : g1 a + g2 b ≠ ⊤ := ne_top_of_lt hablt
  have ha_fin : g1 a ≠ ⊤ := (WithTop.add_ne_top.mp hab_fin).1
  have hb_fin : g2 b ≠ ⊤ := (WithTop.add_ne_top.mp hab_fin).2
  obtain ⟨β, hβ⟩ := WithTop.ne_top_iff_exists.mp hab_fin
  rw [← hβ] at hablt
  have hβlt : β < m0 + (mstar - φ) := WithTop.coe_lt_coe.mp hablt
  let δ1 : V → ℤ := fun v => q1 v - a v
  let δ2 : V → ℤ := fun v => q2 v - b v
  have hqv : ∀ v, palpha v + d v = q1 v + q2 v := fun v => congrFun hq v
  have hpv : ∀ v, palpha v = a v + b v := fun v => congrFun hab v
  have hd_eq : ∀ v, δ1 v + δ2 v = d v := by
    intro v; dsimp [δ1, δ2]; have := hqv v; have := hpv v; omega
  have hdu1 : δ1 u = 0 := by dsimp [δ1, a, c]; omega
  have hdu2 : δ2 u = 0 := by have := hd_eq u; omega
  obtain ⟨k, hk1, hk2, hgap1, hgap2⟩ :=
    l2p_exists_joint_gap δ1 δ2 d α hα hd_eq hd0 u hdu1 hdu2 v0 hv0
  let Y1 : Finset V := Finset.univ.filter (fun v => k + α ≤ δ1 v)
  let Y2 : Finset V := Finset.univ.filter (fun v => k + α ≤ -δ2 v)
  let Y : Finset V := Finset.univ.filter (fun v => v ∈ Y1 ∧ v ∉ Y2)
  have hY1_high : ∀ v ∈ Y1, k + α ≤ q1 v - a v := fun v hv => (Finset.mem_filter.mp hv).2
  have hY1_low : ∀ v ∉ Y1, q1 v - a v ≤ k := by
    intro v hv
    rcases hgap1 v with hle | hge
    · exact hle
    · exfalso; exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hge⟩)
  have hY2_high : ∀ v ∈ Y2, k + α ≤ -(q2 v - b v) := fun v hv => (Finset.mem_filter.mp hv).2
  have hY2_low : ∀ v ∉ Y2, -(q2 v - b v) ≤ k := by
    intro v hv
    rcases hgap2 v with hle | hge
    · exact hle
    · exfalso; exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hge⟩)
  have S1 := l2p_cut_shift g1 h1S h1shift a q1 ha_fin hq1_fin α hα.le k Y1 hY1_high hY1_low
  have S2 := l2p_cut_neg_shift g2 h2S h2shift b q2 hb_fin hq2_fin α hα.le k Y2 hY2_high hY2_low
  have hY2_sub_Y1 : ∀ v, v ∈ Y2 → v ∈ Y1 := by
    intro v hv
    have h2 : k + α ≤ -δ2 v := (Finset.mem_filter.mp hv).2
    have hsum := hd_eq v
    have h0 := hd0 v
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hInd : ∀ v, IndicatorVec Y1 v - IndicatorVec Y2 v = IndicatorVec Y v := by
    intro v
    by_cases h2 : v ∈ Y2
    · have h1 : v ∈ Y1 := hY2_sub_Y1 v h2
      simp [Y, IndicatorVec, h1, h2]
    · by_cases h1 : v ∈ Y1 <;> simp [Y, IndicatorVec, h1, h2]
  let d' : V → ℤ := fun v => d v - α * IndicatorVec Y v
  have hd'0 : ∀ v, 0 ≤ d' v := by
    intro v
    by_cases hv : v ∈ Y
    · have hv1 : k + α ≤ δ1 v := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).2.1).2
      have hv2 : -δ2 v ≤ k := hY2_low v (Finset.mem_filter.mp hv).2.2
      have hsum := hd_eq v
      simp [d', IndicatorVec, hv]; omega
    · simp [d', IndicatorVec, hv]; exact hd0 v
  have hdu' : d' u = 0 := by
    have huY : u ∉ Y := by
      intro huY
      have hu1 : k + α ≤ δ1 u := (Finset.mem_filter.mp (Finset.mem_filter.mp huY).2.1).2
      have hu2 : -δ2 u ≤ k := hY2_low u (Finset.mem_filter.mp huY).2.2
      omega
    simp [d', IndicatorVec, huY, hdu]
  have hv0Y : v0 ∈ Y := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ v0, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ v0, hk2⟩
    · intro hv02
      have := (Finset.mem_filter.mp hv02).2
      omega
  have hN1 : 1 ≤ N := by
    have : d v0 ≤ ∑ v, d v := Finset.single_le_sum (fun v _ => hd0 v) (Finset.mem_univ v0)
    have : 0 ≤ 2 * ((Fintype.card V : ℤ) - 1) * (α - 1) := by
      have : 1 ≤ Fintype.card V := Fintype.card_pos
      nlinarith
    omega
  have hsum_d' : ∑ v, d' v ≤ ((N - 1 : ℕ) : ℤ) := by
    have h1 : ∑ v, (d v - d' v) ≥ d v0 - d' v0 :=
      Finset.single_le_sum (f := fun v => d v - d' v)
        (fun v _ => by dsimp [d']; by_cases hv : v ∈ Y <;> simp [IndicatorVec, hv] <;> omega)
        (Finset.mem_univ v0)
    have hv0_diff : d v0 - d' v0 = α := by simp [d', IndicatorVec, hv0Y]
    rw [ Finset.sum_sub_distrib] at h1
    push_cast [hN1]; omega
  have IH1 := IH (N - 1) (by omega) d' hd'0 ⟨u, hdu'⟩ hsum_d'
    (fun v => q1 v - α * IndicatorVec Y1 v) (fun v => q2 v + α * IndicatorVec Y2 v)
    (by
      funext v
      simp only [Pi.add_apply, d']
      rw [← hInd v]
      have := hqv v
      linarith)
  have hcondY : (m0 : WithTop ℝ) ≤
      g1 (fun v => a v + α * IndicatorVec Y1 v) + g2 (fun v => b v - α * IndicatorVec Y2 v) := by
    refine (hcond Y).trans (l2p_lb g1 g2 hE _ _ _ ?_)
    funext v
    simp only [Pi.add_apply]
    rw [← hInd v]
    have := hpv v
    linarith
  have chain : (mstar : WithTop ℝ) + (m0 : WithTop ℝ) ≤ (φ : WithTop ℝ) + (β : WithTop ℝ) := by
    calc (mstar : WithTop ℝ) + (m0 : WithTop ℝ)
        ≤ (g1 (fun v => q1 v - α * IndicatorVec Y1 v) + g2 (fun v => q2 v + α * IndicatorVec Y2 v)) +
          (g1 (fun v => a v + α * IndicatorVec Y1 v) + g2 (fun v => b v - α * IndicatorVec Y2 v)) :=
            add_le_add IH1 hcondY
      _ = (g1 (fun v => q1 v - α * IndicatorVec Y1 v) + g1 (fun v => a v + α * IndicatorVec Y1 v)) +
          (g2 (fun v => q2 v + α * IndicatorVec Y2 v) + g2 (fun v => b v - α * IndicatorVec Y2 v)) := by
            rw [add_add_add_comm]
      _ ≤ (g1 q1 + g1 a) + (g2 q2 + g2 b) := add_le_add S1 S2
      _ = (g1 q1 + g2 q2) + (g1 a + g2 b) := by rw [add_add_add_comm]
      _ = (φ : WithTop ℝ) + (β : WithTop ℝ) := by rw [hφ, hβ]
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at chain
  linarith

end DiscreteConvex.ConjugacyDualityC

open DiscreteConvex.ConjugacyDualityC Classical
open scoped Pointwise

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) (hg : L2Convex g)
    (hper : ∀ p : V → ℤ, g (p + 1) = g p) (alpha : ℤ) (halpha : 0 < alpha) (palpha : V → ℤ)
    (hpalpha : palpha ∈ DomZ g)
    (hcond : ∀ Y : Finset V, g palpha ≤ g (fun v => palpha v + alpha * IndicatorVec Y v)) :
    (ArgMin g).Nonempty ∧
      ∃ pstar ∈ ArgMin g, ∀ v : V, palpha v ≤ pstar v ∧
        pstar v ≤ palpha v + 2 * ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by
  cases isEmpty_or_nonempty V with
  | inl hE_V =>
    letI := hE_V
    have hmin : palpha ∈ ArgMin g := by
      intro q
      have : q = palpha := Subsingleton.elim _ _
      rw [this]
    exact ⟨⟨palpha, hmin⟩, palpha, hmin, fun v => isEmptyElim v⟩
  | inr hNE_V =>
    letI := hNE_V
    obtain ⟨g1, g2, ⟨h1S, r1, h1T⟩, ⟨h2S, r2, h2T⟩, hE, rfl⟩ := hg
    have hp' : InfConv g1 g2 palpha ≠ ⊤ := hpalpha
    obtain ⟨m0, hm0⟩ := WithTop.ne_top_iff_exists.mp hp'
    have hm0' : InfConv g1 g2 palpha = (m0 : WithTop ℝ) := hm0.symm
    have U1 : InfConv g1 g2 (palpha + 1) ≤ ((m0 + r1 : ℝ) : WithTop ℝ) := by
      have hfor : ∀ ε : ℝ, 0 < ε → InfConv g1 g2 (palpha + 1) ≤ ((m0 + r1 + ε : ℝ) : WithTop ℝ) := by
        intro ε hε
        obtain ⟨a, b, hab, hlt⟩ := l2p_approx g1 g2 palpha m0 hm0' ε hε
        obtain ⟨α, hα⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
        rw [← hα] at hlt
        have hα' : α < m0 + ε := WithTop.coe_lt_coe.mp hlt
        have h1 := l2p_lb g1 g2 hE (palpha + 1) (a + 1) b (by rw [hab]; abel)
        rw [h1T, add_right_comm, ← hα, ← WithTop.coe_add] at h1
        exact h1.trans (WithTop.coe_le_coe.mpr (by linarith))
      rw [hper palpha, hm0'] at hfor ⊢
      refine WithTop.coe_le_coe.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
      have := WithTop.coe_le_coe.mp (hfor ε hε); linarith
    have L1 : InfConv g1 g2 palpha + (r1 : WithTop ℝ) ≤ InfConv g1 g2 (palpha + 1) := by
      refine l2p_glb g1 g2 (palpha + 1) _ (fun a b hab => ?_)
      have h1 := l2p_lb g1 g2 hE palpha (a - 1) b (by
        have : palpha = (palpha + 1) - 1 := by abel
        rw [this, hab]; abel)
      have h2 : g1 a = g1 (a - 1) + (r1 : WithTop ℝ) := by rw [← h1T, sub_add_cancel]
      rw [h2, add_right_comm]
      exact add_le_add h1 le_rfl
    have hr1 : r1 = 0 := by
      rw [hper palpha, hm0', ← WithTop.coe_add, WithTop.coe_le_coe] at L1
      rw [hper palpha, hm0', WithTop.coe_le_coe] at U1
      linarith
    have U2 : InfConv g1 g2 (palpha + 1) ≤ ((m0 + r2 : ℝ) : WithTop ℝ) := by
      have hfor : ∀ ε : ℝ, 0 < ε → InfConv g1 g2 (palpha + 1) ≤ ((m0 + r2 + ε : ℝ) : WithTop ℝ) := by
        intro ε hε
        obtain ⟨a, b, hab, hlt⟩ := l2p_approx g1 g2 palpha m0 hm0' ε hε
        obtain ⟨α, hα⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
        rw [← hα] at hlt
        have hα' : α < m0 + ε := WithTop.coe_lt_coe.mp hlt
        have h1 := l2p_lb g1 g2 hE (palpha + 1) a (b + 1) (by rw [hab]; abel)
        rw [h2T, ← add_assoc, ← hα, ← WithTop.coe_add] at h1
        exact h1.trans (WithTop.coe_le_coe.mpr (by linarith))
      rw [hper palpha, hm0'] at hfor ⊢
      refine WithTop.coe_le_coe.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
      have := WithTop.coe_le_coe.mp (hfor ε hε); linarith
    have L2 : InfConv g1 g2 palpha + (r2 : WithTop ℝ) ≤ InfConv g1 g2 (palpha + 1) := by
      refine l2p_glb g1 g2 (palpha + 1) _ (fun a b hab => ?_)
      have h1 := l2p_lb g1 g2 hE palpha a (b - 1) (by
        have : palpha = (palpha + 1) - 1 := by abel
        rw [this, hab]; abel)
      have h2 : g2 b = g2 (b - 1) + (r2 : WithTop ℝ) := by rw [← h2T, sub_add_cancel]
      rw [h2, ← add_assoc]
      exact add_le_add h1 le_rfl
    have hr2 : r2 = 0 := by
      rw [hper palpha, hm0', ← WithTop.coe_add, WithTop.coe_le_coe] at L2
      rw [hper palpha, hm0', WithTop.coe_le_coe] at U2
      linarith
    have h1shift : ∀ (q : V → ℤ) (k : ℤ), g1 (fun v => q v + k) = g1 q := by
      intro q k
      have := l2p_trf_iter g1 r1 h1T q k
      rw [hr1, mul_zero, WithTop.coe_zero, add_zero] at this
      exact this
    have h2shift : ∀ (q : V → ℤ) (k : ℤ), g2 (fun v => q v + k) = g2 q := by
      intro q k
      have := l2p_trf_iter g2 r2 h2T q k
      rw [hr2, mul_zero, WithTop.coe_zero, add_zero] at this
      exact this
    let R : ℤ := 2 * ((Fintype.card V : ℤ) - 1) * (alpha - 1)
    have hR : 0 ≤ R := by
      have : 1 ≤ Fintype.card V := Fintype.card_pos
      dsimp [R]; nlinarith
    let B : Finset (V → ℤ) := Fintype.piFinset (fun v => Finset.Icc (palpha v) (palpha v + R))
    have hpalphaB : palpha ∈ B := by
      refine Fintype.mem_piFinset.mpr (fun v => Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    obtain ⟨pstar, hpstarB, hminB⟩ := Finset.exists_min_image B (InfConv g1 g2) ⟨palpha, hpalphaB⟩
    have hpstar_le : InfConv g1 g2 pstar ≤ (m0 : WithTop ℝ) := by
      rw [← hm0']; exact hminB palpha hpalphaB
    have hpstar_fin : InfConv g1 g2 pstar ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hpstar_le
    obtain ⟨mstar, hmstar⟩ := WithTop.ne_top_iff_exists.mp hpstar_fin
    have hmstar' : InfConv g1 g2 pstar = (mstar : WithTop ℝ) := hmstar.symm
    have hB : ∀ d : V → ℤ, (∀ v, 0 ≤ d v) → (∀ v, d v ≤ R) →
        (mstar : WithTop ℝ) ≤ InfConv g1 g2 (fun v => palpha v + d v) := by
      intro d hd0 hdR
      rw [← hmstar']
      refine hminB (fun v => palpha v + d v) (Fintype.mem_piFinset.mpr (fun v => Finset.mem_Icc.mpr ?_))
      have := hd0 v; have := hdR v; omega
    have hcond' : ∀ Y : Finset V, (m0 : WithTop ℝ) ≤
        InfConv g1 g2 (fun v => palpha v + alpha * IndicatorVec Y v) := by
      intro Y; rw [← hm0']; exact hcond Y
    have key := l2p_key g1 g2 h1S h1shift h2S h2shift hE palpha m0 mstar hm0' alpha halpha hcond' hB
    have hpstar_min : pstar ∈ ArgMin (InfConv g1 g2) := by
      intro q
      rw [hmstar']
      refine l2p_glb g1 g2 q _ (fun q1 q2 hq => ?_)
      obtain ⟨u, _, hu⟩ := Finset.exists_min_image Finset.univ (fun v => q v - palpha v) Finset.univ_nonempty
      let c : ℤ := q u - palpha u
      let d : V → ℤ := fun v => q v - palpha v - c
      have hd0 : ∀ v, 0 ≤ d v := by
        intro v
        have := hu v (Finset.mem_univ v)
        dsimp [d, c] at this ⊢; omega
      have hdu : d u = 0 := by dsimp [d, c]; omega
      have hshift1 : g1 q1 = g1 (fun v => q1 v + (-c)) := (h1shift q1 (-c)).symm
      rw [hshift1]
      refine key (∑ v, d v).toNat d hd0 ⟨u, hdu⟩
        (by rw [Int.toNat_of_nonneg (Finset.sum_nonneg (fun v _ => hd0 v))])
        (fun v => q1 v + (-c)) q2 ?_
      funext v
      have := congrFun hq v
      simp only [Pi.add_apply, d, c] at this ⊢; omega
    refine ⟨⟨pstar, hpstar_min⟩, pstar, hpstar_min, ?_⟩
    intro v
    exact Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hpstarB v)
