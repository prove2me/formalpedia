-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsC.network_transformation_rr
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:57:32.079207+00:00
-- url     : https://prove2.me/submissions/02765fdf-9baf-464a-9111-b9e1509ea44c

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MNaturalConvexR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SBFR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_TRFR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LNaturalConvexR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugateR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugateArcR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsConvexUnivariateR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeROnT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeROnT

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.NetworkFlowsC

namespace RRCex

/-- `f(x) = 0` for `x ≥ 0`, `+∞` otherwise (real variable). -/
noncomputable def f0 (x : Unit → ℝ) : WithTop ℝ := if 0 ≤ x () then ((0 : ℝ) : WithTop ℝ) else ⊤

/-- `g(p) = 0` for `p ≤ 0`, `+∞` otherwise: the conjugate of `f0`. -/
noncomputable def g0 (p : Unit → ℝ) : WithTop ℝ := if p () ≤ 0 then ((0 : ℝ) : WithTop ℝ) else ⊤

def tl : Empty → Unit := fun a => a.elim
def fa0 : Empty → ℝ → WithTop ℝ := fun a => a.elim
def U : Finset Unit := Finset.univ

theorem toEReal_zero : ToEReal ((0 : ℝ) : WithTop ℝ) = 0 := rfl
theorem toEReal_zero' : ToEReal (0 : WithTop ℝ) = 0 := rfl
theorem toEReal_top : ToEReal ⊤ = ⊤ := rfl

theorem conj : ConvexConjugateR f0 = g0 := by
  funext p
  unfold ConvexConjugateR g0
  by_cases hp : p () ≤ 0
  · rw [if_pos hp]
    have : sSup {v : EReal | ∃ x : Unit → ℝ,
        v = ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f0 x)} = 0 := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro v ⟨x, rfl⟩
        by_cases hx : 0 ≤ x ()
        · rw [show f0 x = ((0 : ℝ) : WithTop ℝ) by simp [f0, hx], toEReal_zero, sub_zero]
          have : (∑ i, p i * x i) ≤ 0 := by
            simp only [Finset.univ_unique, Finset.sum_singleton]
            exact mul_nonpos_of_nonpos_of_nonneg hp hx
          exact_mod_cast this
        · rw [show f0 x = ⊤ by simp [f0, hx], toEReal_top]
          simp
      · refine le_sSup ⟨fun _ => 0, ?_⟩
        rw [show f0 (fun _ => 0) = ((0 : ℝ) : WithTop ℝ) by simp [f0], toEReal_zero]
        simp
    rw [this]; rfl
  · rw [if_neg hp]
    push Not at hp
    have : sSup {v : EReal | ∃ x : Unit → ℝ,
        v = ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f0 x)} = ⊤ := by
      refine sSup_eq_top.mpr (fun b hb => ?_)
      induction b using EReal.rec with
      | bot =>
        refine ⟨0, ⟨fun _ => 0, ?_⟩, EReal.bot_lt_zero⟩
        rw [show f0 (fun _ => 0) = ((0 : ℝ) : WithTop ℝ) by simp [f0], toEReal_zero]
        simp
      | top => exact absurd hb (lt_irrefl _)
      | coe r =>
        refine ⟨((p () * ((|r| + 1) / p ()) : ℝ) : EReal), ⟨fun _ => (|r| + 1) / p (), ?_⟩, ?_⟩
        · rw [show f0 (fun _ => (|r| + 1) / p ()) = ((0 : ℝ) : WithTop ℝ) by
            simp only [f0]; rw [if_pos (by positivity)], toEReal_zero]
          simp
        · have : r < p () * ((|r| + 1) / p ()) := by
            rw [mul_div_cancel₀ _ hp.ne']; linarith [le_abs_self r]
          exact_mod_cast this
    rw [this]; rfl

theorem dom_lift {z : Option Unit → ℝ} (hz : z ∈ DomR (LiftedFunctionR f0)) :
    z none = -z (some ()) ∧ 0 ≤ z (some ()) := by
  by_contra h
  apply hz
  unfold LiftedFunctionR f0
  simp only [Finset.univ_unique, Finset.sum_singleton]
  by_cases h1 : z none = -z (some ())
  · rw [if_pos (by simpa using h1)]
    have h2 : ¬ 0 ≤ z (some ()) := fun h2 => h ⟨h1, h2⟩
    simp [h2]
  · rw [if_neg (by simpa using h1)]

theorem lift_val (z : Option Unit → ℝ) (h1 : z none = -z (some ())) (h2 : 0 ≤ z (some ())) :
    LiftedFunctionR f0 z = ((0 : ℝ) : WithTop ℝ) := by
  unfold LiftedFunctionR f0
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [if_pos (by simpa using h1)]
  simp [h2]

theorem f0_mnat : MNaturalConvexR f0 := by
  intro x hx y hy u hu
  obtain ⟨hx1, hx2⟩ := dom_lift hx
  obtain ⟨hy1, hy2⟩ := dom_lift hy
  simp only [SuppPosR, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  cases u with
  | none =>
    refine ⟨some (), by simp [SuppNegR]; linarith, y (some ()) - x (some ()), by linarith,
      fun α h0 h1 => ?_⟩
    rw [lift_val x hx1 hx2, lift_val y hy1 hy2,
      lift_val _ (by simp; linarith) (by simp; linarith),
      lift_val _ (by simp; linarith) (by simp; linarith)]
  | some u =>
    have : u = () := Subsingleton.elim _ _
    subst this
    refine ⟨none, by simp [SuppNegR]; linarith, x (some ()) - y (some ()), by linarith,
      fun α h0 h1 => ?_⟩
    rw [lift_val x hx1 hx2, lift_val y hy1 hy2,
      lift_val _ (by simp; linarith) (by simp; linarith),
      lift_val _ (by simp; linarith) (by simp; linarith)]

theorem g0_lnat : LNaturalConvexR g0 := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro p q
    unfold LiftedFunctionRL g0
    by_cases hp : p (some ()) - p none ≤ 0
    · by_cases hq : q (some ()) - q none ≤ 0
      · have h1 : max (p (some ())) (q (some ())) - max (p none) (q none) ≤ 0 := by
          rw [sub_nonpos]; exact max_le_max (by linarith) (by linarith)
        have h2 : min (p (some ())) (q (some ())) - min (p none) (q none) ≤ 0 := by
          rw [sub_nonpos]; exact min_le_min (by linarith) (by linarith)
        simp only [hp, hq, h1, h2, if_true]
        exact le_rfl
      · simp only [hq, if_false]; simp
    · simp only [hp, if_false]; simp
  · intro p
    unfold LiftedFunctionRL g0
    simp only [WithTop.coe_zero, add_zero]
    have : p (some ()) + 1 - (p none + 1) = p (some ()) - p none := by ring
    rw [this]

theorem bdy (xi : Empty → ℝ) (v : Unit) : Boundary tl tl xi v = 0 := by
  simp [Boundary]

theorem FT (y : Unit → ℝ) :
    InducedFTildeR tl tl U U fa0 f0 y = if y () = 0 then 0 else ⊤ := by
  unfold InducedFTildeR
  by_cases hy : y () = 0
  · rw [if_pos hy]
    apply le_antisymm
    · refine sInf_le ⟨fun a => a.elim, fun _ => 0, fun _ _ => rfl, fun v _ => by rw [bdy],
        fun v _ => by cases v; rw [bdy, hy]; simp, fun v hv => absurd (Finset.mem_univ v) hv, ?_⟩
      simp [f0, toEReal_zero']
    · refine le_sInf ?_
      rintro L ⟨xi, x, -, hS, -, -, rfl⟩
      have hx : x () = 0 := by rw [← hS () (Finset.mem_univ _), bdy]
      rw [show f0 x + ∑ a : Empty, fa0 a (xi a) = ((0 : ℝ) : WithTop ℝ) by simp [f0, hx]]
      rfl
  · rw [if_neg hy]
    refine sInf_eq_top.mpr ?_
    rintro L ⟨xi, x, -, -, hT, -, -⟩
    exfalso; apply hy
    have := hT () (Finset.mem_univ _)
    rw [bdy] at this; linarith

theorem GT (q : Unit → ℝ) : InducedGTildeR tl tl U U fa0 g0 q = ToEReal (g0 q) := by
  unfold InducedGTildeR
  apply le_antisymm
  · refine sInf_le ⟨fun a => a.elim, q, q, fun v hv => absurd (Finset.mem_univ v) hv,
      fun _ _ => rfl, fun _ _ => rfl, fun a => a.elim, ?_⟩
    simp
  · refine le_sInf ?_
    rintro L ⟨eta, P, p, -, hS, hT, -, rfl⟩
    have : p = q := by
      funext v; rw [← hS v (Finset.mem_univ _), hT v (Finset.mem_univ _)]
    subst this
    simp

theorem FTOnT (y : {v // v ∈ U} → ℝ) :
    InducedFTildeROnT tl tl U U fa0 f0 y =
      if y ⟨(), Finset.mem_univ _⟩ = 0 then ((0 : ℝ) : WithTop ℝ) else ⊤ := by
  unfold InducedFTildeROnT InducedFTildeRWT
  rw [FT]
  have : ExtendFromTR U y () = y ⟨(), Finset.mem_univ _⟩ := by
    simp [ExtendFromTR, U]
  rw [this]
  split_ifs <;> rfl

theorem final : InducedGTildeROnT tl tl U U fa0 g0 ≠
    ConvexConjugateR (InducedFTildeROnT tl tl U U fa0 f0) := by
  intro h
  have h1 := congrFun h (fun _ => 1)
  have lhs : InducedGTildeROnT tl tl U U fa0 g0 (fun _ => 1) = ⊤ := by
    unfold InducedGTildeROnT InducedGTildeRWT
    rw [GT]
    have : g0 (ExtendFromTR U (fun _ => 1)) = ⊤ := by
      simp [g0, ExtendFromTR, U]
    rw [this]; rfl
  have rhs : ConvexConjugateR (InducedFTildeROnT tl tl U U fa0 f0) (fun _ => 1) =
      ((0 : ℝ) : WithTop ℝ) := by
    unfold ConvexConjugateR
    have : sSup {v : EReal | ∃ x : {v // v ∈ U} → ℝ,
        v = ((∑ i, (1 : ℝ) * x i : ℝ) : EReal) -
          ToEReal (InducedFTildeROnT tl tl U U fa0 f0 x)} = 0 := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro v ⟨x, rfl⟩
        rw [FTOnT]
        by_cases hx : x ⟨(), Finset.mem_univ _⟩ = 0
        · rw [if_pos hx, toEReal_zero, sub_zero]
          have : ∀ i, x i = 0 := by
            intro i; obtain ⟨⟨⟩, hi⟩ := i; exact hx
          simp [this]
        · rw [if_neg hx, toEReal_top]; simp
      · refine le_sSup ⟨fun _ => 0, ?_⟩
        rw [FTOnT, if_pos rfl, toEReal_zero]
        simp
    rw [this]; rfl
  rw [lhs, rhs] at h1
  exact WithTop.top_ne_coe h1

end RRCex

open RRCex in
theorem solution : ¬ (∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (tail head : A → V) (S T : Finset V) (fa ga : A → ℝ → WithTop ℝ)
    (f g : (V → ℝ) → WithTop ℝ) (hfa : ∀ a, IsConvexUnivariateR (fa a))
    (hga : ∀ a, IsConvexUnivariateR (ga a))
    (hfbdd : ∀ y, InducedFTildeR tail head S T fa f y ≠ ⊥)
    (hfprop : ∃ y, InducedFTildeR tail head S T fa f y ≠ ⊤)
    (hgbdd : ∀ q, InducedGTildeR tail head S T ga g q ≠ ⊥)
    (hgprop : ∃ q, InducedGTildeR tail head S T ga g q ≠ ⊤),
    (MExchangeAxiomR f → MExchangeAxiomR (InducedFTildeROnT tail head S T fa f)) ∧
    (MNaturalConvexR f → MNaturalConvexR (InducedFTildeROnT tail head S T fa f)) ∧
    ((SBFR g ∧ TRFR g) →
      SBFR (InducedGTildeROnT tail head S T ga g) ∧ TRFR (InducedGTildeROnT tail head S T ga g)) ∧
    (LNaturalConvexR g → LNaturalConvexR (InducedGTildeROnT tail head S T ga g)) ∧
    (MNaturalConvexR f → LNaturalConvexR g →
      g = ConvexConjugateR f → (∀ a, ga a = ConvexConjugateArcR (fa a)) →
      InducedGTildeROnT tail head S T ga g = ConvexConjugateR (InducedFTildeROnT tail head S T fa f))) := by
  intro h
  have H := h tl tl U U fa0 fa0 f0 g0 (fun a => a.elim) (fun a => a.elim)
    (fun y => by rw [FT]; split_ifs <;> simp)
    ⟨fun _ => 0, by rw [FT]; simp⟩
    (fun q => by rw [GT]; exact WithBot.coe_ne_bot)
    ⟨fun _ => 0, by rw [GT]; simp [g0, toEReal_zero']⟩
  exact final (H.2.2.2.2 f0_mnat g0_lnat conj.symm (fun a => a.elim))

#print axioms solution
