-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsC.network_transformation_zz
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:30:49.253726+00:00
-- url     : https://prove2.me/submissions/b390c1ac-3efe-40d4-8b71-82a01a5911d7

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SBF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_TRF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugate
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsIntegerValuedArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugateArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTilde
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTilde
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeOnT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeOnT

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.NetworkFlowsC

namespace NTCex

/-- `f(x) = 0` for `x ≥ 0`, `+∞` otherwise. -/
noncomputable def f0 (x : Unit → ℤ) : WithTop ℝ := if 0 ≤ x () then ((0 : ℝ) : WithTop ℝ) else ⊤

/-- `g(p) = 0` for `p ≤ 0`, `+∞` otherwise: the conjugate of `f0`. -/
noncomputable def g0 (p : Unit → ℤ) : WithTop ℝ := if p () ≤ 0 then ((0 : ℝ) : WithTop ℝ) else ⊤

def tl : Empty → Unit := fun a => a.elim
def fa0 : Empty → ℤ → WithTop ℝ := fun a => a.elim
def U : Finset Unit := Finset.univ

theorem fromEReal_zero : FromEReal 0 = ((0 : ℝ) : WithTop ℝ) := rfl
theorem fromEReal_top : FromEReal ⊤ = ⊤ := rfl
theorem toEReal_zero : ToEReal ((0 : ℝ) : WithTop ℝ) = 0 := rfl
theorem toEReal_top : ToEReal ⊤ = ⊤ := rfl
theorem toEReal_zero' : ToEReal (0 : WithTop ℝ) = 0 := rfl

theorem conj : ConvexConjugate f0 = g0 := by
  funext p
  unfold ConvexConjugate g0
  by_cases hp : p () ≤ 0
  · rw [if_pos hp]
    have : sSup {v : EReal | ∃ x : Unit → ℤ,
        v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (f0 x)} = 0 := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro v ⟨x, rfl⟩
        by_cases hx : 0 ≤ x ()
        · rw [show f0 x = ((0 : ℝ) : WithTop ℝ) by simp [f0, hx], toEReal_zero, sub_zero]
          have : (∑ i, (p i : ℝ) * (x i : ℝ)) ≤ 0 := by
            simp only [Finset.univ_unique, Finset.sum_singleton]
            exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hp) (by exact_mod_cast hx)
          exact_mod_cast this
        · rw [show f0 x = ⊤ by simp [f0, hx], toEReal_top]
          simp
      · refine le_sSup ⟨fun _ => 0, ?_⟩
        rw [show f0 (fun _ => 0) = ((0 : ℝ) : WithTop ℝ) by simp [f0], toEReal_zero]
        simp
    rw [this]; rfl
  · rw [if_neg hp]
    push Not at hp
    have : sSup {v : EReal | ∃ x : Unit → ℤ,
        v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (f0 x)} = ⊤ := by
      refine sSup_eq_top.mpr (fun b hb => ?_)
      induction b using EReal.rec with
      | bot =>
        refine ⟨0, ⟨fun _ => 0, ?_⟩, EReal.bot_lt_zero⟩
        rw [show f0 (fun _ => 0) = ((0 : ℝ) : WithTop ℝ) by simp [f0], toEReal_zero]
        simp
      | top => exact absurd hb (lt_irrefl _)
      | coe r =>
        obtain ⟨n, hn⟩ := exists_nat_gt r
        refine ⟨((p () * n : ℤ) : ℝ), ⟨fun _ => (n : ℤ), ?_⟩, ?_⟩
        · rw [show f0 (fun _ => (n : ℤ)) = ((0 : ℝ) : WithTop ℝ) by simp [f0], toEReal_zero]
          simp
        · have h1 : (1 : ℝ) ≤ p () := by exact_mod_cast hp
          have h2 : (0 : ℝ) ≤ n := by positivity
          have : r < ((p () * n : ℤ) : ℝ) := by push_cast; nlinarith
          exact_mod_cast this
    rw [this]; rfl

theorem dom_lift {z : Option Unit → ℤ} (hz : z ∈ DomZ (LiftedFunction f0)) :
    z none = -z (some ()) ∧ 0 ≤ z (some ()) := by
  by_contra h
  apply hz
  unfold LiftedFunction f0
  simp only [Finset.univ_unique, Finset.sum_singleton]
  by_cases h1 : z none = -z (some ())
  · rw [if_pos (by simpa using h1)]
    have h2 : ¬ 0 ≤ z (some ()) := fun h2 => h ⟨h1, h2⟩
    simp [h2]
  · rw [if_neg (by simpa using h1)]

theorem lift_val (z : Option Unit → ℤ) (h1 : z none = -z (some ())) (h2 : 0 ≤ z (some ())) :
    LiftedFunction f0 z = ((0 : ℝ) : WithTop ℝ) := by
  unfold LiftedFunction f0
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [if_pos (by simpa using h1)]
  simp [h2]

theorem f0_mnat : MNaturalConvex f0 := by
  intro x hx y hy u hu
  obtain ⟨hx1, hx2⟩ := dom_lift hx
  obtain ⟨hy1, hy2⟩ := dom_lift hy
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  cases u with
  | none =>
    refine ⟨some (), by simp [SuppNeg]; omega, ?_⟩
    rw [lift_val x hx1 hx2, lift_val y hy1 hy2, lift_val _ (by simp; omega) (by simp; omega),
      lift_val _ (by simp; omega) (by simp; omega)]
  | some u =>
    have : u = () := Subsingleton.elim _ _
    subst this
    refine ⟨none, by simp [SuppNeg]; omega, ?_⟩
    rw [lift_val x hx1 hx2, lift_val y hy1 hy2, lift_val _ (by simp; omega) (by simp; omega),
      lift_val _ (by simp; omega) (by simp; omega)]

theorem g0_lnat : LNaturalConvex g0 := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro p q
    unfold LiftedFunctionL g0
    by_cases hp : p (some ()) - p none ≤ 0
    · by_cases hq : q (some ()) - q none ≤ 0
      · have h1 : (p ⊔ q) (some ()) - (p ⊔ q) none ≤ 0 := by
          simp only [Pi.sup_apply]; omega
        have h2 : (p ⊓ q) (some ()) - (p ⊓ q) none ≤ 0 := by
          simp only [Pi.inf_apply]; omega
        simp only [hp, hq, h1, h2, if_true]
        exact le_rfl
      · simp only [hq, if_false]; simp
    · simp only [hp, if_false]; simp
  · intro p
    unfold LiftedFunctionL g0
    simp only [Pi.add_apply, Pi.one_apply, WithTop.coe_zero, add_zero]
    have : p (some ()) + 1 - (p none + 1) = p (some ()) - p none := by ring
    rw [this]

theorem bdy (xi : Empty → ℤ) (v : Unit) : BoundaryZ tl tl xi v = 0 := by
  simp [BoundaryZ]

theorem FT (y : Unit → ℤ) :
    InducedFTilde tl tl U U fa0 f0 y = if y () = 0 then 0 else ⊤ := by
  unfold InducedFTilde
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
    rw [bdy] at this; omega

theorem GT (q : Unit → ℤ) : InducedGTilde tl tl U U fa0 g0 q = ToEReal (g0 q) := by
  unfold InducedGTilde
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

theorem FTOnT (y : {v // v ∈ U} → ℤ) :
    InducedFTildeOnT tl tl U U fa0 f0 y =
      if y ⟨(), Finset.mem_univ _⟩ = 0 then ((0 : ℝ) : WithTop ℝ) else ⊤ := by
  unfold InducedFTildeOnT InducedFTildeWT
  rw [FT]
  have : ExtendFromT U y () = y ⟨(), Finset.mem_univ _⟩ := by
    simp [ExtendFromT, U]
  rw [this]
  split_ifs <;> rfl

theorem final : InducedGTildeOnT tl tl U U fa0 g0 ≠ ConvexConjugate (InducedFTildeOnT tl tl U U fa0 f0) := by
  intro h
  have h1 := congrFun h (fun _ => 1)
  have lhs : InducedGTildeOnT tl tl U U fa0 g0 (fun _ => 1) = ⊤ := by
    unfold InducedGTildeOnT InducedGTildeWT
    rw [GT]
    have : g0 (ExtendFromT U (fun _ => 1)) = ⊤ := by
      simp [g0, ExtendFromT, U]
    rw [this]; rfl
  have rhs : ConvexConjugate (InducedFTildeOnT tl tl U U fa0 f0) (fun _ => 1) =
      ((0 : ℝ) : WithTop ℝ) := by
    unfold ConvexConjugate
    have : sSup {v : EReal | ∃ x : {v // v ∈ U} → ℤ,
        v = ((∑ i, ((1 : ℤ) : ℝ) * (x i : ℝ) : ℝ) : EReal) -
          ToEReal (InducedFTildeOnT tl tl U U fa0 f0 x)} = 0 := by
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

end NTCex

open NTCex in
theorem solution : ¬ (∀ {V : Type} {A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    [DecidableEq A] (tail head : A → V) (S T : Finset V) (fa ga : A → ℤ → WithTop ℝ)
    (f g : (V → ℤ) → WithTop ℝ)
    (hfa : ∀ a, DiscreteConvexUnivariate (fa a) ∧ IsIntegerValuedArcZ (fa a))
    (hga : ∀ a, DiscreteConvexUnivariate (ga a) ∧ IsIntegerValuedArcZ (ga a))
    (hfbdd : ∀ y, InducedFTilde tail head S T fa f y ≠ ⊥)
    (hfprop : ∃ y, InducedFTilde tail head S T fa f y ≠ ⊤)
    (hgbdd : ∀ q, InducedGTilde tail head S T ga g q ≠ ⊥)
    (hgprop : ∃ q, InducedGTilde tail head S T ga g q ≠ ⊤),
    (MExchangeAxiom f → IsIntegerValuedFn f →
      MExchangeAxiom (InducedFTildeOnT tail head S T fa f) ∧
        IsIntegerValuedFn (InducedFTildeOnT tail head S T fa f)) ∧
    (MNaturalConvex f → IsIntegerValuedFn f →
      MNaturalConvex (InducedFTildeOnT tail head S T fa f) ∧
        IsIntegerValuedFn (InducedFTildeOnT tail head S T fa f)) ∧
    ((SBF g ∧ TRF g) → IsIntegerValuedFn g →
      (SBF (InducedGTildeOnT tail head S T ga g) ∧ TRF (InducedGTildeOnT tail head S T ga g)) ∧
        IsIntegerValuedFn (InducedGTildeOnT tail head S T ga g)) ∧
    (LNaturalConvex g → IsIntegerValuedFn g →
      LNaturalConvex (InducedGTildeOnT tail head S T ga g) ∧
        IsIntegerValuedFn (InducedGTildeOnT tail head S T ga g)) ∧
    (MNaturalConvex f → LNaturalConvex g → IsIntegerValuedFn f → IsIntegerValuedFn g →
      g = ConvexConjugate f → (∀ a, ga a = ConvexConjugateArcZ (fa a)) →
      InducedGTildeOnT tail head S T ga g = ConvexConjugate (InducedFTildeOnT tail head S T fa f))) := by
  intro h
  have hint_f : IsIntegerValuedFn f0 := by
    intro x; unfold f0; split_ifs
    · right; exact ⟨0, by simp⟩
    · left; rfl
  have hint_g : IsIntegerValuedFn g0 := by
    intro x; unfold g0; split_ifs
    · right; exact ⟨0, by simp⟩
    · left; rfl
  have H := h tl tl U U fa0 fa0 f0 g0 (fun a => a.elim) (fun a => a.elim)
    (fun y => by rw [FT]; split_ifs <;> simp)
    ⟨fun _ => 0, by rw [FT]; simp⟩
    (fun q => by rw [GT]; exact WithBot.coe_ne_bot)
    ⟨fun _ => 0, by rw [GT]; simp [g0, toEReal_zero']⟩
  exact final (H.2.2.2.2 f0_mnat g0_lnat hint_f hint_g conj.symm (fun a => a.elim))

#print axioms solution
