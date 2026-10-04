-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsC.network_transformation_zr
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:54:37.868977+00:00
-- url     : https://prove2.me/submissions/324a5ca8-d237-46aa-8356-c742be5ca61b

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SBF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_TRF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTilde
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTilde
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeOnT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeOnT

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.NetworkFlowsC

namespace ZRCex

def tl : Unit → Bool := fun _ => true
def hd : Unit → Bool := fun _ => false
def S : Finset Bool := {true}
def T : Finset Bool := {false}

/-- `ψ = 0` on `{0, 3}`, `+∞` elsewhere: midpoint convex with a hole. -/
noncomputable def psi (t : ℤ) : WithTop ℝ := if t = 0 ∨ t = 3 then ((0 : ℝ) : WithTop ℝ) else ⊤

noncomputable def fa : Unit → ℤ → WithTop ℝ := fun _ => psi
def ga : Unit → ℤ → WithTop ℝ := fun _ _ => 0

/-- `f = 0` on `{x : x(t) = 0}`: M♮-convex. -/
noncomputable def f (x : Bool → ℤ) : WithTop ℝ := if x false = 0 then ((0 : ℝ) : WithTop ℝ) else ⊤
def g : (Bool → ℤ) → WithTop ℝ := fun _ => 0

theorem psi_dcu : DiscreteConvexUnivariate psi := by
  refine ⟨⟨0, by simp [psi]⟩, fun x => ?_⟩
  by_cases h1 : x = 0 ∨ x = 3
  · by_cases h2 : x + 2 = 0 ∨ x + 2 = 3
    · exfalso; omega
    · have : psi (x + 2) = ⊤ := by simp only [psi]; rw [if_neg h2]
      rw [this]; simp
  · have : psi x = ⊤ := by simp only [psi]; rw [if_neg h1]
    rw [this]; simp

theorem bdy (xi : Unit → ℤ) : BoundaryZ tl hd xi = fun b => if b then xi () else -xi () := by
  funext b
  cases b <;> simp [BoundaryZ, tl, hd]

theorem FT (y : Bool → ℤ) : InducedFTilde tl hd S T fa f y = ToEReal (psi (y false)) := by
  unfold InducedFTilde
  apply le_antisymm
  · refine sInf_le ⟨fun _ => y false, fun b => if b then y false else 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv; cases v <;> simp [S] at hv ⊢
    · intro v hv; simp [S] at hv; subst hv; rw [bdy]; simp
    · intro v hv; simp [T] at hv; subst hv; rw [bdy]; simp
    · intro v h1 h2; cases v <;> simp [S, T] at h1 h2
    · simp [f, fa]
  · refine le_sInf ?_
    rintro L ⟨xi, x, hsupp, hS, hT, -, rfl⟩
    have h1 := hS true (by simp [S])
    have h2 := hT false (by simp [T])
    have h3 := hsupp false (by simp [S])
    rw [bdy] at h1 h2
    simp at h1 h2
    simp [f, h3, fa, h2]

theorem GT (q : Bool → ℤ) : InducedGTilde tl hd S T ga g q = 0 := by
  unfold InducedGTilde
  apply le_antisymm
  · refine sInf_le ⟨fun _ => q false, fun b => if b then 0 else q false, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro v _; rfl
    · intro v hv; simp [S] at hv; subst hv; simp
    · intro v hv; simp [T] at hv; subst hv; simp
    · intro a; simp [tl, hd]
    · simp [g, ga]; rfl
  · refine le_sInf ?_
    rintro L ⟨eta, P, p, -, -, -, -, rfl⟩
    simp [g, ga]; rfl

theorem dom_lift {z : Option Bool → ℤ} (hz : z ∈ DomZ (LiftedFunction f)) :
    z none = -(z (some true) + z (some false)) ∧ z (some false) = 0 := by
  by_contra h
  apply hz
  unfold LiftedFunction f
  simp only [Fintype.sum_bool]
  by_cases h1 : z none = -(z (some true) + z (some false))
  · rw [if_pos h1]
    have h2 : ¬ z (some false) = 0 := fun h2 => h ⟨h1, h2⟩
    simp [h2]
  · rw [if_neg h1]

theorem lift_val (z : Option Bool → ℤ) (h1 : z none = -(z (some true) + z (some false)))
    (h2 : z (some false) = 0) : LiftedFunction f z = ((0 : ℝ) : WithTop ℝ) := by
  unfold LiftedFunction f
  simp only [Fintype.sum_bool]
  rw [if_pos h1]
  simp [h2]

theorem f_mnat : MNaturalConvex f := by
  intro x hx y hy u hu
  obtain ⟨hx1, hx2⟩ := dom_lift hx
  obtain ⟨hy1, hy2⟩ := dom_lift hy
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases u with _ | _ | _
  · refine ⟨some true, by simp [SuppNeg]; omega, ?_⟩
    rw [lift_val x hx1 hx2, lift_val y hy1 hy2, lift_val _ (by simp; omega) (by simp; omega),
      lift_val _ (by simp; omega) (by simp; omega)]
  · omega
  · refine ⟨none, by simp [SuppNeg]; omega, ?_⟩
    rw [lift_val x hx1 hx2, lift_val y hy1 hy2, lift_val _ (by simp; omega) (by simp; omega),
      lift_val _ (by simp; omega) (by simp; omega)]

abbrev W := {v // v ∈ T}

def w0 : W := ⟨false, by simp [T]⟩

instance : Subsingleton W := ⟨fun a b => Subtype.ext (by
  have ha := a.2; have hb := b.2; simp [T] at ha hb; rw [ha, hb])⟩

theorem FTOnT (y : W → ℤ) : InducedFTildeOnT tl hd S T fa f y = psi (y w0) := by
  unfold InducedFTildeOnT InducedFTildeWT
  rw [FT]
  have : ExtendFromT T y false = y w0 := by simp [ExtendFromT, T, w0]
  rw [this]; rfl

theorem not_mnat : ¬ MNaturalConvex (InducedFTildeOnT tl hd S T fa f) := by
  intro h
  have hL : ∀ z : Option W → ℤ, LiftedFunction (InducedFTildeOnT tl hd S T fa f) z =
      if z none = -z (some w0) then psi (z (some w0)) else ⊤ := by
    intro z
    unfold LiftedFunction
    rw [Fintype.sum_subsingleton _ w0, FTOnT]
  let x : Option W → ℤ := fun o => o.elim (-3) (fun _ => 3)
  let y : Option W → ℤ := fun _ => 0
  have hx : x ∈ DomZ (LiftedFunction (InducedFTildeOnT tl hd S T fa f)) := by
    show _ ≠ ⊤; rw [hL]; simp [x, psi]
  have hy : y ∈ DomZ (LiftedFunction (InducedFTildeOnT tl hd S T fa f)) := by
    show _ ≠ ⊤; rw [hL]; simp [y, psi]
  obtain ⟨v, hv, hineq⟩ := h x hx y hy (some w0) (by simp [SuppPos, x, y])
  cases v with
  | some u => simp [SuppNeg, x, y] at hv
  | none =>
    rw [hL, hL, hL, hL] at hineq
    simp [x, y, psi] at hineq

end ZRCex

open ZRCex in
theorem solution : ¬ (∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (tail head : A → V) (S T : Finset V) (fa ga : A → ℤ → WithTop ℝ)
    (f g : (V → ℤ) → WithTop ℝ) (hfa : ∀ a, DiscreteConvexUnivariate (fa a))
    (hga : ∀ a, DiscreteConvexUnivariate (ga a))
    (hfbdd : ∀ y, InducedFTilde tail head S T fa f y ≠ ⊥)
    (hfprop : ∃ y, InducedFTilde tail head S T fa f y ≠ ⊤)
    (hgbdd : ∀ q, InducedGTilde tail head S T ga g q ≠ ⊥)
    (hgprop : ∃ q, InducedGTilde tail head S T ga g q ≠ ⊤),
    (MExchangeAxiom f → MExchangeAxiom (InducedFTildeOnT tail head S T fa f)) ∧
    (MNaturalConvex f → MNaturalConvex (InducedFTildeOnT tail head S T fa f)) ∧
    ((SBF g ∧ TRF g) →
      SBF (InducedGTildeOnT tail head S T ga g) ∧ TRF (InducedGTildeOnT tail head S T ga g)) ∧
    (LNaturalConvex g → LNaturalConvex (InducedGTildeOnT tail head S T ga g))) := by
  intro h
  have H := h tl hd S T fa ga f g (fun _ => psi_dcu) (fun _ => ⟨⟨0, by simp [ga]⟩, fun _ => by simp [ga]⟩)
    (fun y => by rw [FT]; exact WithBot.coe_ne_bot)
    ⟨fun _ => 0, by rw [FT]; simp [psi]; exact ne_of_beq_false rfl⟩
    (fun q => by rw [GT]; exact EReal.zero_ne_bot)
    ⟨fun _ => 0, by rw [GT]; exact EReal.zero_ne_top⟩
  exact not_mnat (H.2.1 f_mnat)

#print axioms solution
