-- Prove2me | solution 1 for CelestialWedge.wedge_bracket_lie
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:38:58.588068+00:00
-- url     : https://prove2.me/submissions/a505a3cd-35bd-4d5a-bbca-5426b14560fa

import Mathlib
import Definitions.Def_celestial_wedge_algebra

namespace CelestialWedgeAux74

open CelestialWedge

/-- structure constant on raw labels -/
def om (x y : ℚ × ℚ) : ℚ := structConst x.1 x.2 y.1 y.2

/-- label sum -/
def sh (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 + y.1 - 2, x.2 + y.2)

/-- untruncated bracket on all labels -/
noncomputable def B : (ℚ × ℚ →₀ ℂ) →ₗ[ℂ] (ℚ × ℚ →₀ ℂ) →ₗ[ℂ] (ℚ × ℚ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun x =>
    Finsupp.linearCombination ℂ fun y => ((om x y : ℚ) : ℂ) • Finsupp.single (sh x y) (1 : ℂ)

lemma B_single (x y : ℚ × ℚ) (a b : ℂ) :
    B (Finsupp.single x a) (Finsupp.single y b) =
      Finsupp.single (sh x y) (a * b * ((om x y : ℚ) : ℂ)) := by
  simp only [B, Finsupp.linearCombination_single, LinearMap.smul_apply, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  congr 1
  ring

/-- embedding -/
noncomputable def Phi : WedgeSpace →ₗ[ℂ] (ℚ × ℚ →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ Subtype.val

lemma Phi_injective : Function.Injective Phi := by
  intro X Y h
  exact Finsupp.mapDomain_injective Subtype.val_injective h

lemma Phi_single (x : WedgeIndex) (a : ℂ) :
    Phi (Finsupp.single x a) = Finsupp.single x.1 a := by
  exact Finsupp.mapDomain_single

lemma om_zero_of_not (x y : WedgeIndex)
    (h : ¬ InWedge (x.1.1 + y.1.1 - 2) (x.1.2 + y.1.2)) : om x.1 y.1 = 0 := by
  obtain ⟨⟨p, m⟩, a, b, h1, h2⟩ := x
  obtain ⟨⟨q, n⟩, c, d, h3, h4⟩ := y
  simp only at h1 h2 h3 h4 h ⊢
  have hm : m = ((a : ℚ) - b) / 2 := by linarith
  have hp : p = ((a : ℚ) + b) / 2 + 1 := by linarith
  have hn : n = ((c : ℚ) - d) / 2 := by linarith
  have hq : q = ((c : ℚ) + d) / 2 + 1 := by linarith
  have key : a + c = 0 ∨ b + d = 0 := by
    by_contra hc
    simp only [not_or] at hc
    apply h
    refine ⟨a + c - 1, b + d - 1, ?_, ?_⟩
    · have : 1 ≤ a + c := Nat.one_le_iff_ne_zero.mpr hc.1
      push_cast [this]
      linarith
    · have : 1 ≤ b + d := Nat.one_le_iff_ne_zero.mpr hc.2
      push_cast [this]
      linarith
  simp only [om, structConst]
  rw [hm, hp, hn, hq]
  rcases key with k | k
  · have ha : a = 0 := by omega
    have hc : c = 0 := by omega
    subst ha hc
    push_cast
    ring
  · have hb : b = 0 := by omega
    have hd : d = 0 := by omega
    subst hb hd
    push_cast
    ring

lemma Phi_bracketGen (x y : WedgeIndex) :
    Phi (bracketGen x y) = Finsupp.single (sh x.1 y.1) ((om x.1 y.1 : ℚ) : ℂ) := by
  unfold bracketGen
  split_ifs with h
  · rw [map_smul]
    erw [Phi_single]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  · rw [om_zero_of_not x y h]
    simp

lemma Phi_bracket (X Y : WedgeSpace) : Phi (bracket X Y) = B (Phi X) (Phi Y) := by
  induction X using Finsupp.induction_linear with
  | zero => simp
  | add X1 X2 h1 h2 => simp [h1, h2]
  | single x a =>
    induction Y using Finsupp.induction_linear with
    | zero => simp
    | add Y1 Y2 h1 h2 => simp only [map_add, h1, h2]
    | single y b =>
      rw [Phi_single, Phi_single, B_single]
      simp only [bracket, Finsupp.linearCombination_single, LinearMap.smul_apply, map_smul,
        Phi_bracketGen, Finsupp.smul_single, smul_eq_mul]
      congr 1
      ring

lemma B_antisymm (U V : ℚ × ℚ →₀ ℂ) : B U V = - B V U := by
  induction U using Finsupp.induction_linear with
  | zero => simp
  | add U1 U2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2, neg_add]
  | single x a =>
    induction V using Finsupp.induction_linear with
    | zero => simp
    | add V1 V2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2, neg_add]
    | single y b =>
      rw [B_single, B_single, ← Finsupp.single_neg]
      have : sh x y = sh y x := by
        simp only [sh, Prod.mk.injEq]; constructor <;> ring
      rw [this]
      congr 1
      simp only [om, structConst]
      push_cast
      ring

lemma B_self (U : ℚ × ℚ →₀ ℂ) : B U U = 0 := by
  have h := B_antisymm U U
  have h2 : (2 : ℂ) • B U U = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

lemma B_jacobi (U V W : ℚ × ℚ →₀ ℂ) :
    B U (B V W) = B (B U V) W + B V (B U W) := by
  induction U using Finsupp.induction_linear with
  | zero => simp
  | add U1 U2 h1 h2 =>
    simp only [map_add, LinearMap.add_apply, h1, h2]
    abel
  | single x a =>
    induction V using Finsupp.induction_linear with
    | zero => simp
    | add V1 V2 h1 h2 =>
      simp only [map_add, LinearMap.add_apply, h1, h2]
      abel
    | single y b =>
      induction W using Finsupp.induction_linear with
      | zero => simp
      | add W1 W2 h1 h2 =>
        simp only [map_add, LinearMap.add_apply, h1, h2]
        abel
      | single z c =>
        rw [B_single, B_single, B_single, B_single, B_single, B_single]
        have e1 : sh (sh x y) z = sh x (sh y z) := by
          simp only [sh, Prod.mk.injEq]; constructor <;> ring
        have e2 : sh y (sh x z) = sh x (sh y z) := by
          simp only [sh, Prod.mk.injEq]; constructor <;> ring
        rw [e1, e2, ← Finsupp.single_add]
        congr 1
        simp only [om, structConst, sh]
        push_cast
        ring

end CelestialWedgeAux74

open CelestialWedgeAux74 in
open CelestialWedge in
theorem solution :
    (∀ X : WedgeSpace, bracket X X = 0) ∧
    (∀ X Y Z : WedgeSpace,
      bracket X (bracket Y Z) = bracket (bracket X Y) Z + bracket Y (bracket X Z)) := by
  refine ⟨fun X => ?_, fun X Y Z => ?_⟩
  · apply Phi_injective
    rw [Phi_bracket, B_self, map_zero]
  · apply Phi_injective
    rw [map_add, Phi_bracket, Phi_bracket, Phi_bracket, Phi_bracket, Phi_bracket, Phi_bracket]
    exact B_jacobi _ _ _
