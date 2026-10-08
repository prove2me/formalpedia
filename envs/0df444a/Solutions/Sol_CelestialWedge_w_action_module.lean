-- Prove2me | solution 1 for CelestialWedge.w_action_module
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:00:45.917162+00:00
-- url     : https://prove2.me/submissions/68876f35-6d65-458d-aa0a-235a0367d8a5

import Mathlib
import Definitions.Def_celestial_wedge_algebra
import Definitions.Def_celestial_gluon_s_algebra

set_option autoImplicit false

universe u

namespace CelestialWedgeWAux

open CelestialWedge Complex

open Classical in
noncomputable def Sp {ι : Type u} (P M : ℚ) (a : ι) : SSpace ι :=
  if h : InWedge P M then Finsupp.single (⟨(P, M), h⟩, a) 1 else 0

open Classical in
noncomputable def Gp (P M : ℚ) : WedgeSpace :=
  if h : InWedge P M then Finsupp.single ⟨(P, M), h⟩ 1 else 0

lemma Sp_congr {ι : Type u} {P M P' M' : ℚ} (a : ι) (h1 : P = P') (h2 : M = M') :
    Sp P M a = Sp P' M' a := by
  subst h1; subst h2; rfl

lemma structConst_zero (x : WedgeIndex) (Q N : ℚ) (hy : InWedge Q N)
    (h : ¬ InWedge (x.1.1 + Q - 2) (x.1.2 + N)) :
    structConst x.1.1 x.1.2 Q N = 0 := by
  obtain ⟨a, b, ha, hb⟩ := x.2
  obtain ⟨c, d, hc, hd⟩ := hy
  unfold structConst
  rcases Nat.eq_zero_or_pos (a + c) with hac | hac
  · have ha0 : a = 0 := by omega
    have hc0 : c = 0 := by omega
    subst ha0; subst hc0
    simp only [Nat.cast_zero] at ha hc
    linear_combination (Q - 1) * ha - (x.1.1 - 1) * hc
  rcases Nat.eq_zero_or_pos (b + d) with hbd | hbd
  · have hb0 : b = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hb0; subst hd0
    simp only [Nat.cast_zero] at hb hd
    linear_combination -(Q - 1) * hb + (x.1.1 - 1) * hd
  exfalso
  apply h
  refine ⟨a + c - 1, b + d - 1, ?_, ?_⟩
  · rw [Nat.cast_sub (by omega)]; push_cast; linarith
  · rw [Nat.cast_sub (by omega)]; push_cast; linarith

lemma wActGen_eq {ι : Type u} (x : WedgeIndex) (y : WedgeIndex × ι) :
    wActGen x y = ((structConst x.1.1 x.1.2 y.1.1.1 y.1.1.2 : ℚ) : ℂ) •
      Sp (x.1.1 + y.1.1.1 - 2) (x.1.2 + y.1.1.2) y.2 := by
  unfold wActGen Sp
  split_ifs <;> simp

lemma bracketGen_eq (x y : WedgeIndex) :
    bracketGen x y = ((structConst x.1.1 x.1.2 y.1.1 y.1.2 : ℚ) : ℂ) •
      Gp (x.1.1 + y.1.1 - 2) (x.1.2 + y.1.2) := by
  unfold bracketGen Gp
  split_ifs <;> simp

lemma wAct_single {ι : Type u} (x : WedgeIndex) (y : WedgeIndex × ι) :
    wAct (Finsupp.single x 1) (Finsupp.single y 1) = wActGen x y := by
  simp [wAct, Finsupp.linearCombination_single]

lemma bracket_single (x y : WedgeIndex) :
    bracket (Finsupp.single x 1) (Finsupp.single y 1) = bracketGen x y := by
  simp [bracket, Finsupp.linearCombination_single]

lemma act_Sp {ι : Type u} (x : WedgeIndex) (P M : ℚ) (a : ι) (c : ℂ)
    (hc : ¬ InWedge P M → c = 0) :
    c • wAct (Finsupp.single x 1) (Sp P M a) =
      (c * ((structConst x.1.1 x.1.2 P M : ℚ) : ℂ)) • Sp (x.1.1 + P - 2) (x.1.2 + M) a := by
  by_cases h : InWedge P M
  · have : Sp P M a = (Finsupp.single ((⟨(P, M), h⟩ : WedgeIndex), a) 1 : SSpace ι) :=
      dif_pos h
    rw [this, wAct_single, wActGen_eq, smul_smul]
  · rw [hc h]; simp

lemma Gp_act {ι : Type u} (P M : ℚ) (s : WedgeIndex × ι) (c : ℂ)
    (hc : ¬ InWedge P M → c = 0) :
    c • wAct (Gp P M) (Finsupp.single s 1) =
      (c * ((structConst P M s.1.1.1 s.1.1.2 : ℚ) : ℂ)) •
        Sp (P + s.1.1.1 - 2) (M + s.1.1.2) s.2 := by
  by_cases h : InWedge P M
  · have : Gp P M = (Finsupp.single (⟨(P, M), h⟩ : WedgeIndex) 1 : WedgeSpace) :=
      dif_pos h
    rw [this]
    have e := wActGen_eq (ι := ι) (⟨(P, M), h⟩ : WedgeIndex) s
    erw [wAct_single, e, smul_smul]
  · rw [hc h]; simp

lemma basis {ι : Type u} (x y : WedgeIndex) (s : WedgeIndex × ι) :
    wAct (bracket (Finsupp.single x 1) (Finsupp.single y 1)) (Finsupp.single s 1) =
      wAct (Finsupp.single x 1) (wAct (Finsupp.single y 1) (Finsupp.single s 1)) -
        wAct (Finsupp.single y 1) (wAct (Finsupp.single x 1) (Finsupp.single s 1)) := by
  rw [bracket_single, bracketGen_eq, map_smul, LinearMap.smul_apply,
    Gp_act _ _ _ _ (fun h => by rw [structConst_zero x y.1.1 y.1.2 y.2 h]; simp)]
  rw [wAct_single, wActGen_eq, map_smul,
    act_Sp _ _ _ _ _ (fun h => by rw [structConst_zero y s.1.1.1 s.1.1.2 s.1.2 h]; simp)]
  rw [wAct_single, wActGen_eq, map_smul,
    act_Sp _ _ _ _ _ (fun h => by rw [structConst_zero x s.1.1.1 s.1.1.2 s.1.2 h]; simp)]
  rw [Sp_congr s.2 (show x.1.1 + (y.1.1 + s.1.1.1 - 2) - 2 = x.1.1 + y.1.1 - 2 + s.1.1.1 - 2 by ring)
      (show x.1.2 + (y.1.2 + s.1.1.2) = x.1.2 + y.1.2 + s.1.1.2 by ring),
    Sp_congr s.2 (show y.1.1 + (x.1.1 + s.1.1.1 - 2) - 2 = x.1.1 + y.1.1 - 2 + s.1.1.1 - 2 by ring)
      (show y.1.2 + (x.1.2 + s.1.1.2) = x.1.2 + y.1.2 + s.1.1.2 by ring),
    ← sub_smul]
  congr 1
  unfold structConst
  push_cast
  ring

theorem main {ι : Type u} (X Y : WedgeSpace) (s : SSpace ι) :
    wAct (bracket X Y) s = wAct X (wAct Y s) - wAct Y (wAct X s) := by
  induction X using Finsupp.induction_linear with
  | zero => simp
  | add X1 X2 h1 h2 =>
    simp only [map_add, LinearMap.add_apply, h1, h2]
    abel
  | single x r =>
    induction Y using Finsupp.induction_linear with
    | zero => simp
    | add Y1 Y2 h1 h2 =>
      simp only [map_add, LinearMap.add_apply, h1, h2]
      abel
    | single y t =>
      induction s using Finsupp.induction_linear with
      | zero => simp
      | add s1 s2 h1 h2 =>
        simp only [map_add, h1, h2]
        abel
      | single z v =>
        rw [← Finsupp.smul_single_one x r, ← Finsupp.smul_single_one y t,
          ← Finsupp.smul_single_one z v]
        simp only [map_smul, LinearMap.smul_apply]
        rw [basis x y z]
        simp only [smul_sub, smul_smul]
        congr 1 <;> congr 1 <;> ring

end CelestialWedgeWAux

open CelestialWedge Complex in
theorem solution {ι : Type*} (X Y : WedgeSpace) (s : SSpace ι) :
    wAct (bracket X Y) s = wAct X (wAct Y s) - wAct Y (wAct X s) := by
  exact CelestialWedgeWAux.main X Y s
