-- Prove2me | solution 1 for CollabProject.TimeDep.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:35:57.514279+00:00
-- url     : https://prove2.me/submissions/4175c6d9-f813-43bc-8e31-1e94fea6a273

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Model

open CollabProject.TimeDep

namespace CollabProject.TimeDep.T6Aux

/-- The unique best response of a classed manufacturer type. -/
noncomputable def br (T : MType) : Act → Act
  | .keep => if T.p10 < T.s0 then .delay else .keep
  | .delay => if T.p20 < T.s0 then .delay else .keep

lemma br_spec (T : MType) (hc : T.Classed) (a a0 : Act) :
    IsBR0 T a a0 ↔ a0 = br T a := by
  obtain ⟨h12, h1, h2⟩ := hc
  unfold IsBR0 SequentialGame.IsBR0
  constructor
  · intro h
    have hk := h .keep
    have hd := h .delay
    cases a <;> cases a0 <;>
      simp [br, u0, delayCount, penalty, Act.delayPeriods] at hk hd ⊢ <;>
      first
        | linarith
        | (rcases lt_or_gt_of_ne h1 with h | h <;> linarith)
        | (rcases lt_or_gt_of_ne h2 with h | h <;> linarith)
  · rintro rfl b
    cases a <;> cases b <;>
      simp [br, u0, delayCount, penalty, Act.delayPeriods] <;>
      split_ifs <;> simp <;> linarith

lemma low_high (T : MType) (hc : T.Classed) (w : ℝ) (hw : 0 ≤ w) :
    (if T.s0 < T.p10 then w else 0) + (if T.p20 < T.s0 then w else 0) ≤ w := by
  obtain ⟨h12, h1, h2⟩ := hc
  split_ifs <;> linarith

lemma term_diff (S : SType) (T : MType) (hc : T.Classed) (w : ℝ) :
    w * u1 S .delay (br T .delay) - w * u1 S .keep (br T .keep) =
      w * S.s1 - S.p11 * (if T.s0 < T.p10 then w else 0)
        - S.p21 * (if T.p20 < T.s0 then w else 0) := by
  obtain ⟨h12, h1, h2⟩ := hc
  rcases lt_or_gt_of_ne h1 with c1 | c1 <;>
  rcases lt_or_gt_of_ne h2 with c2 | c2 <;>
  simp [br, u1, delayCount, penalty, Act.delayPeriods, c1, c2,
    not_lt.mpr c1.le, not_lt.mpr c2.le] <;>
  first | ring | (exfalso; linarith) | (simp [show ¬ T.p20 < T.s0 by linarith]; ring) | (simp [show ¬ T.s0 < T.p10 by linarith]; ring)

lemma core (S : SType) (M : MType) (h : Standing S M) (hG : Generic S M)
    (X : ℝ) (hX : S.s1 < X → S.s1 < S.p21) (htie : S.s1 ≠ X)
    (a1 b1 : Act) (E : Act → ℝ) (hE : E .delay - E .keep = S.s1 - X)
    (ha : ∀ b, u1 S b (br M b) ≤ u1 S a1 (br M a1)) (hb : ∀ b, E b ≤ E b1) :
    delayCount b1 (br M b1) < delayCount a1 (br M a1) ↔
      (S.p11 < S.s1 ∧ S.s1 < S.p21 ∧ M.s0 < M.p10 ∧ M.p10 < M.p20 ∧ S.s1 < X) := by
  obtain ⟨hs1, hs0, -, -, -, hp1, hp0⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := hG
  have ha1 := ha .keep
  have ha2 := ha .delay
  have hb1 := hb .keep
  have hb2 := hb .delay
  rcases lt_or_gt_of_ne g1 with c1 | c1 <;>
  rcases lt_or_gt_of_ne g2 with c2 | c2 <;>
  rcases lt_or_gt_of_ne g3 with c3 | c3 <;>
  rcases lt_or_gt_of_ne g4 with c4 | c4 <;>
  rcases lt_or_gt_of_ne htie with c5 | c5 <;>
  cases a1 <;> cases b1 <;>
  simp [br, u1, delayCount, penalty, Act.delayPeriods, c1, c2, c3, c4, c5,
    not_lt.mpr c1.le, not_lt.mpr c2.le, not_lt.mpr c3.le, not_lt.mpr c4.le,
    lt_asymm c1, lt_asymm c2, lt_asymm c3, lt_asymm c4, hp0] at ha1 ha2 hb1 hb2 ⊢ <;>
  first
    | linarith
    | (have := hX c5; linarith)
    | (intros; linarith)
    | skip

end CollabProject.TimeDep.T6Aux

open CollabProject.TimeDep.T6Aux in
theorem solution {ι : Type} [Fintype ι]
    (S : SType) (M : MType) (B : Belief ι)
    (h : Standing S M) (hG : Generic S M)
    (hB : ∀ i, (B.θ i).Classed)
    (htie : S.s1 ≠ S.p11 * qLow B + S.p21 * qHigh B) :
    (∀ (a1 : Act) (σ0 : Act → Act) (b1 : Act)
      (σ : ι → Act → Act) (τ0 : Act → Act),
      IsSPNE S M a1 σ0 → IsAsymEq S B M b1 σ τ0 →
      delayCount b1 (τ0 b1) < delayCount a1 (σ0 a1)) ↔
      (S.p11 < S.s1 ∧ S.s1 < S.p21 ∧ M.s0 < M.p10 ∧ M.p10 < M.p20 ∧
       S.s1 < S.p11 * qLow B + S.p21 * qHigh B) := by
  have hMc : M.Classed := ⟨h.2.2.2.2.2.2, hG.1, hG.2.1⟩
  set X := S.p11 * qLow B + S.p21 * qHigh B with hXdef
  have hqL : 0 ≤ qLow B := Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact B.w_nonneg i
    · exact le_refl _
  have hqH : 0 ≤ qHigh B := Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact B.w_nonneg i
    · exact le_refl _
  have hq : qLow B + qHigh B ≤ 1 := by
    rw [← B.w_sum]
    unfold qLow qHigh
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => low_high _ (hB i) _ (B.w_nonneg i)
  have hX : S.s1 < X → S.s1 < S.p21 := by
    intro hlt
    have hp := h.2.2.2.2.2.1
    have hs := h.1
    have e1 : S.p11 * qLow B ≤ S.p21 * qLow B := by nlinarith
    by_cases hp21 : 0 ≤ S.p21
    · nlinarith
    · nlinarith
  -- the expected-payoff difference under best responses
  let σc : ι → Act → Act := fun i => br (B.θ i)
  have hE : expU1 S B σc .delay - expU1 S B σc .keep = S.s1 - X := by
    unfold expU1
    rw [← Finset.sum_sub_distrib]
    simp only [σc]
    rw [Finset.sum_congr rfl fun i _ => term_diff S (B.θ i) (hB i) (B.w i)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, B.w_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [qLow, qHigh, hXdef]
    ring
  -- reduce arbitrary equilibria to best-response form
  have red : ∀ (a1 : Act) (σ0 : Act → Act) (b1 : Act)
      (σ : ι → Act → Act) (τ0 : Act → Act),
      IsSPNE S M a1 σ0 → IsAsymEq S B M b1 σ τ0 →
      (σ0 = br M ∧ τ0 = br M ∧ σ = σc ∧
        (∀ b, u1 S b (br M b) ≤ u1 S a1 (br M a1)) ∧
        (∀ b, expU1 S B σc b ≤ expU1 S B σc b1)) := by
    intro a1 σ0 b1 σ τ0 hS hA
    have e0 : σ0 = br M := funext fun a => (br_spec M hMc a (σ0 a)).1 (hS.1 a)
    have e1 : τ0 = br M := funext fun a => (br_spec M hMc a (τ0 a)).1 (hA.2.1 a)
    have e2 : σ = σc := funext fun i => funext fun a =>
      (br_spec (B.θ i) (hB i) a (σ i a)).1 (hA.1 i a)
    refine ⟨e0, e1, e2, ?_, ?_⟩
    · intro b; have := hS.2 b; rw [e0] at this; exact this
    · intro b; have := hA.2.2 b; rw [e2] at this; exact this
  constructor
  · intro H
    -- construct canonical equilibria
    obtain ⟨a1, ha1⟩ : ∃ a1 : Act, ∀ b, u1 S b (br M b) ≤ u1 S a1 (br M a1) := by
      by_cases hc : u1 S .keep (br M .keep) ≤ u1 S .delay (br M .delay)
      · exact ⟨.delay, fun b => by cases b <;> first | exact le_refl _ | exact hc⟩
      · push_neg at hc; exact ⟨.keep, fun b => by cases b <;> first | exact le_refl _ | exact hc.le⟩
    obtain ⟨b1, hb1⟩ : ∃ b1 : Act, ∀ b, expU1 S B σc b ≤ expU1 S B σc b1 := by
      by_cases hc : expU1 S B σc .keep ≤ expU1 S B σc .delay
      · exact ⟨.delay, fun b => by cases b <;> first | exact le_refl _ | exact hc⟩
      · push_neg at hc; exact ⟨.keep, fun b => by cases b <;> first | exact le_refl _ | exact hc.le⟩
    have hSP : IsSPNE S M a1 (br M) :=
      ⟨fun a => (br_spec M hMc a _).2 rfl, ha1⟩
    have hAE : IsAsymEq S B M b1 σc (br M) :=
      ⟨fun i a => (br_spec (B.θ i) (hB i) a _).2 rfl,
       fun a => (br_spec M hMc a _).2 rfl, hb1⟩
    have := H a1 (br M) b1 σc (br M) hSP hAE
    exact (core S M h hG X hX htie a1 b1 (expU1 S B σc) hE ha1 hb1).1 this
  · intro hc a1 σ0 b1 σ τ0 hS hA
    obtain ⟨e0, e1, -, ha1, hb1⟩ := red a1 σ0 b1 σ τ0 hS hA
    subst e0 e1
    exact (core S M h hG X hX htie a1 b1 (expU1 S B σc) hE ha1 hb1).2 hc
