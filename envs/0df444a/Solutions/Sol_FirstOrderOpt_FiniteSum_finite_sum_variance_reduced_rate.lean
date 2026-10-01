-- Prove2me | solution 1 for FirstOrderOpt.FiniteSum.finite_sum_variance_reduced_rate
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T17:29:50.170864+00:00
-- url     : https://prove2.me/submissions/f2ff7f39-4d92-42ec-b5fe-0a318c6df146

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Set E) (Ψ : E → ℝ) (V : E → E → ℝ)
    (LQ : ℝ) (hLQ : 0 < LQ)
    (γ : ℝ) (hγ : γ = 1 / (16 * LQ))
    (T : ℕ → ℝ) (hT1 : T 1 = 7) (hT0 : T 0 = T 1 / 2) (hTrec : ∀ s, 2 ≤ s → T s = 2 * T (s - 1))
    (w : ℕ → ℝ) (hw : ∀ s, 1 ≤ s → w s = (1 - 4 * LQ * γ) * (T (s - 1) - 1) - 4 * LQ * γ * T s)
    (hwpos : ∀ s, 1 ≤ s → 0 < w s)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y)
    (S : ℕ) (hS : 1 ≤ S)
    (xtilde : ℕ → Ω → E) (hxtilde : ∀ s, 1 ≤ s → ∀ ω, xtilde s ω ∈ X)
    (x : ℕ → Ω → E) (hx : ∀ s, ∀ ω, x s ω ∈ X)
    (hx0eq : ∀ ω, x 0 ω = x0) (hxtilde0eq : ∀ ω, xtilde 0 ω = x0)
    (hintx : ∀ s, Integrable (fun ω => Ψ (x s ω)) μ)
    (hintxtilde : ∀ s, Integrable (fun ω => Ψ (xtilde s ω)) μ)
    (hintVxs : ∀ s, Integrable (fun ω => V (x s ω) xstar) μ)
    (hepoch : ∀ s, 1 ≤ s →
      γ * (∫ ω, Ψ (x s ω) ∂μ - Ψ xstar) +
        (1 - 4 * LQ * γ) * γ * (T s - 1) * (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) +
        ∫ ω, V (x s ω) xstar ∂μ
      ≤ γ * (∫ ω, Ψ (x (s - 1) ω) ∂μ - Ψ xstar) +
        4 * LQ * γ ^ 2 * T s * (∫ ω, Ψ (xtilde (s - 1) ω) ∂μ - Ψ xstar) +
        ∫ ω, V (x (s - 1) ω) xstar ∂μ)
    (xbar : Ω → E)
    (hxbar : ∀ ω, xbar ω =
      (∑ s ∈ Finset.Icc 1 S, w s)⁻¹ • ∑ s ∈ Finset.Icc 1 S, w s • xtilde s ω)
    (hint : Integrable (fun ω => Ψ (xbar ω)) μ),
∫ ω, Ψ (xbar ω) ∂μ - Ψ xstar ≤
      (8 / (2 : ℝ) ^ (S - 1)) * ((11 / 4) * (Ψ x0 - Ψ xstar) + 16 * LQ * V x0 xstar)) := by
  intro h
  let T:ℕ→ℝ:=fun s=>7/2*(2:ℝ)^s
  let w:ℕ→ℝ:=fun s=>(3/4)*(T (s-1)-1)-(1/4)*T s
  have hrec:∀s,1≤s→T s=2*T (s-1):=by
    intro s hs
    dsimp [T]
    conv_lhs => rw [show s=s-1+1 by omega,pow_succ]
    ring
  have hwpos:∀s,1≤s→0<w s:=by
    intro s hs
    have ht:T (s-1)≥7/2:=by
      have hp:(1:ℝ)≤(2:ℝ)^(s-1):=one_le_pow₀ (by norm_num)
      dsimp [T]
      nlinarith
    dsimp [w]
    rw [hrec s hs]
    linarith
  have hb:=h (E:=ℝ) (Ω:=Unit) (μ:=Measure.dirac ()) (X:=Set.univ)
    (Ψ:=fun _=>0) (V:=fun _ _=>-1) (LQ:=1) (hLQ:=by norm_num)
    (γ:=1/16) (hγ:=by norm_num)
    (T:=T) (hT1:=by norm_num [T]) (hT0:=by norm_num [T]) (hTrec:=fun s hs=>hrec s (by omega))
    (w:=w) (hw:=by intro s hs;dsimp [w];norm_num) (hwpos:=hwpos)
    (x0:=0) (xstar:=0) (hx0:=Set.mem_univ _) (hxstar:=Set.mem_univ _)
    (hxstar_opt:=by intros;exact le_rfl) (S:=1) (hS:=le_rfl)
    (xtilde:=fun _ _=>0) (hxtilde:=by intros;trivial)
    (x:=fun _ _=>0) (hx:=by intros;trivial) (hx0eq:=by intros;rfl) (hxtilde0eq:=by intros;rfl)
    (hintx:=by intro s;exact integrable_const _) (hintxtilde:=by intro s;exact integrable_const _)
    (hintVxs:=by intro s;exact integrable_const _)
    (hepoch:=by intro s hs;simp)
    (xbar:=fun _=>0) (hxbar:=by intro ω;simp) (hint:=integrable_const _)
  norm_num at hb
