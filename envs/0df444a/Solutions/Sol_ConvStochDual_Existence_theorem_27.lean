-- Prove2me | solution 1 for ConvStochDual.Existence.theorem_27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:08:06.561235+00:00
-- url     : https://prove2.me/submissions/a743e45d-9d0e-4d99-80cf-d8d5b2935ab0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConvStochDual_Existence_Setting
import Theorems.Thm_ConvStochDual_Existence_theorem_18
import Theorems.Thm_ConvStochDual_Existence_theorem_26
import Theorems.Thm_ConvStochDual_Existence_pp13_weak_duality_optimality

open MeasureTheory
open ConvStochDual.Existence

theorem solution {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}
    (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (hEf : EfProperLsc s) (hEt : CondExpClosed s)
    (hpos : LinClosed (pos ((fun q : X × U => q - (0, s.ubar)) '' domPhi s)))
    (hA23 : Assumption23_1 s ∧ Assumption23_2 s) :
    valSP s = valSPX s ∧ valSPX s = valD s ∧
    (∃ p : V, p ∈ XaPerp s ∧ ∃ y : Y, dualObj s p y = valD s) ∧
    (∀ x : RV Ω P n, Adapted τ 𝔽 P x → Ef s x (ιU s.ubar) < ⊤ →
      ((Ef s x (ιU s.ubar) ≠ ⊥ ∧
          ∀ x' : RV Ω P n, Adapted τ 𝔽 P x' → Ef s x (ιU s.ubar) ≤ Ef s x' (ιU s.ubar)) →
        ∃ p : V, p ∈ XaPerp s ∧ ∃ y : Y,
          ∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω)
            (p.1 ω) (y.1 ω)) ∧
      ((∃ p : V, p ∈ XaPerp s ∧ ∃ y : Y,
          ∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω)
            (p.1 ω) (y.1 ω)) →
        ∀ x' : RV Ω P n, Adapted τ 𝔽 P x' → Ef s x (ιU s.ubar) ≤ Ef s x' (ιU s.ubar))) := by
  obtain ⟨⟨p0, y0, hatt⟩, hSPX⟩ := theorem_18 s hS hEf hpos
  obtain ⟨hDsD, hiff⟩ := theorem_26 s hS hEf hEt hA23
  obtain ⟨p, hp, y, hpy⟩ := hiff.mp ⟨p0, y0, hatt⟩
  have hSPXD : valSPX s = valD s := hSPX.trans hDsD
  -- weak duality
  have hweak : ∀ x : RV Ω P n, Adapted τ 𝔽 P x → valD s ≤ Ef s x (ιU s.ubar) := by
    intro x hx
    rw [← hpy]
    exact (pp13_weak_duality_optimality s hS x hx p hp y).1
  have hSP_le : valSP s ≤ valSPX s := by
    unfold valSPX phi valSP
    refine le_iInf fun x => le_iInf fun hx => ?_
    refine iInf₂_le (ιX x) ?_
    simpa using hx
  have hSP_ge : valSPX s ≤ valSP s := by
    rw [hSPXD]
    unfold valSP
    exact le_iInf fun x => le_iInf fun hx => hweak x hx
  have hSP : valSP s = valSPX s := le_antisymm hSP_le hSP_ge
  refine ⟨hSP, hSPXD, ⟨p, hp, y, hpy⟩, ?_⟩
  intro x hx hfin
  refine ⟨?_, ?_⟩
  · rintro ⟨hbot, hopt⟩
    refine ⟨p, hp, y, ?_⟩
    have hEq : Ef s x (ιU s.ubar) = valSP s := by
      apply le_antisymm
      · unfold valSP
        exact le_iInf fun x' => le_iInf fun hx' => hopt x' hx'
      · unfold valSP
        exact iInf₂_le x hx
    have hdual : dualObj s p y = Ef s x (ιU s.ubar) := by
      rw [hpy, hEq, hSP, hSPXD]
    exact (pp13_weak_duality_optimality s hS x hx p hp y).2.1 hfin.ne hbot hdual
  · rintro ⟨p', hp', y', hsub⟩
    exact (pp13_weak_duality_optimality s hS x hx p' hp' y').2.2 hfin hsub
