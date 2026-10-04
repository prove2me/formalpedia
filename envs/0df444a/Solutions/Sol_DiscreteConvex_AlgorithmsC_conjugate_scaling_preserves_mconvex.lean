-- Prove2me | solution 1 for DiscreteConvex.AlgorithmsC.conjugate_scaling_preserves_mconvex
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:23:42.768982+00:00
-- url     : https://prove2.me/submissions/cfffc27e-1f99-40b8-ae25-b1cec7ef1dfa

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_AlgorithmsC_ScaledConjugate
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateFromZ
import Definitions.Def_DiscreteConvex_AlgorithmsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScalingE
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScaling

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.AlgorithmsC

namespace ScalingCex

/-- The indicator of `{0} ⊆ ℤ^Unit`. -/
noncomputable def g0 (p : Unit → ℤ) : WithTop ℝ := if p () = 0 then ((0 : ℝ) : WithTop ℝ) else ⊤

theorem g0_lnat : LNaturalConvex g0 := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro x y
    unfold LiftedFunctionL g0
    by_cases hx : x (some ()) - x none = 0
    · by_cases hy : y (some ()) - y none = 0
      · have h1 : (x ⊔ y) (some ()) - (x ⊔ y) none = 0 := by
          simp only [Pi.sup_apply]
          rw [show x (some ()) = x none by omega, show y (some ()) = y none by omega]; simp
        have h2 : (x ⊓ y) (some ()) - (x ⊓ y) none = 0 := by
          simp only [Pi.inf_apply]
          rw [show x (some ()) = x none by omega, show y (some ()) = y none by omega]; simp
        simp only [hx, hy, h1, h2, if_true]
        exact le_rfl
      · simp only [hy, if_false]; simp
    · simp only [hx, if_false]; simp
  · intro p
    unfold LiftedFunctionL g0
    simp only [Pi.add_apply, Pi.one_apply, WithTop.coe_zero, add_zero]
    have : p (some ()) + 1 - (p none + 1) = p (some ()) - p none := by ring
    rw [this]

theorem conjE (x : Unit → ℝ) : ConjugateScalingE g0 1 x = 0 := by
  unfold ConjugateScalingE ConjugateFromZE
  apply le_antisymm
  · refine sSup_le ?_
    rintro v ⟨p, rfl⟩
    by_cases hp : p () = 0
    · have hs : (∑ i, (p i : ℝ) * x i) = 0 := by simp [hp]
      have hg : ScaledConjugate g0 1 p = ((0 : ℝ) : WithTop ℝ) := by
        simp [ScaledConjugate, g0, hp, PosScalarMul]
      rw [hs, hg]
      show ((0 : ℝ) : EReal) - ((0 : ℝ) : EReal) ≤ 0
      simp
    · have hg : ScaledConjugate g0 1 p = ⊤ := by
        simp [ScaledConjugate, g0, hp, PosScalarMul]
      rw [hg]
      show _ - (⊤ : EReal) ≤ 0
      simp
  · refine le_sSup ⟨fun _ => 0, ?_⟩
    have hg : ScaledConjugate g0 1 (fun _ => 0) = ((0 : ℝ) : WithTop ℝ) := by
      simp [ScaledConjugate, g0, PosScalarMul]
    rw [hg]
    show (0 : EReal) = ((∑ i : Unit, ((0 : ℤ) : ℝ) * x i : ℝ) : EReal) - ((0 : ℝ) : EReal)
    simp

theorem conj (x : Unit → ℝ) : ConjugateScaling g0 1 x = ((0 : ℝ) : WithTop ℝ) := by
  unfold ConjugateScaling
  rw [conjE]
  rfl

theorem not_exc : ¬ MExchangeAxiomR (ConjugateScaling g0 1) := by
  intro h
  have hd : ∀ x : Unit → ℝ, x ∈ DomR (ConjugateScaling g0 1) := by
    intro x; show ConjugateScaling g0 1 x ≠ ⊤; rw [conj]; exact WithTop.coe_ne_top
  obtain ⟨v, hv, -⟩ := h (fun _ => 1) (hd _) (fun _ => 0) (hd _) ()
    (by simp [SuppPosR])
  simp [SuppNegR] at hv
  norm_num at hv

end ScalingCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) (hg : LNaturalConvex g)
    (alpha : ℤ) (halpha : 0 < alpha) (hprop : ∀ x, ConjugateScalingE g alpha x ≠ ⊥),
    MExchangeAxiomR (ConjugateScaling g alpha) ∧
      LNaturalConvex (ScaledConjugate g alpha) ∧
      ConjugateScaling g alpha = ConjugateFromZ (ScaledConjugate g alpha)) := by
  intro h
  refine ScalingCex.not_exc (h ScalingCex.g0 ScalingCex.g0_lnat 1 one_pos ?_).1
  intro x
  rw [ScalingCex.conjE]
  exact EReal.zero_ne_bot

#print axioms solution
