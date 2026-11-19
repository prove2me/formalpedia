-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.dynamic_cut_interface
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-11-19T03:56:35.668649+00:00
-- url     : https://prove2.me/submissions/2b8f2712-217e-49e9-ad66-3c1ec6916d84

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_CutProtocol

set_option autoImplicit false
open DecrAlmostLinearSSSP.Decremental
open scoped ENNReal NNReal

theorem solution : ¬ (
    ∀ exponent : ℕ, ∃ (impl : CutImplementation) (K h Γ a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial Γ ∧ Subpolynomial a ∧
      (∀ m, 32 ≤ K m ∧ K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      ∀ m ξ, 0 < ξ → ImplementsCut impl m exponent (K m) (h m) (Γ m)
        (C * m * a m) ξ) := by
  intro h
  obtain ⟨impl,_,_,_,_,_,_⟩ := h 0
  let c : Machine := ⟨0,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0,false,false,0⟩
  exact Fin.elim0 ((impl.view 0 1 c).physical.graph.tail ⟨0,by decide⟩)
