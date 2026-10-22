-- Prove2me | solution 1 for DualityStability.StrongDuality.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:34:14.353962+00:00
-- url     : https://prove2.me/submissions/9aa0dd9e-4bc6-4be3-b6bc-ed2b7e52b414

import Mathlib
import Definitions.Def_DualityStability_StrongDuality_Program

set_option autoImplicit false
open DualityStability.StrongDuality

lemma HH_ereal (a b G F : EReal) (c : ℝ) (ha : a ≠ ⊥) (hb : b ≠ ⊤) (hG : G ≤ (c : EReal) - b)
    (hF : (c : EReal) - a ≤ F) : G - F ≤ a - b := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top =>
    induction b using EReal.rec with
    | bot => simp
    | top => exact absurd rfl hb
    | coe β => simp
  | coe α =>
    induction b using EReal.rec with
    | bot => simp
    | top => exact absurd rfl hb
    | coe β =>
      induction F using EReal.rec with
      | bot =>
        exfalso
        have h := le_bot_iff.mp hF
        rw [← EReal.coe_sub] at h
        exact EReal.coe_ne_bot _ h
      | top => simp
      | coe φ =>
        induction G using EReal.rec with
        | bot => simp
        | top =>
          exfalso
          have h := top_le_iff.mp hG
          rw [← EReal.coe_sub] at h
          exact EReal.coe_ne_top _ h
        | coe γ =>
          have h1 : γ ≤ c - β := by exact_mod_cast hG
          have h2 : c - α ≤ φ := by exact_mod_cast hF
          have : γ - φ ≤ α - β := by linarith
          exact_mod_cast this

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

theorem solution (p : Program E E' F F') : p.dualValue ≤ p.h 0 := by
  unfold Program.dualValue Program.h
  refine iSup_le (fun y' => le_iInf (fun x => ?_))
  have hG : p.gstar y' ≤ ((p.fPair.pair (p.A x) y' : ℝ) : EReal) - p.g (p.A x) := by
    unfold Program.gstar
    exact iInf_le (fun y => ((p.fPair.pair y y' : ℝ) : EReal) - p.g y) (p.A x)
  have hF : ((p.fPair.pair (p.A x) y' : ℝ) : EReal) - p.f x ≤ p.fstar (p.Astar y') := by
    unfold Program.fstar
    have := le_iSup (fun x' => ((p.ePair.pair x' (p.Astar y') : ℝ) : EReal) - p.f x') x
    rwa [← p.adjoint x y'] at this
  unfold Program.dualAt Program.primalAt
  rw [sub_zero]
  exact HH_ereal _ _ _ _ _ (p.f_no_neg_inf x) (p.g_no_pos_inf _) hG hF
