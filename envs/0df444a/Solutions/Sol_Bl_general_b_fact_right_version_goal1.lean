-- Prove2me | solution 1 for Bl.general_b_fact_right_version.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:13.523746+00:00
-- url     : https://prove2.me/submissions/7eb5cf50-607c-49e6-b18b-3fe9d2f45a84

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_version
namespace Bl.general_b_fact_right_version
theorem _root_.solution :
  ∀ {E Ω : Type} [inst : Field.{0} E] [inst_1 : Field.{0} Ω] [inst_2 : Algebra.{0, 0} E Ω] (σ : AlgEquiv.{0, 0, 0} E Ω Ω)
  (y : Ω),
  IsIntegral.{0, 0} E y →
    Exists.{1} fun (n : Nat) ↦ And (Ne.{1} n 0) (Eq.{1} (DFunLike.coe.{1, 1, 1} (HPow.hPow.{0, 0, 0} σ n) y) y) := by
  intro E Ω _ _ _ σ y hy
  have hmem : ∀ k : ℕ, (σ ^ k) y ∈ (minpoly E y).rootSet Ω := by
    intro k
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hy, ?_⟩
    have h := Polynomial.aeval_algHom_apply ((σ ^ k : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) y (minpoly E y)
    rw [minpoly.aeval, map_zero] at h
    simpa using h
  obtain ⟨a, b, hab, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun k : ℕ => (σ ^ k) y) hmem (Polynomial.rootSet_finite _ _)
  refine ⟨b - a, by omega, ?_⟩
  have hb : b = a + (b - a) := by omega
  rw [hb, pow_add, AlgEquiv.mul_apply] at he
  exact ((σ ^ a).injective he).symm
end Bl.general_b_fact_right_version
