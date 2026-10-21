-- Prove2me | solution 1 for FiniteFields.Dwork.exists_natCast_approx
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:43:11.575042+00:00
-- url     : https://prove2.me/submissions/a0dd2ed1-e72f-4d39-b197-b40b2d2b8ae5

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter
open PowerSeries IsUltrametricDist
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2TraceLimitResiduePrimeAlgebra
omit [Finite k]
theorem solution (σ : CoefficientRing (ZMod p) p) (M : ℕ) :
    ∃ N : ℕ, ∃ c : CoefficientRing k p,
      wittPrimeFieldMap k p σ - (N : CoefficientRing k p)
        = (p : CoefficientRing k p) ^ M * c := by
  obtain ⟨c₀, hc₀⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec M (WittVector.equiv p σ))
  refine ⟨(WittVector.equiv p σ).appr M, wittPrimeFieldMap k p ((WittVector.equiv p).symm c₀), ?_⟩
  have hZ : σ - (((WittVector.equiv p σ).appr M : ℕ) : CoefficientRing (ZMod p) p)
      = (p : CoefficientRing (ZMod p) p) ^ M * (WittVector.equiv p).symm c₀ := by
    apply (WittVector.equiv p).injective
    rw [map_sub, map_mul, map_pow, RingEquiv.apply_symm_apply, map_natCast, map_natCast]
    exact hc₀
  have hmap := congrArg (wittPrimeFieldMap k p) hZ
  rwa [map_sub, map_natCast, map_mul, map_pow, map_natCast] at hmap
