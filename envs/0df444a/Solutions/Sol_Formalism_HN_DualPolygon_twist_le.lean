-- Prove2me | solution 1 for Formalism.HN.DualPolygon.twist_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:05.712848+00:00
-- url     : https://prove2.me/submissions/0ffb42e4-19d0-4dba-abe7-b8ca45d11c40

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_DualPolygon_twist_span_smul
import Theorems.Thm_Formalism_HN_DualPolygon_twist_prime_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
attribute [local instance] Ideal.Quotient.field
variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) : ∀ (X : Submodule (𝓞 K) W), X.FG →
    (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup ≤
      Ideal.absNorm 𝔟 ^ finrank K (Submodule.span K (X : Set W)) := by
  revert h𝔟
  refine UniqueFactorizationMonoid.induction_on_prime 𝔟 ?_ ?_ ?_
  · intro h
    exact absurd Submodule.zero_eq_bot h
  · intro x hx _ X _
    rw [Ideal.isUnit_iff.1 hx, Submodule.top_smul, Ideal.absNorm_top, one_pow,
      AddSubgroup.relIndex_self]
  · intro a p ha hp ih _ X hX
    have hpb : p ≠ ⊥ := hp.ne_zero
    have hab : a ≠ ⊥ := ha
    haveI : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpb
    rw [Submodule.mul_smul, ← AddSubgroup.relIndex_mul_relIndex (p • a • X).toAddSubgroup
      (a • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)]
    have h1 := twist_prime_le (a • X) (Submodule.FG.smul (IsNoetherian.noetherian a) hX) p hpb
    rw [twist_span_smul X a hab] at h1
    have h2 := ih hab X hX
    rw [map_mul, mul_pow]
    exact Nat.mul_le_mul h1 h2
end Formalism.HN.DualPolygon
