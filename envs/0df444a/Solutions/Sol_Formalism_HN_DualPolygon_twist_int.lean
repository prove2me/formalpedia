-- Prove2me | solution 1 for Formalism.HN.DualPolygon.twist_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:23.694819+00:00
-- url     : https://prove2.me/submissions/0af896b7-befc-4d4a-adff-546619d3a90e

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
open scoped Pointwise
variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (X : Submodule (𝓞 K) W) (hX : X.FG) (m : ℕ) (hm : m ≠ 0) :
    ((Ideal.span {(m : 𝓞 K)}) • X).toAddSubgroup.relIndex X.toAddSubgroup =
      m ^ finrank ℤ X := by
  have htf := twist_torsionFree (K := K) (W := W)
  have : Module.Finite (𝓞 K) X := Module.Finite.iff_fg.mpr hX
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 K) X
  rw [Submodule.ideal_span_singleton_smul]
  set H := ((m : 𝓞 K) • X).toAddSubgroup.addSubgroupOf X.toAddSubgroup with hH
  have hcoe : ∀ x : X, ((m • x : X) : W) = (m : 𝓞 K) • (x : W) := by
    intro x
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul (𝓞 K)]
  have hmem : ∀ x : X, m • x ∈ H.toIntSubmodule := by
    intro x
    show m • x ∈ H
    rw [hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, hcoe]
    exact Submodule.smul_mem_pointwise_smul _ _ _ x.2
  let f : X →+ H.toIntSubmodule :=
    { toFun := fun x => ⟨m • x, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : ((m • x : X) : W) = ((m • y : X) : W) := by
        have := congrArg (fun z : H.toIntSubmodule => ((z : X) : W)) hxy
        simpa [f] using this
      rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower] at h1
      exact Subtype.ext (htf.nsmul_right_injective hm h1)
    · rintro ⟨z, hz⟩
      have hz' : (z : W) ∈ (m : 𝓞 K) • X := by
        have : z ∈ H := hz
        rwa [hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup] at this
      obtain ⟨x, hx, hxz⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hz'
      refine ⟨⟨x, hx⟩, ?_⟩
      ext
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hcoe]
      exact hxz
  let e := AddEquiv.ofBijective f hf
  have key := Submodule.natAbs_det_equiv H.toIntSubmodule e
  have hlin : H.toIntSubmodule.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : X →+ H.toIntSubmodule) =
      (m : ℤ) • LinearMap.id := by
    ext x
    simp [e, f]
  rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one] at key
  change H.index = _
  rw [Int.natAbs_pow, Int.natAbs_natCast] at key
  exact key.symm
end Formalism.HN.DualPolygon
