-- Prove2me | solution 1 for Formalism.HN.DualPolygon.twist_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:27.595071+00:00
-- url     : https://prove2.me/submissions/006c90a9-f242-44fc-a080-d56849b41450

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
import Theorems.Thm_Formalism_HN_DualPolygon_twist_le
import Theorems.Thm_Formalism_HN_DualPolygon_twist_finrank_int
import Theorems.Thm_Formalism_HN_DualPolygon_twist_int
import Theorems.Thm_Formalism_HN_DualPolygon_twist_absNorm_nat

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
theorem _root_.solution {K W : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W] (X : Submodule (𝓞 K) W) (hX : X.FG) (𝔟 : Ideal (𝓞 K))
    (h𝔟 : 𝔟 ≠ ⊥) :
    (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup =
      Ideal.absNorm 𝔟 ^ finrank K (Submodule.span K (X : Set W)) := by
  set m := Ideal.absNorm 𝔟 with hmdef
  have hm : m ≠ 0 := fun h => h𝔟 (Ideal.absNorm_eq_zero_iff.1 h)
  have hmem : (m : 𝓞 K) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {(m : 𝓞 K)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have hspan0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  have h𝔠0 : 𝔠 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h𝔠
    exact hspan0 h𝔠
  set r := finrank K (Submodule.span K (X : Set W)) with hr
  have hall := twist_int X hX m hm
  rw [twist_finrank_int X hX, h𝔠, mul_comm, Submodule.mul_smul,
    ← AddSubgroup.relIndex_mul_relIndex (𝔠 • 𝔟 • X).toAddSubgroup
      (𝔟 • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)] at hall
  have ha := twist_le 𝔟 h𝔟 X hX
  have hb := twist_le 𝔠 h𝔠0 (𝔟 • X) (Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hX)
  rw [twist_span_smul X 𝔟 h𝔟] at hb
  have hnorm : Ideal.absNorm 𝔠 * m = m ^ finrank ℚ K := by
    rw [hmdef, ← map_mul, mul_comm, ← h𝔠, twist_absNorm_nat]
  have hB : 0 < Ideal.absNorm 𝔠 ^ r :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔠0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have htot : Ideal.absNorm 𝔠 ^ r * m ^ r = m ^ (finrank ℚ K * r) := by
    rw [← mul_pow, hnorm, ← pow_mul]
  by_contra hne
  have hlt := lt_of_le_of_ne ha hne
  have h1 : (𝔠 • 𝔟 • X).toAddSubgroup.relIndex (𝔟 • X).toAddSubgroup *
      (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup < Ideal.absNorm 𝔠 ^ r * m ^ r :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hb) (Nat.mul_lt_mul_of_pos_left hlt hB)
  rw [hall, htot] at h1
  exact lt_irrefl _ h1
end Formalism.HN.DualPolygon
