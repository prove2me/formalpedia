-- Prove2me | solution 1 for Formalism.L2.DIV.range_V0E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:19:24.859008+00:00
-- url     : https://prove2.me/submissions/dcc5536b-4dec-4e3e-ab7d-f681e830354b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_image_idempotent_spec
import Theorems.Thm_Formalism_L2_DIV_group_action_matrix_hom
import Theorems.Thm_Formalism_L2_DIV_level_part_spec
import Theorems.Thm_Formalism_L2_DIV_lvlIdem_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G]
    [Fintype G] (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
    (hidem : idemOf X * idemOf X = idemOf X)
    (hcomm : lvlIdem P ψ * idemOf X = idemOf X * lvlIdem P ψ) :
    LinearMap.range (S.V0E r X P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (idemOf X)).mulVecLin ⊓ S.lvlPart r P ψ := by
  have hE := (group_action_matrix_hom K S G r).2
  unfold CSD.V0E CSD.cutE
  rw [(image_idempotent_spec K S.dim (S.gaMat r (goodAt X P ψ))).2]
  unfold goodAt
  rw [hE, ← level_part_spec K S G r P ψ]
  have hEE : S.gaMat r (idemOf X) * S.gaMat r (idemOf X) = S.gaMat r (idemOf X) := by
    rw [← hE, hidem]
  have hFF : S.gaMat r (lvlIdem P ψ) * S.gaMat r (lvlIdem P ψ) = S.gaMat r (lvlIdem P ψ) := by
    rw [← hE, lvlIdem_idem]
  have hEF : S.gaMat r (lvlIdem P ψ) * S.gaMat r (idemOf X) = S.gaMat r (idemOf X) * S.gaMat r (lvlIdem P ψ) := by
    rw [← hE, ← hE, hcomm]
  ext y
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(S.gaMat r (lvlIdem P ψ)).mulVec x, by rw [Matrix.mulVec_mulVec]⟩,
      ⟨(S.gaMat r (idemOf X)).mulVec x, by rw [Matrix.mulVec_mulVec, hEF]⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨y, ?_⟩
    have hy1 : (S.gaMat r (idemOf X)).mulVec y = y := by rw [← ha, Matrix.mulVec_mulVec, hEE]
    have hy2 : (S.gaMat r (lvlIdem P ψ)).mulVec y = y := by rw [← hb, Matrix.mulVec_mulVec, hFF]
    rw [← Matrix.mulVec_mulVec, hy2, hy1]
end Formalism.L2.DIV
