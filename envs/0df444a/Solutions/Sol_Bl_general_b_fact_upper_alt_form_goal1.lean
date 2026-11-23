-- Prove2me | solution 1 for Bl.general_b_fact_upper_alt_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:52.925856+00:00
-- url     : https://prove2.me/submissions/411001a6-4f24-4415-9cb8-8812a2c16466

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpperAltForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper_alt_form
namespace Bl.general_b_fact_upper_alt_form
theorem _root_.solution :
  ∀ {K : Type} [inst : Field.{0} K] {n k : Type} [Fintype.{0} n] [DecidableEq.{1} n] [inst_3 : Fintype.{0} k]
  [DecidableEq.{1} k] (f : RingHom.{0, 0} K Complex) (A : Matrix.{0, 0, 0} n k K),
  Function.Injective.{1, 1} (Matrix.mulVec.{0, 0, 0} A) →
    Function.Injective.{1, 1} (Matrix.mulVec.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} A (DFunLike.coe.{1, 1, 1} f))) := by
  intro K _ n k _ _ _ _ f A hA
  have hker : LinearMap.ker (Matrix.toLin' A) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun x y hxy => hA (by simpa only [Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective hker
  have hBA : LinearMap.toMatrix' g * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
  have h1 : (LinearMap.toMatrix' g).map f * A.map f = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ f.map_zero f.map_one]
  intro v w hvw
  have h2 := congrArg (fun u => Matrix.mulVec ((LinearMap.toMatrix' g).map f) u) hvw
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using h2
end Bl.general_b_fact_upper_alt_form
