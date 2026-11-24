-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.map_mulLeft_den_span_image_eq_map_num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:51:52.49485+00:00
-- url     : https://prove2.me/submissions/fae3d298-a0c8-4b63-9f61-8a5709c8546c

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_MapMulLeftDenSpanImageEqMapNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
private lemma algebraMap_ringOfIntegers_tower {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (x : 𝓞 E) : algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) x) = algebraMap E F (algebraMap (𝓞 E) E x) := rfl
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 F) ((algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E) : 𝓞 F) : F))
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) =
      Submodule.map (Algebra.linearMap (𝓞 F) F) (J.num.map (algebraMap (𝓞 E) (𝓞 F))) := by
  have hden := FractionalIdeal.den_mul_self_eq_num J
  rw [Submodule.map_span, Ideal.map, Ideal.span, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have h1 : J.den • j ∈ J.den • (J : Submodule (𝓞 E) E) :=
      Submodule.smul_mem_pointwise_smul j _ _ hj
    rw [hden] at h1
    obtain ⟨n, hn, hnj⟩ := Submodule.mem_map.mp h1
    refine ⟨algebraMap (𝓞 E) (𝓞 F) n, ⟨n, hn, rfl⟩, ?_⟩
    show algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) n) =
      algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E)) * algebraMap E F j
    rw [algebraMap_ringOfIntegers_tower, algebraMap_ringOfIntegers_tower, ← map_mul]
    congr 1
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    have h1 : algebraMap (𝓞 E) E n ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J.num :=
      Submodule.mem_map_of_mem hn
    rw [← hden] at h1
    obtain ⟨j, hj, hjn⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    refine ⟨algebraMap E F j, ⟨j, hj, rfl⟩, ?_⟩
    show algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E)) * algebraMap E F j =
      algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) n)
    rw [algebraMap_ringOfIntegers_tower, algebraMap_ringOfIntegers_tower, ← map_mul, ← Algebra.smul_def]
    exact congrArg (algebraMap E F) hjn
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
