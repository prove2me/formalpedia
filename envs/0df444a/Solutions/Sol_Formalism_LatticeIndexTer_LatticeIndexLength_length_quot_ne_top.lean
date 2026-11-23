-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexLength.length_quot_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:25.436187+00:00
-- url     : https://prove2.me/submissions/38dc27d2-c7d3-47fa-9f4a-81285a1f78be

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open Formalism.LatticeIndexTer.LatticeIndexLength
namespace Formalism.LatticeIndexTer.LatticeIndexLength
theorem _root_.solution {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M]
    (d : O) (hd : d ≠ 0) (N : Submodule O M) (hN : ∀ m : M, d • m ∈ N) :
    Module.length O (M ⧸ N) ≠ ⊤ := by
  let I : Ideal O := Ideal.span {d}
  have hle : I • (⊤ : Submodule O M) ≤ N := by
    rw [Submodule.smul_le]
    intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact N.smul_mem _ (hN m)
  refine ne_top_of_le_ne_top ?_
    (Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle))
  have h1 : IsFiniteLength O (O ⧸ I) :=
    isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hd)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h1
  obtain ⟨_, h1a⟩ := h1
  have : IsArtinianRing (O ⧸ I) := isArtinian_of_tower O h1a
  have : Module.Finite (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M)) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M))
  have : IsArtinian (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M)) := inferInstance
  have : IsArtinian O (M ⧸ I • (⊤ : Submodule O M)) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top
end Formalism.LatticeIndexTer.LatticeIndexLength
