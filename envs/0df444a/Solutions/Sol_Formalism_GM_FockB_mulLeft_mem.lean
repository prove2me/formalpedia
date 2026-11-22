-- Prove2me | solution 1 for Formalism.GM.FockB.mulLeft_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:45.225654+00:00
-- url     : https://prove2.me/submissions/7273060a-2e4b-4a49-b281-4a9b24726f3a

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.FockB
theorem _root_.solution {S : Set σ} {f : MvPolynomial σ k} (hf : f ∈ Algebra.adjoin k (X '' S)) :
    LinearMap.mulLeft k f ∈ Ops S := by
  have e1 : LinearMap.mulLeft k f = Algebra.lmul k (MvPolynomial σ k) f := by
    refine LinearMap.ext fun g => ?_
    simp
  rw [e1]
  have h2 : Algebra.lmul k (MvPolynomial σ k) f ∈ (Algebra.adjoin k (X '' S)).map (Algebra.lmul k _) :=
    Subalgebra.mem_map.mpr ⟨f, hf, rfl⟩
  rw [AlgHom.map_adjoin] at h2
  refine Algebra.adjoin_mono ?_ h2
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨u, hu, Or.inl ?_⟩
  refine LinearMap.ext fun g => ?_
  simp
end Formalism.GM.FockB
