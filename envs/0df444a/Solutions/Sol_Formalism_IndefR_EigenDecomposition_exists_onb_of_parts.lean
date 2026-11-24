-- Prove2me | solution 1 for Formalism.IndefR.EigenDecomposition.exists_onb_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:15.752187+00:00
-- url     : https://prove2.me/submissions/da1d32ba-6443-42e2-9c71-e7d28f4e1c25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_EigenDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Formalism Formalism.IndefR Formalism.IndefR.EigenDecomposition
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace Formalism.IndefR.EigenDecomposition
theorem _root_.solution {I : Type*} [Finite I] (P : I → Submodule ℂ H)
    (horth : ∀ i j, i ≠ j → P i ⟂ P j) (htop : ⨆ i, P i = ⊤) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H) (lab : Fin n → I), ∀ k, b k ∈ P (lab k) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have hV : OrthogonalFamily ℂ (fun i => P i) (fun i => (P i).subtypeₗᵢ) :=
    fun i j hij v w => (horth i j hij).inner_eq v.2 w.2
  have hint : DirectSum.IsInternal (fun i => P i) := by
    rw [hV.isInternal_iff, htop, Submodule.top_orthogonal_eq_bot]
  let b := hint.collectedOrthonormalBasis hV (fun i => stdOrthonormalBasis ℂ (P i))
  let e := Fintype.equivFin (Σ i, Fin (Module.finrank ℂ (P i)))
  refine ⟨_, b.reindex e, fun k => (e.symm k).1, fun k => ?_⟩
  rw [OrthonormalBasis.reindex_apply]
  exact hint.collectedOrthonormalBasis_mem hV _ _
end Formalism.IndefR.EigenDecomposition
