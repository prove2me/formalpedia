-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.op_minor_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:43.183331+00:00
-- url     : https://prove2.me/submissions/e385e2be-9b8d-455f-a082-ee2da96ac7fb

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_minor_mem
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mono
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {d N0 N1 p : ℕ} (s : ZMod d) (A : Fin p → Fin N0 → K)
    (I : Fin p → Fin N1) (mono : ZV d N0 N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (s, j, I r') : MvPolynomial (ZV d N0 N1) K)).det.support) :
    ∃ τ : Fin p → Fin N0, Function.Injective τ ∧
      (∃ π : Equiv.Perm (Fin p), ∀ i, A (π i) (τ i) ≠ 0) ∧
      mono = ∑ i, Finsupp.single ((s, τ i, I i) : ZV d N0 N1) 1 := by
  classical
  have hinj : Function.Injective (fun y : Fin N0 × Fin N1 => ((s, y.1, y.2) : ZV d N0 N1)) := by
    intro a b h
    simpa [Prod.ext_iff] using h
  have hdet : (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (s, j, I r') : MvPolynomial (ZV d N0 N1) K)).det =
      rename (fun y : Fin N0 × Fin N1 => ((s, y.1, y.2) : ZV d N0 N1))
        (Matrix.of fun (r r' : Fin p) =>
          (∑ j, C (A r j) * X (j, I r') : MvPolynomial (Fin N0 × Fin N1) K)).det := by
    rw [AlgHom.map_det]
    congr 1
    refine Matrix.ext fun r r' => ?_
    simp [AlgHom.mapMatrix_apply, Matrix.map_apply]
  rw [hdet, support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m, hm, rfl⟩ := hm
  obtain ⟨τ, hτ, hπ, rfl⟩ := shape_minor_mem A I m hm
  refine ⟨τ, hτ, hπ, ?_⟩
  rw [Finsupp.mapDomain_finsetSum]
  simp [Finsupp.mapDomain_single]
end Formalism.DworkPowerSeriesWeights
