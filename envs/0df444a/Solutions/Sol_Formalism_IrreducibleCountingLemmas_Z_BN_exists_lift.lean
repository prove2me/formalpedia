-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:40.977893+00:00
-- url     : https://prove2.me/submissions/b50a95ac-9840-4d8b-a65b-7c6fcbe99188

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
open TensorProduct
variable {k G V W : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution (K : Type) [Field K] [Algebra k K] (ρ : Representation k G V)
    (τ : Representation k G W) (x : MonoidAlgebra k G) :
    ∃ y : MonoidAlgebra K G, (bc K ρ).asAlgebraHom y = (ρ.asAlgebraHom x).baseChange K ∧
      (bc K τ).asAlgebraHom y = (τ.asAlgebraHom x).baseChange K := by
  induction x using MonoidAlgebra.induction_on with
  | of g => exact ⟨MonoidAlgebra.of K G g, by simp [bc], by simp [bc]⟩
  | add x y hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', by simp [h1, h3, LinearMap.baseChange_add],
      by simp [h2, h4, LinearMap.baseChange_add]⟩
  | smul r x hx =>
    obtain ⟨x', h1, h2⟩ := hx
    exact ⟨algebraMap k K r • x', by rw [map_smul (bc K ρ).asAlgebraHom, h1, map_smul ρ.asAlgebraHom, LinearMap.baseChange_smul,
        algebraMap_smul],
      by rw [map_smul (bc K τ).asAlgebraHom, h2, map_smul τ.asAlgebraHom, LinearMap.baseChange_smul,
        algebraMap_smul]⟩
end Formalism.IrreducibleCountingLemmas.Z.BN
