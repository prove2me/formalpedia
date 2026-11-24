-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_asAlgebraHom_eq_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:50.273157+00:00
-- url     : https://prove2.me/submissions/c62bb61b-6cc4-44ea-912d-006a6b648641

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_eq_of_span
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exists_lift
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_asModule
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_bc_of
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_span_of

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
theorem _root_.solution [FiniteDimensional k V] [FiniteDimensional k W]
    (K : Type) [Field K] [Algebra k K] [IsAlgClosed K]
    (ρ : Representation k G V) (τ : Representation k G W)
    (h : ∀ g, (ρ g).charpoly = (τ g).charpoly) (x : MonoidAlgebra k G) :
    (ρ.asAlgebraHom x).charpoly = (τ.asAlgebraHom x).charpoly := by
  obtain ⟨y, hy1, hy2⟩ := exists_lift K ρ τ x
  have key := cp_eq_of_span (K := K) (A := MonoidAlgebra K G)
    _ (span_of K) (bc K ρ).asModule (bc K τ).asModule (by
      rintro _ ⟨g, rfl⟩
      rw [cp_bc_of, cp_bc_of, h g])
  have h2 := congrFun key y
  rw [cp_asModule, cp_asModule, hy1, hy2, LinearMap.charpoly_baseChange,
    LinearMap.charpoly_baseChange] at h2
  exact Polynomial.map_injective _ (algebraMap k K).injective h2
end Formalism.IrreducibleCountingLemmas.Z.BN
