-- Prove2me | solution 1 for Formalism.CountingSumsFrames.divPow_mem_fockLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:27.697524+00:00
-- url     : https://prove2.me/submissions/7d37acef-6fc9-4735-accf-c7e2d0f25d00

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_zero_mem_fockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_add_mem_fockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_diagMul_divPow_mem_fockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_diagLaplacian_divPow_mem_fockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_divPow_mem_of_generators

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
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {K : Type} [Field K] [CharZero K] {k : ℕ} (R : Subring K) (l : ℕ) (f : PolXY K k)
    (hf : f ∈ FockLat R) : hDiv K k l f ∈ FockLat R ∧ ctrDiv K k l f ∈ FockLat R :=
  divPow_mem_of_generators (FockLat R) (add_mem_fockLattice R) (zero_mem_fockLattice R) (diagMul_divPow_mem_fockLattice R) (diagLaplacian_divPow_mem_fockLattice R) l f hf
end Formalism.CountingSumsFrames
