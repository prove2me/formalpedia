-- Prove2me | solution 1 for Formalism.CountingSumsFrames.divPow_mem_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:09.413824+00:00
-- url     : https://prove2.me/submissions/39683b2b-2aad-48c0-992f-c66e33a94e54

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_divPow_sum_mem
import Theorems.Thm_Formalism_CountingSumsFrames_diagMul_commute
import Theorems.Thm_Formalism_CountingSumsFrames_diagLaplacian_commute
import Theorems.Thm_Formalism_CountingSumsFrames_pairingDivPow_eq
import Theorems.Thm_Formalism_CountingSumsFrames_laplacianDivPow_eq

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
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (L : Set (PolXY K k)) (hadd : ∀ f g, f ∈ L → g ∈ L → f + g ∈ L) (h0 : (0 : PolXY K k) ∈ L)
    (he : ∀ (i : Fin k) (n : ℕ) (f : PolXY K k), f ∈ L → (((n.factorial : K)⁻¹) • h3e K i ^ n) f ∈ L)
    (hd : ∀ (i : Fin k) (n : ℕ) (f : PolXY K k), f ∈ L → (((n.factorial : K)⁻¹) • h3d K i ^ n) f ∈ L)
    (l : ℕ) (f : PolXY K k) (hf : f ∈ L) : hDiv K k l f ∈ L ∧ ctrDiv K k l f ∈ L := by
  constructor
  · rw [pairingDivPow_eq]
    exact divPow_sum_mem (K := K) (stabilizerSubsemiring (K := K) L hadd h0) univ (fun i => h3e K i) diagMul_commute
      (fun i n => he i n) l f hf
  · rw [laplacianDivPow_eq]
    exact divPow_sum_mem (K := K) (stabilizerSubsemiring (K := K) L hadd h0) univ (fun i => h3d K i) diagLaplacian_commute
      (fun i n => hd i n) l f hf
end Formalism.CountingSumsFrames
