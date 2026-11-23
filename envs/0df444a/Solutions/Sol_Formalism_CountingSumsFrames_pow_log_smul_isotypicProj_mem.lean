-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pow_log_smul_isotypicProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:26.684551+00:00
-- url     : https://prove2.me/submissions/4a6008bd-6012-480b-8578-4403b61aed18

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_pow_log_div_choose_mem
import Theorems.Thm_Formalism_CountingSumsFrames_pow_log_smul_harmonicProj_mem

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
theorem _root_.solution (R : Subring K) (p : ℕ) (hp : p.Prime) (hR : PLocal R p) (M : Set (PolXY K k))
    (h0 : (0 : PolXY K k) ∈ M) (hadd : ∀ f g, f ∈ M → g ∈ M → f + g ∈ M)
    (hs : ∀ r ∈ R, ∀ f ∈ M, r • f ∈ M)
    (hM : ∀ (l : ℕ) (f : PolXY K k), f ∈ M → hDiv K k l f ∈ M ∧ ctrDiv K k l f ∈ M)
    (A B j : ℕ) (hj : j ≤ A) (f : PolXY K k) (hf : f ∈ M) :
    ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ M := by
  have h1 : ((p : K) ^ Nat.log p (A + B + k)) • harProj K k (A - j) (B - j) (ctrDiv K k j f) ∈ M :=
    pow_log_smul_harmonicProj_mem R p hp hR M h0 hadd hs hM (A - j) (B - j) (A + B + k) (by omega) _ (hM j f hf).2
  have h2 := (hM j _ h1).1
  have h3 := hs _ (pow_log_div_choose_mem R p hp hR (A + B + k - 2 * j + j - 1) (A + B + k) j (by omega)) _ h2
  have : ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f =
      ((p : K) ^ Nat.log p (A + B + k) / (((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)) •
        hDiv K k j (((p : K) ^ Nat.log p (A + B + k)) • harProj K k (A - j) (B - j) (ctrDiv K k j f)) := by
    rw [levelProj, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_smul, smul_smul,
      smul_smul]
    congr 1
    rw [two_mul, pow_add]
    ring
  rw [this]
  exact h3
end Formalism.CountingSumsFrames
