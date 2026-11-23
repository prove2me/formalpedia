-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.gauss_dual_of_fock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:35.097808+00:00
-- url     : https://prove2.me/submissions/b7b26473-b85a-40a6-b67f-004b37625a73

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_latOf_iff
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_mem_PolAB
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_dual_to_fock
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_fock_to_dual
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_fockGaussLatticeComparison_holds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_smul_mem_latOf_gauss
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_smul_mem_latOf_dual

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
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {K : Type} [Field K] [CharZero K] {k A B p : ℕ} (R : Subring K) (g : GL (Fin k) K)
    (hk : 1 ≤ k) (hp : p.Prime) (hR : PLocal R p) (T : PolXY K k →ₗ[K] PolXY K k)
    (hT : ∀ f, f ∈ PolAB K k A B → T f ∈ PolAB K k A B) (n : ℕ) (hn : n ≤ 2 * Nat.log p (A + B + k))
    (hF : ∀ f, f ∈ PolAB K k A B → f ∈ latOf g (FockLat R) → ((p : K) ^ n) • T f ∈ latOf g (FockLat R))
    (f : PolXY K k) (hf : f ∈ PolAB K k A B) :
    (f ∈ latOf g (GaussLat R) → ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • T f ∈ latOf g (GaussLat R)) ∧
    (f ∈ latOf g (DualLat R) → ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • T f ∈ latOf g (DualLat R)) := by
  have hAf : (A.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hBf : (B.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hL : ∀ X : ℕ, X ≤ A + B + k →
      (k - 1) * Nat.log p X + n ≤ (k + 1) * Nat.log p (A + B + k) := by
    intro X hX
    have hlX : Nat.log p X ≤ Nat.log p (A + B + k) := Nat.log_mono_right hX
    calc (k - 1) * Nat.log p X + n ≤ (k - 1) * Nat.log p (A + B + k) + 2 * Nat.log p (A + B + k) :=
          add_le_add (Nat.mul_le_mul_left _ hlX) hn
      _ = (k + 1) * Nat.log p (A + B + k) := by rw [← add_mul]; congr 1; omega
  have hpow : ∀ a b : ℕ, a ≤ b → ∀ x : PolXY K k, ((p : K) ^ b) • x = ((p : K) ^ (b - a)) • (((p : K) ^ a) • x) := by
    intro a b hab x
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hab]
  have hpR : ∀ a : ℕ, (p : K) ^ a ∈ R := fun a => R.pow_mem (natCast_mem R p) a
  refine ⟨fun hG => ?_, fun hD => ?_⟩
  · have h1 := (fockGaussLatticeComparison_holds K k A B p R g hk hp hR f hf).2 hG
    have hcf : ((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f ∈ PolAB K k A B :=
      Submodule.smul_mem _ _ hf
    have h2 := hF _ hcf h1
    have hpol : ((p : K) ^ n) • T (((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f) ∈
        PolAB K k A B := Submodule.smul_mem _ _ (hT _ hcf)
    have h3 := (fockGaussLatticeComparison_holds K k A B p R g hk hp hR _ hpol).1 h2
    have e : (A.factorial : K) • (((p : K) ^ n) •
        T (((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f)) =
        ((p : K) ^ ((k - 1) * Nat.log p A + n)) • T f := by
      rw [map_smul, smul_smul, smul_smul]
      congr 1
      field_simp
      ring
    rw [e] at h3
    rw [hpow _ _ (hL A (by omega))]
    exact smul_mem_latOf_gauss R g (hpR _) h3
  · have hf' := glAct_mem_PolAB g⁻¹ f hf
    have h1 : (B.factorial : K) • f ∈ latOf g (FockLat R) := by
      rw [mem_latOf_iff, map_smul]
      exact dual_to_fock R hf' ((mem_latOf_iff g _ f).1 hD)
    have hbf : (B.factorial : K) • f ∈ PolAB K k A B := Submodule.smul_mem _ _ hf
    have h2 := hF _ hbf h1
    have hpol : ((p : K) ^ n) • T ((B.factorial : K) • f) ∈ PolAB K k A B :=
      Submodule.smul_mem _ _ (hT _ hbf)
    have h3 : ((p : K) ^ ((k - 1) * Nat.log p B) * (B.factorial : K)⁻¹) •
        (((p : K) ^ n) • T ((B.factorial : K) • f)) ∈ latOf g (DualLat R) := by
      rw [mem_latOf_iff] at h2 ⊢
      rw [map_smul]
      exact fock_to_dual R hp hR (glAct_mem_PolAB g⁻¹ _ hpol) h2
    have e : ((p : K) ^ ((k - 1) * Nat.log p B) * (B.factorial : K)⁻¹) •
        (((p : K) ^ n) • T ((B.factorial : K) • f)) =
        ((p : K) ^ ((k - 1) * Nat.log p B + n)) • T f := by
      rw [map_smul, smul_smul, smul_smul]
      congr 1
      field_simp
      ring
    rw [e] at h3
    rw [hpow _ _ (hL B (by omega))]
    exact smul_mem_latOf_dual R g (hpR _) h3
end Formalism.CountingSumsFrames.Har4
