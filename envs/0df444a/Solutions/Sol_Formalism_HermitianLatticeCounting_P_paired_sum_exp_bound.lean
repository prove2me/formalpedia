-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.paired_sum_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:13.663768+00:00
-- url     : https://prove2.me/submissions/3a7f2e32-f17a-4536-bfad-6b36fdaf5698

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (I I' : Finset ι) (J : Finset κ) (N : ι → ℝ)
    (D t : κ → ℝ) (φ : ι → κ) (B : ℝ) (c : ℕ) (hsub : I' ⊆ I) (hφ : ∀ i ∈ I', φ i ∈ J)
    (hinj : Set.InjOn φ (I' : Set ι)) (hN : ∀ i ∈ I, 0 ≤ N i)
    (hp : ∀ i ∈ I', N i ≤ Real.exp (t (φ i)) * D (φ i)) (hB : ∀ i ∈ I \ I', N i ≤ B)
    (hB1 : 1 ≤ B) (hc : (I \ I').card ≤ c) (hD : ∀ a ∈ J, 1 ≤ D a) (ht : ∀ a ∈ J, 0 ≤ t a) :
    ∏ i ∈ I, N i ≤ B ^ c * Real.exp (∑ a ∈ J, t a) * ∏ a ∈ J, D a := by
  have e1 : ∏ i ∈ I, N i = (∏ i ∈ I \ I', N i) * ∏ i ∈ I', N i := (Finset.prod_sdiff hsub).symm
  have e2 : ∏ i ∈ I \ I', N i ≤ B ^ c := by
    calc ∏ i ∈ I \ I', N i ≤ ∏ _i ∈ I \ I', B :=
          Finset.prod_le_prod (fun i hi => hN i (Finset.sdiff_subset hi)) hB
      _ = B ^ (I \ I').card := by rw [Finset.prod_const]
      _ ≤ B ^ c := pow_le_pow_right₀ hB1 hc
  have h1 : ∀ a ∈ J, 1 ≤ Real.exp (t a) * D a := fun a ha =>
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (ht a ha)) (hD a ha)
  have him : I'.image φ ⊆ J := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hφ i hi
  have e3 : ∏ i ∈ I', N i ≤ ∏ a ∈ J, (Real.exp (t a) * D a) := by
    calc ∏ i ∈ I', N i ≤ ∏ i ∈ I', (Real.exp (t (φ i)) * D (φ i)) :=
          Finset.prod_le_prod (fun i hi => hN i (hsub hi)) hp
      _ = ∏ a ∈ I'.image φ, (Real.exp (t a) * D a) := (Finset.prod_image (f := fun a => Real.exp (t a) * D a) hinj).symm
      _ ≤ ∏ a ∈ J, (Real.exp (t a) * D a) :=
          Finset.prod_le_prod_of_subset_of_one_le him
            (fun a ha => le_trans zero_le_one (h1 a (him ha))) (fun a ha _ => h1 a ha)
  have e4 : ∏ a ∈ J, (Real.exp (t a) * D a) = Real.exp (∑ a ∈ J, t a) * ∏ a ∈ J, D a := by
    rw [Finset.prod_mul_distrib, Real.exp_sum]
  rw [e1, mul_assoc, ← e4]
  exact mul_le_mul e2 e3 (Finset.prod_nonneg fun i hi => hN i (hsub hi)) (by positivity)
end Formalism.HermitianLatticeCounting.P
