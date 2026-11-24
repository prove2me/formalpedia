-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.one_le_zetaMul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:31.473488+00:00
-- url     : https://prove2.me/submissions/af967fbf-b110-4b6e-adb4-50c3e362d03f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_one_le_zetaMul_prime_pow_even

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
open scoped ComplexOrder
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (k : ℕ)
    (hk : k ≠ 0) : 1 ≤ DirichletCharacter.zetaMul χ (k ^ 2) := by
  rw [χ.isMultiplicative_zetaMul.multiplicative_factorization _ (pow_ne_zero 2 hk)]
  unfold Finsupp.prod
  calc (1 : ℂ) = ∏ _p ∈ (k ^ 2).factorization.support, (1 : ℂ) := by simp
    _ ≤ _ := by
      refine Finset.prod_le_prod (fun _ _ => zero_le_one) (fun p hp => ?_)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
      rw [Nat.factorization_pow]
      simpa using one_le_zetaMul_prime_pow_even hχ hpp (k.factorization p)
end Formalism.HermitianLattices.Ext.SupplyAP
