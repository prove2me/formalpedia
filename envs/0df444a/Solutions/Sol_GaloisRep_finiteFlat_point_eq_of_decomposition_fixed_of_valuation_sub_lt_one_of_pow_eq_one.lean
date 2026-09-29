-- Prove2me | solution 1 for GaloisRep.finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a112f039-ef8e-56d7-b9b4-f7e768534fa9

import Theorems.Thm_GaloisRep_finiteFlat_point_eq_of_forall_kernel_point_eq_one
import Theorems.Thm_GaloisRep_finiteFlat_point_eq_one_of_pow_prime_pow_of_forall_dvr
import Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H]
    [Module.Finite (GaloisRep.ratLocalizedAt ℓ) H] [Module.Flat (GaloisRep.ratLocalizedAt ℓ) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H]
    (k : ℕ) (hord : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ), f ^ ℓ ^ k = 1)
    (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) (hf : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (f h) = f h)) (hg : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (g h) = g h))
    (hfg : ∀ h : H, A.valuation (f h - g h) < 1) :
    f = g :=
  GaloisRep.finiteFlat_point_eq_of_forall_kernel_point_eq_one ℓ A hA H k hord
    (fun φ hφ hφ1 hφk =>
      GaloisRep.finiteFlat_point_eq_one_of_pow_prime_pow_of_forall_dvr ℓ hℓ A hA
        (fun O _ _ _ hu H' _ _ _ _ _ x hx k' hxk =>
          HopfAlgebra.point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal O ℓ hℓ hu H' x hx k' hxk)
        H φ hφ hφ1 k hφk)
    f g hf hg hfg

end S_GaloisRep_finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one
end P2MW
export P2MW.S_GaloisRep_finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one (solution)
