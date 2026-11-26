-- Prove2me | solution 1 for FixedNumerator.QuarticData.g_eq_conj_chi_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:20.172904+00:00
-- url     : https://prove2.me/submissions/52956fb0-7e52-499f-b67e-4e03d81c3a16

module
public import Definitions.Def_FixedNumerator_Primary
public import Definitions.Def_FixedNumerator_Local

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (ν : GaussianInt) {c : GaussianInt} (hc : IsPrimary c)
    (hcop : IsCoprime ν c) : D.g ν c = starRingEnd ℂ (D.χ ν c) * D.g 1 c := by
  simpa using D.g_twist ν 1 c hc hcop
end FixedNumerator.QuarticData
