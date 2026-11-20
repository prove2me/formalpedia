-- Prove2me | solution 1 for DeletionCode.SpectrumPath.equal_spectrum_eq_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:53.783018+00:00
-- url     : https://prove2.me/submissions/16084b72-1463-487c-b84f-711541cb43bf

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
import Theorems.Thm_DeletionCode_SpectrumPath_equal_spectrum_recovers_word

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word z : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1))
    (hspectrum : wordSpectrum z n L = wordSpectrum word n L) :
    (fun i : Fin n => z i.val) = (fun i : Fin n => word i.val) := by
  funext i
  simpa only [Nat.zero_add] using
    equal_spectrum_recovers_word word z n L hL hn hunique hspectrum i.val i.isLt
end DeletionCode.SpectrumPath
