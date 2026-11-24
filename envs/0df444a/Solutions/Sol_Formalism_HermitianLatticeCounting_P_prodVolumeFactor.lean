-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodVolumeFactor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:16.179898+00:00
-- url     : https://prove2.me/submissions/761bcc42-a8f3-4964-aab3-97f1ba79412f

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : NProduct := by
  intro ι _ k r G vt T g v hk hT hg hvt hprod
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nv
  rw [Finset.prod_pow]
  have e : ∏ w, (Real.exp 1 * Real.pi * G w * g⁻¹ ^ (2 * r + 2) / (T * k * vt w)) =
      (Real.exp 1 * Real.pi * g⁻¹ ^ (2 * r + 2) / (T * k)) ^ Fintype.card ι * (∏ w, G w) /
        ∏ w, vt w := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro w _
    ring
  rw [e, hprod, mul_comm k (Fintype.card ι), pow_mul, ← mul_pow]
  congr 1
  ring
end Formalism.HermitianLatticeCounting.P
