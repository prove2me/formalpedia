-- Prove2me | solution 1 for CohnElkies.complexWallisLogPrimitive_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/51e9faf0-774c-43c3-adfb-e27bcc844d92

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexWallisTranslatedSegment_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {z : ℂ} (hz : 0 < z.re)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ =>
        (z + (r : ℂ)) * Complex.log (z + (r : ℂ)) -
          (z + (r : ℂ)))
      (Complex.log (z + (s : ℂ))) s := by
  have hline := complexWallisTranslatedSegment_hasDerivAt z s
  have hpositive : 0 < (z + (s : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hs.1]
  have hslit : z + (s : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hpositive)
  have hnonzero : z + (s : ℂ) ≠ 0 :=
    Complex.slitPlane_ne_zero hslit
  have hlog := hline.clog_real hslit
  convert! (hline.mul hlog).sub hline using 1
  simp [div_eq_mul_inv, hnonzero]
end CohnElkies
