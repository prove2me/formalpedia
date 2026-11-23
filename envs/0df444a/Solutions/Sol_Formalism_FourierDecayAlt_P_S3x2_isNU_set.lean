-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.isNU_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:11.40423+00:00
-- url     : https://prove2.me/submissions/25c180e0-5905-4c1a-be50-8f3b10bfe3c8

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_mem_PG
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_isUnit_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (x : Matrix (Idx r k) (Idx r k) A) :
    IsNU x ↔ ∃ g ∈ PG r (upUniG A k), (g : Matrix (Idx r k) (Idx r k) A) = x := by
  constructor
  · rintro ⟨n, _, hn, ⟨u, hu, rfl⟩, rfl⟩
    have hd : IsUnit u.det := by rw [isUpUni_det A hu]; exact isUnit_one
    exact ⟨toGL n (isN_isUnit_det hn) * phi A r k (toGL u hd),
      (mem_PG _ _).2 ⟨_, toGL u hd, hu, hn, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, h, hh, hn, rfl⟩ := (mem_PG _ _).1 hg
    exact ⟨n, _, hn, ⟨h, hh, rfl⟩, rfl⟩
end Formalism.FourierDecayAlt.P.S3x2
