-- Prove2me | solution 1 for Formalism.REAL.coeMatrix_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:49.821112+00:00
-- url     : https://prove2.me/submissions/03f0a852-43ce-4b59-a21d-f27f6d9c5dbf

import Definitions.Def_Formalism_RealPlaceAnalysis_UJLocCompact
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Topology
noncomputable section
namespace Formalism.REAL
private lemma jm_sq_lemma {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix Topology
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    (Jm ε * gᴴ * Jm ε) * g = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', jm_sq_lemma]
end Formalism.REAL
