-- Prove2me | solution 1 for Formalism.REAL.f1alg_ct_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:05.28335+00:00
-- url     : https://prove2.me/submissions/44baff18-6125-465d-9621-cb1b52ee8886

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace Formalism.REAL
private lemma Jm_conjTranspose_eq {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    (Jm ε * A * Jm ε)ᴴ = Jm ε * Aᴴ * Jm ε := by
  rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose_eq, Matrix.mul_assoc]
end Formalism.REAL
