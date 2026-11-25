-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.hermFrameCount_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:08.613562+00:00
-- url     : https://prove2.me/submissions/c184c837-09c5-489f-8f7c-c5a0fd1c779b

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_fconj_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_herm_count_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.HermFrameCount := by
  intro hUO hW K _ _ q n a J T hc hJ hdJ hT
  let _ : StarRing K := starRingOfCard K q hc
  have hs : ∀ x : K, star x = x ^ q := fun x => rfl
  have hUO' : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b := by
    intro b J h1 h2
    have := hUO K q b J hc (by rw [fconj_eq hs]; exact h1) h2
    simpa only [fconj_eq hs] using this
  have hW' : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y := by
    intro n a J X Y h1 h2 h3 h4 h5
    have := hW K q n a J X Y hc (by rw [fconj_eq hs]; exact h1) h2 h3 h4
      (by simp only [fconj_eq hs]; exact h5)
    simpa only [fconj_eq hs] using this
  have := herm_count_star hs hc hUO' hW' n a J T (by rw [← fconj_eq hs]; exact hJ) hdJ
    (by rw [← fconj_eq hs]; exact hT)
  simpa only [fconj_eq hs] using this
end Formalism.FourierDecayAlt.P
