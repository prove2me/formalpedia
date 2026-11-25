-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedS.qr_of_dp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:24.794439+00:00
-- url     : https://prove2.me/submissions/8ecaf750-affc-478d-a986-25762c0c2747

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.NFRadRedS
theorem _root_.solution {c : Fin r → ℂ} {g : Q.Mx k r} (hc : c ∈ OmX r) (hg : g ∈ Qx5.Dp k r z z') :
    (c, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z' := by
  have h0 : 0 < GGl k r z z' g := hg
  unfold GGl at h0
  exact ⟨hc, by linarith⟩
end Formalism.FourierDecayAlt.P.NFRadRedS
