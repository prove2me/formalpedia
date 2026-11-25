-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.first_section_hermitian_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:15.867718+00:00
-- url     : https://prove2.me/submissions/ac80b202-6a8f-43e6-912f-3eb2ec628878

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_inWb_uwb
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_inWb_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_inWb_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_zeta_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_muZ_uwb
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_zeta_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_zeta_muZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_self_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hsec : IsSection k r z z' μsec)
    {g : Q.Mx k r} (hG : 0 < GGl k r z z' g) :
    herm (Hpk k r) (u1 k r z z' μsec g) (u1 k r z z' μsec g) = (qf k r z z' g : ℂ) ∧
      herm (Hpk k r) z (u1 k r z z' μsec g) = 0 ∧ inWb k r (u1 k r z z' μsec g) := by
  have hζ := zeta_lt hG
  have hμ := NFRadRedA.muZ_uwb hsec hζ
  have hμU : muZ k r μsec (zetaL k r z z' (Fin.last r) g) ∈ UH (Hpk k r) := hμ.1
  have hvz : herm (Hpk k r) (muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ z') z = zetaL k r z z' (Fin.last r) g := by
    rw [← NFRadRedA.zeta_eq]
    exact NFRadRedA.zeta_muZ hz hz' hsec hζ
  have hvv : herm (Hpk k r) (muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ z') (muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ z') =
      -((Tz k r z' : ℝ) : ℂ) := by
    rw [TwoByOneBlock.herm_UH hμU, TwoByOneBlock.herm_self_eq]
  obtain ⟨h1, h2⟩ := key hT.ne' (TwoByOneBlock.herm_self_eq z) hvz hvv
  exact ⟨h1, h2, inWb_add (inWb_uwb hμ hz') (inWb_smul _ hz)⟩
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
