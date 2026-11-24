-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:30.54936+00:00
-- url     : https://prove2.me/submissions/2052b38b-1d92-421d-b42a-d5690610be85

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_vmv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
private lemma hpk_conjTranspose_self (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | (simp; done) | (exfalso; omega)
end HermitianXiVector
namespace HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
end HermitianXiVector
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianXiVector
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    C2.nEich k r z ξ *ᵥ y = y + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • (-(herm (Hpk k r) y z) • C2.xiV k r ξ +
      herm (Hpk k r) y (C2.xiV k r ξ) • z + ((1 / 2 : ℂ) * herm (Hpk k r) y (C2.xiV k r ξ)) • C2.xiV k r ξ) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := hpk_conjTranspose_self k r
  first
  | simp only [C2.nEich, add_mulVec, one_mulVec, smul_mulVec, neg_mulVec, vmv_apply _ hH, neg_smul, smul_smul]
  | simp only [C2.nEich, add_mulVec, one_mulVec, Matrix.smul_mulVec_assoc, neg_mulVec, vmv_apply _ hH, neg_smul, smul_smul]
end Formalism.FourierDecayAlt.P.HermitianXiVector
