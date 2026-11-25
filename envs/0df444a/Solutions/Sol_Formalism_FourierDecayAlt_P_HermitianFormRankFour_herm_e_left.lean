-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.herm_e_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:22:22.983045+00:00
-- url     : https://prove2.me/submissions/d56c3a72-3a77-4808-9ed9-0d9db5f9839e

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
namespace HermitianFormRankFour
section L2
open scoped Matrix.Norms.L2Operator
end L2
section Core
variable {N K J : Type} [Fintype N] [Fintype K] [Fintype J] [DecidableEq N] [DecidableEq K] [DecidableEq J]
variable {V : Matrix N K ℂ} {C : Matrix N J ℂ} {Vd : Matrix K N ℂ} {Cd : Matrix J N ℂ}
end Core
section Geo
variable {k r : ℕ}
private theorem hpk_col_e_lemma (k r : ℕ) (c : Fin r) (t : Fin (2 * r + k + 1)) :
    Hpk k r t (eI k r c) = if t = esI k r c then 1 else 0 := by
  have := c.isLt
  have := t.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega
end Geo
end HermitianFormRankFour
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianFormRankFour
theorem _root_.solution (w : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    herm (Hpk k r) (bvec (eI k r c)) w = star (w (esI k r c)) := by
  simp only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Pi.star_apply, hpk_col_e_lemma]
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
