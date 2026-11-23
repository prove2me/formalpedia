-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.Ph_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:40.093461+00:00
-- url     : https://prove2.me/submissions/5889f09c-7325-446a-9b04-84aa02c75002

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
variable {B : Type} [Ring B] [Algebra ℂ B] (p0 p1 : B) (c : ℂ)
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (T : B) (γ Ya Y : ℂ) (h1 : Y ≠ γ) (h2 : Ya ≠ γ) (h3 : Y ≠ Ya) :
    Ph p0 p1 (Y - Ya)⁻¹ ((Y - γ)⁻¹ • T) ((Ya - γ)⁻¹ • T) =
      (Y - γ)⁻¹ • (((1 + 1 / (Ya - γ)) • p0 + (1 - 1 / (Ya - γ)) • p1) * T) := by
  have h1' : Y - γ ≠ 0 := sub_ne_zero.mpr h1
  have h2' : Ya - γ ≠ 0 := sub_ne_zero.mpr h2
  have h3' : Y - Ya ≠ 0 := sub_ne_zero.mpr h3
  have key : (Y - Ya)⁻¹ • ((Y - γ)⁻¹ • T - (Ya - γ)⁻¹ • T) = (-((Y - γ)⁻¹ * (Ya - γ)⁻¹)) • T := by
    rw [← sub_smul, smul_smul]
    congr 1
    field_simp
    ring
  unfold Ph
  rw [key, ← sub_smul, ← add_smul, mul_smul_comm, mul_smul_comm, add_mul, smul_mul_assoc,
    smul_mul_assoc, smul_add, smul_smul, smul_smul]
  congr 2 <;> ring
end Formalism.FourierDecayAlt.P.Fr11
