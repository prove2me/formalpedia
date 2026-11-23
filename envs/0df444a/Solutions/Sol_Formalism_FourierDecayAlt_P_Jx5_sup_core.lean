-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx5.sup_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:43.587159+00:00
-- url     : https://prove2.me/submissions/22267f90-26f5-4f1a-b3aa-6beff7be01df

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx5
namespace Formalism.FourierDecayAlt.P.Jx5
theorem _root_.solution {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (w : ι)
    (hg : 0 < G.g) (hk : 0 < G.ka) (S : Set ℝ) :
    sSup ((fun Y => G.g ^ G.m * (G.place w).be G.ka de de' T T' Y) '' S) /
        (G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹) =
      sSup ((fun Y => (G.place w).core de de' T T' Y) '' S) := by
  have ha : 0 < G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹ := by positivity
  have e : (fun Y => G.g ^ G.m * (G.place w).be G.ka de de' T T' Y) '' S =
      (G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹) • ((fun Y => (G.place w).core de de' T T' Y) '' S) := by
    rw [← Set.image_smul, Set.image_image]
    refine Set.image_congr fun Y _ => ?_
    show G.g ^ G.m * ((G.ka ^ (G.m - 1))⁻¹ * (G.place w).core de de' T T' Y) = _
    rw [smul_eq_mul, mul_assoc]
  rw [e, Real.sSup_smul_of_nonneg ha.le, smul_eq_mul, mul_div_cancel_left₀ _ ha.ne']
end Formalism.FourierDecayAlt.P.Jx5
