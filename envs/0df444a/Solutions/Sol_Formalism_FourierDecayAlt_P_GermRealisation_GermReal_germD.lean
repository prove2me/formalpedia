-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermRealisation.GermReal.germD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:00.966712+00:00
-- url     : https://prove2.me/submissions/54dfb9e9-0007-4e83-a5f8-e0c5299e2165

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocTail
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfRealised
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermRealisation_integral_inner_self_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integral_norm_cvec_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRealisation
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
attribute [instance] GermReal.nag GermReal.ips GermReal.cs
namespace Formalism.FourierDecayAlt.P.GermRealisation
namespace GermReal
theorem _root_.solution {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : GermReal S v ε b s a Y) (hs : 2 ≤ s) (B : ℝ)
    (hB : ∀ h ∈ Y, ∀ t : ℂ, t ≠ 0 → ‖KB.gN S v ε (b + s - 2) a (h ++ [(s - 1, t)]) (h ++ [(s - 1, t)])‖ ≤ B) :
    GermD s R.β R.ε' Y R.ut R.bt B := by
  refine ⟨by omega, R.hβ, R.hε', R.memU, fun h hh x hx => ?_, R.meas, R.loc, R.germ⟩
  have hg := R.gram h hh h hh x x hx hx
  have hb := hB h hh x⁻¹ (inv_ne_zero hx)
  unfold gK at hg
  dsimp only at hg
  rw [hg] at hb
  unfold gramL Uc at hb
  dsimp only at hb
  rw [integral_inner_self_eq, integral_norm_cvec_sq s (R.ut h) x hx, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hb
  exact hb
end GermReal
end Formalism.FourierDecayAlt.P.GermRealisation
