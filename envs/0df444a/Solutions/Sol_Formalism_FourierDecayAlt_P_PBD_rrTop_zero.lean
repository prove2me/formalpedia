-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.rrTop_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:10:11.532325+00:00
-- url     : https://prove2.me/submissions/ae2cf725-7f9f-4e51-bd34-f95577cfe9ff

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_ptG_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_hsInner_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (l0 : ℕ)
    (T : D.LevTower P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (Θ : Top.TopLift P.k P.r Wp Wq) (TP : Top.TypeProj P T.base.π T.base.z (m₀ *ᵥ ν')) (s : ℂ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (H H' : C.LPt) (c : ℂ) (hH : D.ptSize H = P.r)
    (hc : Complex.normSq c ≤ Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') :
    D.RRplace T s ν' m₀ (Top.topOf P l0 T ν' m₀ Θ TP) F (P.r + 1) w (H ++ [(1, c)]) H' = 0 := by
  have hv : ∀ F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp), D.vecV T.base ν' m₀ F' (H ++ [(1, c)]) = 0 := by
    intro F'
    unfold D.vecV
    rw [dif_neg]
    rintro ⟨-, hG⟩
    rw [ptG_app _ c H P.r hH] at hG
    have : Complex.normSq (D.ptMatN H P.r).det * (Complex.normSq c - Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (by linarith)
    linarith
  unfold D.RRplace
  split_ifs with h1 h2 h3 h4
  · omega
  · rw [hv, hsInner_zero_left]
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    rw [hv, ContinuousLinearMap.comp_zero, hsInner_zero_left, mul_zero]
  · rfl
  · rfl
end Formalism.FourierDecayAlt.P.PBD
