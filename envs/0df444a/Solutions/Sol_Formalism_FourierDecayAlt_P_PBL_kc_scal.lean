-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.kc_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:39.951263+00:00
-- url     : https://prove2.me/submissions/149295a6-c164-4f9c-a226-17c953e6f34d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_g_pos_of_built
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_lamS_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_gamLev_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_gamLev_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_scal_id
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_bSt_pos__d344a790c9c8
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_rd_pos__cb5bba46fb5e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBL
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBL
theorem _root_.solution {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter)
    (h h' : C.LPt) :
    (KB.dlB S (j + 1) 1)⁻¹ * (Kc S v j w h h' * |(lamS S j ^ 2)⁻¹|) = dW S v j w h h' := by
  have hgpos := g_pos_of_built hB
  have hrd := rd_pos' E
  have hκ : 0 < D.kapG (S.g : ℝ) (S6.rd E) := by unfold D.kapG; positivity
  have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
  have hlam_pos := lamS_pos S hgpos j
  have hfac := gamLev_succ S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) j hj
  have hΓpos : 0 < ΓS S (j + 1) := gamLev_pos _ _ _ _ hκ hδ _
  have hbh : 0 < bS S h := bSt_pos' _ hκ h
  have hbh' : 0 < bS S h' := bSt_pos' _ hκ h'
  have hgl : (S.g : ℝ) / (2 * Real.pi) = (D.kapG (S.g : ℝ) (S6.rd E) * S6.rd E)⁻¹ := by
    unfold D.kapG; field_simp
  have hfrj : S.fr (j + 1) 1 = S6.rd E ^ (-(S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ))) := by
    unfold C.HidaSetting.fr
    rw [← Real.rpow_intCast]
    push_cast
    ring_nf
  have hkey : rhoS S j * (lamS S j ^ 2)⁻¹ =
      S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)) *
        D.kapG (S.g : ℝ) (S6.rd E) ^ (4 * ((S.G.r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev S.G.k S.G.r (j + 1) - 1)) := by
    rw [rhoS, hfrj, lamS, hgl, ← div_eq_mul_inv, scal_id _ _ hκ hrd]
    congr 1
    congr 1
    unfold S6.nuBlock
    push_cast
    ring
  set K : ℝ := √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * rhoS S j with hK
  have hscal : K * |(lamS S j ^ 2)⁻¹| =
      KB.dlB S (j + 1) 1 * (√(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S j))) := by
    rw [abs_of_pos (inv_pos.2 (pow_pos hlam_pos 2))]
    have hΓj : ΓS S j = _ := hfac
    rw [hΓj]
    have e2 : K * (lamS S j ^ 2)⁻¹ =
        √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * (rhoS S j * (lamS S j ^ 2)⁻¹) := by
      rw [hK]; ring
    rw [e2, hkey]
    unfold KB.dlB
    have hΓ1 : ΓS S (j + 1) =
        D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (j + 1) := rfl
    rw [← hΓ1, zpow_neg]
    have hκX := zpow_pos hκ (4 * ((S.G.r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev S.G.k S.G.r (j + 1) - 1))
    field_simp
  have hdl : 0 < KB.dlB S (j + 1) 1 := by unfold KB.dlB; exact div_pos (zpow_pos hrd _) hδ
  have e3 : Kc S v j w h h' * |(lamS S j ^ 2)⁻¹| = (K * |(lamS S j ^ 2)⁻¹|) / S.sizeAt v w := by
    unfold Kc; rw [hK]; ring
  rw [e3, hscal, mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hdl.ne', one_mul]
  unfold dW
  ring
end Formalism.FourierDecayAlt.P.PBL
