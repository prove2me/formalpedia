-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.sep_grid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:35.971172+00:00
-- url     : https://prove2.me/submissions/8f105be1-5f67-49c0-90e1-4778e6613b06

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_ntop_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField Finset
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) {b b' : ℕ} {y y' : ℝ}
    (hy : y ∈ S.grid v b) (hy' : y' ∈ S.grid v b') (hne : b ≠ b') {e e' : ℝ}
    (he : e ∈ ({0, 1} : Finset ℝ)) (he' : e' ∈ ({0, 1} : Finset ℝ)) :
    (S.Ntop : ℝ) ^ 2 + 1 ≤ |(y + e) - (y' + e')| := by
  obtain ⟨hlen, hgr, -⟩ := hG v
  have hN : (20 : ℝ) ≤ S.Ntop := ntop_ge S
  obtain ⟨-, -, hyl, hyu⟩ := hgr b y hy
  obtain ⟨-, -, hyl', hyu'⟩ := hgr b' y' hy'
  simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
  have he0 : 0 ≤ e ∧ e ≤ 1 := by rcases he with rfl | rfl <;> norm_num
  have he0' : 0 ≤ e' ∧ e' ≤ 1 := by rcases he' with rfl | rfl <;> norm_num
  unfold C.gridL at hyl hyu hyl' hyu'
  have hNpos : (0 : ℝ) < 6 * S.Ntop := by positivity
  have hΔ : (S.Ntop : ℝ) ^ 2 + 1 ≤ (S.cutHi v - S.cutLo v) / (6 * S.Ntop) := by
    rw [le_div_iff₀ hNpos]
    nlinarith
  set Δ := (S.cutHi v - S.cutLo v) / (6 * S.Ntop) with hΔdef
  have hΔ0 : 0 ≤ Δ := by nlinarith
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hbb : (b : ℝ) + 1 ≤ b' := by exact_mod_cast hlt
    have key : 2 * (b : ℝ) * Δ + 2 * Δ ≤ 2 * (b' : ℝ) * Δ := by nlinarith
    exact le_abs.2 (Or.inr (by linarith))
  · have hbb : (b' : ℝ) + 1 ≤ b := by exact_mod_cast hlt
    have key : 2 * (b' : ℝ) * Δ + 2 * Δ ≤ 2 * (b : ℝ) * Δ := by nlinarith
    exact le_abs.2 (Or.inl (by linarith))
end Formalism.FourierDecayAlt.P.PBD
