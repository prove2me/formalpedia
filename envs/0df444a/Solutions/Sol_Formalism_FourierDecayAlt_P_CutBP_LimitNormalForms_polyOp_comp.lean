-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.polyOp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:04.383269+00:00
-- url     : https://prove2.me/submissions/88b25971-1f07-4d33-b87b-1b69d3dce0c1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ext_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_op_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_op_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ck_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_word_le_opOrder
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_opOrder_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_sgs_gv
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_polyOp_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_comp_raw
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_polyDeg_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_lie_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_rho_eq_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution [FiniteDimensional ℂ Wp] {o₁ κ₁ o₂ κ₂ : ℕ} {Θ₁ Θ₂ : DiffOp k r Wp Wq}
    (h₁ : CutMP.PolyOp o₁ κ₁ Θ₁) (h₂ : CutMP.PolyOp o₂ κ₂ Θ₂) :
    ∃ Θ : DiffOp k r Wp Wq, CutMP.PolyOp (o₁ + o₂) (κ₁ + κ₂) Θ ∧
      (∀ (VV : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp)), CkOn ((o₁ + o₂ : ℕ) : ℕ∞) VV F →
        ∀ g ∈ VV, g ∈ GV k r → opApply Θ F g = opApply Θ₁ (opApply Θ₂ F) g) ∧
      ∀ (D : RealPlaceData k r Wp Wq) (O : Set (Mat k r)), IsOpen O →
        Commutes D (GV k r ∩ O) Θ₁ → Commutes D (GV k r ∩ O) Θ₂ → Commutes D (GV k r ∩ O) Θ := by
  obtain ⟨Θ₀, hP, he⟩ := comp_raw (k := k) (Wp := Wp) (Wq := Wq) r r (Nat.zero_add r).symm o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ h₁ h₂
  let Z : DTerm k r Wp Wq := scalTerm (fun _ => 0) (List.replicate (o₁ + o₂) 0)
    (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact lie_zero)
  have hZ : ∀ F, opApply (Z :: Θ₀) F = opApply Θ₀ F := fun F => by
    rw [op_cons]; funext g; simp [Z, scalTerm]
  have hord : o₁ + o₂ ≤ opOrder (Z :: Θ₀) := by
    have := word_le_opOrder (Z :: Θ₀) Z (by simp)
    simpa [Z, scalTerm] using this
  have hloc : ∀ (VV : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp)), CkOn ((o₁ + o₂ : ℕ) : ℕ∞) VV F →
      ∀ g ∈ VV, g ∈ GV k r → opApply (Z :: Θ₀) F g = opApply Θ₁ (opApply Θ₂ F) g := by
    intro VV F hF g hgV hg
    obtain ⟨f, U, hf, hU, hgU, hfe⟩ := ext_loc hF hgV
    rw [← op_congr (Z :: Θ₀) hU (fun x hx hxU => hfe x hxU hx) hg hgU, hZ, he f hf g hg]
    exact op_congr Θ₁ hU (fun x hx hxU => op_congr Θ₂ hU (fun y hy hyU => hfe y hyU hy) hx hxU) hg hgU
  refine ⟨Z :: Θ₀, fun T hT => ?_, hloc, ?_⟩
  · rcases List.mem_cons.1 hT with rfl | h'
    · exact ⟨by simp [Z, scalTerm], fun _ => 0, polyDeg_const _ 0, fun _ => rfl, fun _ => rfl⟩
    · exact hP T h'
  · intro D O hO c₁ c₂ p hp f hf g hg
    have hf' : CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (GV k r) f := sCkOn_mono (by exact_mod_cast hord) hf
    have hρf : CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (GV k r) (rho D p f) := by
      rw [rho_eq_trn]
      exact CkOn_trn _ (gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)) (gv_mul hp.2.2.2.1 hp.2.2.1.1) hf'
    have o1 : opOrder Θ₁ ≤ o₁ := opOrder_le Θ₁ fun T hT => (h₁ T hT).1
    have o2 : opOrder Θ₂ ≤ o₂ := opOrder_le Θ₂ fun T hT => (h₂ T hT).1
    have hf2 : CkOn (opOrder Θ₂ : ℕ∞) (GV k r) f := sCkOn_mono (by exact_mod_cast o2.trans (Nat.le_add_left _ _)) hf'
    have hφ : CkOn (opOrder Θ₁ : ℕ∞) (GV k r) (opApply Θ₂ f) :=
      sCkOn_mono (by exact_mod_cast o1) (ck_op (m := (o₁ : ℕ∞)) (o := o₂) (by exact_mod_cast hf') Θ₂
        fun T hT => ⟨polyOp_ck h₂ _ T hT, (h₂ T hT).1⟩)
    rw [hloc _ _ hρf g hg.1 hg.1,
      op_congr Θ₁ hO (fun x hx hxO => c₂ p hp f hf2 x ⟨hx, hxO⟩) hg.1 hg.2, c₁ p hp _ hφ g hg]
    simp only [rho]
    rw [hloc _ f hf' _ (sgs_gv D hp hg.1) (sgs_gv D hp hg.1)]
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
