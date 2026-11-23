-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.exists_injective_shift_of_orbZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:54.750451+00:00
-- url     : https://prove2.me/submissions/81bc2c29-5700-442c-b228-4d854a9e23ab

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isPP_of_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_mem_PPsub
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_base_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_sUp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_sUp_conj
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_sUp_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K) (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w : Point K) (y)
    (σ : Matrix (Fin w.1.sum) (Fin w.1.sum) K) (hσ : IsPP R k σ) :
    ∃ S : Cos R w → Cos R w, Function.Injective S ∧ ∀ q, kap R k w q = y →
      kap R k w (S q) = y ∧ phase ψ (rep R (S q)) = phase ψ (rep R q) * ψ (sUp σ) ∧
      ∀ p, orbZ w (rep R q) = base R k w y * p →
        ∃ g, IsUpUni g ∧ IsInt R g ∧ orbZ w (rep R (S q)) = base R k w y * (σ * p) * g := by
  obtain ⟨y1, y2⟩ := y
  have hσd : IsUnit σ.det := by rw [isUpUni_det K hσ.1.1]; exact isUnit_one
  obtain ⟨σG, hσG⟩ : ∃ x : upUniG K w.1.sum,
      ((x : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = σ :=
    ⟨⟨Matrix.nonsingInvUnit σ hσd, hσ.1.1⟩, rfl⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u : upUniG K w.1.sum, y2.out = u := ⟨_, rfl⟩
  have hmk : (QuotientGroup.mk u₀ : upUniG K w.1.sum ⧸ PPsub R k w.1.sum) = y2 := by
    rw [← hu₀]; exact QuotientGroup.out_eq' y2
  obtain ⟨τ, hτ⟩ : ∃ x : upUniG K w.1.sum, x = u₀ * σG * u₀⁻¹ := ⟨_, rfl⟩
  refine ⟨fun q => (q.1, QuotientGroup.mk (τ * q.2.out)), ?_, ?_⟩
  · intro a b hab
    have h1 : a.1 = b.1 := (Prod.mk.inj hab).1
    have h2 : (QuotientGroup.mk (τ * a.2.out) : upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) =
        QuotientGroup.mk (τ * b.2.out) := (Prod.mk.inj hab).2
    rw [QuotientGroup.eq] at h2
    have h3 : (τ * a.2.out)⁻¹ * (τ * b.2.out) = a.2.out⁻¹ * b.2.out := by group
    rw [h3, ← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
    exact Prod.ext h1 h2
  · intro q hq
    have hq1 : q.1 = y1 := (Prod.mk.inj hq).1
    have hq2 : (QuotientGroup.mk q.2.out : upUniG K w.1.sum ⧸ PPsub R k w.1.sum) = y2 :=
      (Prod.mk.inj hq).2
    subst hq1
    obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (intSub R (upUniG K w.1.sum)) (τ * q.2.out)
    have hp0 : u₀⁻¹ * q.2.out ∈ PPsub R k w.1.sum := by
      rw [← QuotientGroup.eq, hmk, hq2]
    have hγP : (γ : upUniG K w.1.sum) ∈ PPsub R k w.1.sum :=
      isPP_of_int R k (γ : upUniG K w.1.sum).2 γ.2.1
    have hσP : σG ∈ PPsub R k w.1.sum := by
      rw [grp_mem_PPsub, hσG]; exact hσ
    refine ⟨?_, ?_, ?_⟩
    · refine Prod.ext rfl ?_
      show (QuotientGroup.mk (QuotientGroup.mk (τ * q.2.out) :
        upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)).out :
          upUniG K w.1.sum ⧸ PPsub R k w.1.sum) = y2
      rw [hγ, ← hmk, eq_comm, QuotientGroup.eq]
      have : u₀⁻¹ * (τ * q.2.out * γ) = σG * (u₀⁻¹ * q.2.out) * γ := by
        rw [hτ]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hσP hp0) hγP
    · show ψ (sLow _ + sUp (((QuotientGroup.mk (τ * q.2.out) :
        upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)).out : GL (Fin w.1.sum) K) :
          Matrix (Fin w.1.sum) (Fin w.1.sum) K)) = ψ (sLow _ + sUp _) * ψ (sUp σ)
      rw [hγ, grp_sUp_mul, grp_sUp_mul, hτ, grp_sUp_conj, hσG, ← AddChar.map_add_eq_mul]
      have h1 := hψ _ (Formalism.DoubleCosetMeasures.P.sUp_mem R _ γ.2.1)
      rw [← add_assoc, AddChar.map_add_eq_mul, h1, mul_one]
      congr 1
      simp only [rep]
      ring
    · intro p hp
      refine ⟨((γ : upUniG K w.1.sum) : GL (Fin w.1.sum) K), (γ : upUniG K w.1.sum).2, γ.2.1, ?_⟩
      have e0 : ((u₀ : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
          (((u₀⁻¹ : upUniG K w.1.sum) : GL (Fin w.1.sum) K) :
            Matrix (Fin w.1.sum) (Fin w.1.sum) K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
      have e1 : ∀ M : Matrix (Fin w.1.sum) (Fin w.1.sum) K,
          ((u₀ : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
          ((((u₀⁻¹ : upUniG K w.1.sum) : GL (Fin w.1.sum) K) :
            Matrix (Fin w.1.sum) (Fin w.1.sum) K) * M) = M := by
        intro M; rw [← Matrix.mul_assoc, e0, Matrix.one_mul]
      have hb : base R k w (q.1, y2) * (((u₀⁻¹ * q.2.out : upUniG K w.1.sum) :
          GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = orbZ w (rep R q) := by
        simp only [base, orbZ, rep, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hu₀]
        rw [e1]
      have hpe : p = (((u₀⁻¹ * q.2.out : upUniG K w.1.sum) :
          GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := by
        have := congrArg (fun M => (base R k w (q.1, y2))⁻¹ * M) (hb.trans hp)
        simp only [Matrix.nonsing_inv_mul_cancel_left _ _ (base_det R k w (q.1, y2))] at this
        exact this.symm
      show orbZ w (q.1.out, (QuotientGroup.mk (τ * q.2.out) :
        upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)).out) = _
      rw [hγ, hpe, hτ]
      simp only [base, orbZ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hσG, hu₀]
end Formalism.FourierDecayAlt.P.A5x9
