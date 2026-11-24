-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.CC.Surj.wal_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:29:20.589449+00:00
-- url     : https://prove2.me/submissions/2e4e2949-0897-4307-b932-f8dd9335b861

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_walInt_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_walInt_smul
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_walInt_sub
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_walInt_neg
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_walInt_cT
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_cT_sub
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_cT_smul
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_inv_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.MainNotions.Gaps.CC.Surj
theorem _root_.solution (S : Subring A) (τ : A →+* A) (hτ : ∀ s ∈ S, τ s ∈ S) (J Ji : Matrix n n A)
    (hJi : Ji * J = 1) (L : Submodule S (n → A)) (δ c : A) (hδ : δ ∈ S) (hc : c ∈ S)
    (hτδ : τ δ = δ) (hτc : τ c = c)
    (hL : ∀ N : Matrix n n A, walInt S N → ∀ x ∈ L, (δ • N) *ᵥ x ∈ L)
    (g γ : GL n A) (hg : g ∈ UJ τ J) (hγ : γ ∈ UJ τ J)
    (hgi : walInt S (c • ((g⁻¹ : GL n A) : Matrix n n A))) (hJ : walInt S (c • J))
    (hJi' : walInt S (c • Ji)) (T : Matrix n n A) (hT : walInt S T)
    (hD : (g : Matrix n n A) - (γ : Matrix n n A) = (c * c * δ) • T) :
    γ⁻¹ * g ∈ stabGL L := by
  set G : Matrix n n A := (g : Matrix n n A) with hG
  set Γ : Matrix n n A := (γ : Matrix n n A) with hΓ
  set Gi : Matrix n n A := ((g⁻¹ : GL n A) : Matrix n n A) with hGi
  set Γi : Matrix n n A := ((γ⁻¹ : GL n A) : Matrix n n A) with hΓi
  have e1 : Gi * (G - Γ) = δ • (c • ((c • Gi) * T)) := by
    rw [hD]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1; ring
  have e2 : Γi = Gi - Ji * cT τ (G - Γ) * J := by
    rw [hΓi, hGi, wal_inv_eq τ J Ji hJi γ hγ, wal_inv_eq τ J Ji hJi g hg, wal_cT_sub, Matrix.mul_sub,
      Matrix.sub_mul, sub_sub_cancel]
  have e3 : Ji * cT τ (G - Γ) * J * (G - Γ) =
      δ • ((c * c * δ) • ((c • Ji) * cT τ T * (c • J) * T)) := by
    rw [hD, wal_cT_smul, map_mul, map_mul, hτc, hτδ]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1; ring
  have i1 : walInt S (c • ((c • Gi) * T)) := walInt_smul S hc (walInt_mul S hgi hT)
  have i3 : walInt S ((c * c * δ) • ((c • Ji) * cT τ T * (c • J) * T)) :=
    walInt_smul S (mul_mem (mul_mem hc hc) hδ)
      (walInt_mul S (walInt_mul S (walInt_mul S hJi' (walInt_cT S τ hτ hT)) hJ) hT)
  have hΓΓ : Γi * Γ = 1 := Units.inv_mul γ
  have hGG : Gi * G = 1 := Units.inv_mul g
  have hk : Γi * G = 1 + δ • (c • ((c • Gi) * T) -
      (c * c * δ) • ((c • Ji) * cT τ T * (c • J) * T)) := by
    have : Γi * G = 1 + Γi * (G - Γ) := by rw [Matrix.mul_sub, hΓΓ]; abel
    rw [this, e2, Matrix.sub_mul, e1, e3, smul_sub]
  have hki : Gi * Γ = 1 + δ • (-(c • ((c • Gi) * T))) := by
    have : Gi * Γ = 1 - Gi * (G - Γ) := by rw [Matrix.mul_sub, hGG]; abel
    rw [this, e1, smul_neg, sub_eq_add_neg]
  have hkk : Gi * Γ * (Γi * G) = 1 := by
    have h1 : Γ * Γi = 1 := Units.mul_inv γ
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Γ, h1, Matrix.one_mul, hGG]
  intro x
  rw [Units.val_mul]
  constructor
  · intro hx
    rw [hk, Matrix.add_mulVec, Matrix.one_mulVec]
    exact add_mem hx (hL _ (walInt_sub S i1 i3) x hx)
  · intro hx
    have : x = (Gi * Γ) *ᵥ ((Γi * G) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]
    rw [this, hki, Matrix.add_mulVec, Matrix.one_mulVec]
    exact add_mem hx (hL _ (walInt_neg S i1) _ hx)
end Formalism.MainNotions.Gaps.CC.Surj
