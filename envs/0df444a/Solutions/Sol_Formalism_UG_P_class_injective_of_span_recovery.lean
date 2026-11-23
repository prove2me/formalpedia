-- Prove2me | solution 1 for Formalism.UG.P.class_injective_of_span_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:42.7725+00:00
-- url     : https://prove2.me/submissions/cc3281b5-160b-44f0-9d22-0b9082217297

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassInjectiveOfSpanRecovery

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG Formalism.UG.CS
namespace Formalism.UG.P
theorem _root_.solution (hSpanRecover : Formalism.UG.CS.SpanRecover)
    (hGlobLatEquiv : Formalism.UG.CS.GlobLatEquiv) : Formalism.UG.CS.ClassInj := by
  intro F E _ _ _ _ _ n _ _ σ J Λ hfin hspan g g' γ hγ hlat
  set A := FiniteAdeleRing (𝓞 F) F with hA
  set L := latS (F := F) A (tensInt (F := F) A (intOE E) (intAd F)) Λ with hL
  set γA : GL n (E ⊗[F] A) := bc (inclE (F := F) A) γ with hγA

  have hsig : ∀ e : E, sigR σ A (inclE (F := F) A e) = inclE (F := F) A (σ e) := by
    intro e
    simp [sigR, inclE]
  have hγm : (γA : Matrix n n (E ⊗[F] A)) = (γ : Matrix n n E).map (inclE (F := F) A) := rfl
  have hγU : γA ∈ UPts σ J A := by
    change cT (sigR σ A) (γA : Matrix n n (E ⊗[F] A)) * J.map (inclE (F := F) A)
      * (γA : Matrix n n (E ⊗[F] A)) = J.map (inclE (F := F) A)
    have h0 : cT (σ : E →+* E) (γ : Matrix n n E) * J * (γ : Matrix n n E) = J := hγ
    have hc : cT (sigR σ A) (γA : Matrix n n (E ⊗[F] A))
        = (cT (σ : E →+* E) (γ : Matrix n n E)).map (inclE (F := F) A) := by
      ext i j
      simp [cT, hγm, hsig]
    rw [hc, hγm, ← Matrix.map_mul, ← Matrix.map_mul, h0]

  have heq : globLat (γA * (g' : GL n (E ⊗[F] A))) Λ = globLat (g : GL n (E ⊗[F] A)) Λ := by
    have h1 := hGlobLatEquiv F E n Λ γ (g' : GL n (E ⊗[F] A)) 1 (one_mem _)
    rw [mul_one] at h1
    rw [h1, hlat]
  have hR : ∀ u : n → E ⊗[F] A,
      (((g : GL n (E ⊗[F] A))⁻¹ : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ u ∈ L ↔
        (((γA * (g' : GL n (E ⊗[F] A)))⁻¹ : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ u ∈ L := by
    intro u
    have h1 := hSpanRecover F E n Λ hfin hspan (g : GL n (E ⊗[F] A)) u
    have h2 := hSpanRecover F E n Λ hfin hspan (γA * (g' : GL n (E ⊗[F] A))) u
    rw [heq] at h2
    exact h1.symm.trans h2
  set k : GL n (E ⊗[F] A) := (g : GL n (E ⊗[F] A))⁻¹ * (γA * (g' : GL n (E ⊗[F] A))) with hk
  have hkS : k ∈ stabGL L := by
    intro x
    have h := hR (((γA * (g' : GL n (E ⊗[F] A)) : GL n (E ⊗[F] A)) : Matrix n n _) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    exact h.symm
  have hkU : k ∈ UPts σ J A :=
    mul_mem (inv_mem g.2) (mul_mem hγU g'.2)
  rw [DoubleCoset.eq]
  refine ⟨⟨γA⁻¹, inv_mem hγU⟩, ?_, ⟨k, hkU⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨γ⁻¹, inv_mem hγ, map_inv _ _⟩
  · rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hkU, hkS⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hk]
    group
end Formalism.UG.P
