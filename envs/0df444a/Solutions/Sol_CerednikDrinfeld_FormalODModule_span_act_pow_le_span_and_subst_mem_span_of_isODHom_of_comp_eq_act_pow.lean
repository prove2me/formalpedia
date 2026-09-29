-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.span_act_pow_le_span_and_subst_mem_span_of_isODHom_of_comp_eq_act_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/25e2e796-4b26-577c-a078-b96c779dae48

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_span_act_pow_le_span_and_subst_mem_span_of_isODHom_of_comp_eq_act_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff X subst_X)
set_option linter.unusedSectionVars false

namespace P2mKA

section Span

variable {B : Type} [CommRing B] {σ τ : Type} [Finite τ]

theorem adicEval_zero_eq {T : Type} [CommRing T] [Algebra B T] (G : MvPowerSeries τ B) :
    MvFormalGroup.adicEval (⊥ : Ideal T) (fun _ : τ => (0 : T)) G = algebraMap B T (constantCoeff G) := by
  let ψ : MvPowerSeries τ B →ₐ[B] T :=
    (Algebra.ofId B T).comp { (MvPowerSeries.constantCoeff : MvPowerSeries τ B →+* B) with
      commutes' := fun r => MvPowerSeries.constantCoeff_C r }
  have hψX : ∀ s : τ, ψ (X s) = 0 := by
    intro s
    show algebraMap B T (constantCoeff (X s : MvPowerSeries τ B)) = 0
    rw [MvPowerSeries.constantCoeff_X, map_zero]
  have hψ : ∀ s : τ, ψ (X s) ∈ ((⊥ : Ideal T)).radical := fun s => by rw [hψX]; exact Ideal.zero_mem _
  have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal T) ψ hψ G
  have hx : (fun s : τ => ψ (X s)) = fun _ => (0 : T) := funext hψX
  rw [hx] at h
  exact h.symm

theorem subst_mem_span (ρ : τ → MvPowerSeries σ B) (hρ0 : ∀ t, constantCoeff (ρ t) = 0)
    (H : MvPowerSeries τ B) (hH : constantCoeff H = 0) :
    subst ρ H ∈ Ideal.span (Set.range ρ) := by
  let I : Ideal (MvPowerSeries σ B) := Ideal.span (Set.range ρ)
  let ψ : MvPowerSeries τ B →ₐ[B] (MvPowerSeries σ B ⧸ I) :=
    (Ideal.Quotient.mkₐ B I).comp (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hρ0))
  have hψX : ∀ t : τ, ψ (X t) = 0 := by
    intro t
    show Ideal.Quotient.mk I (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hρ0) (X t)) = 0
    rw [MvPowerSeries.substAlgHom_apply, subst_X (hasSubst_of_constantCoeff_zero hρ0), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨t, rfl⟩
  have hψ : ∀ t : τ, ψ (X t) ∈ ((⊥ : Ideal (MvPowerSeries σ B ⧸ I))).radical :=
    fun t => by rw [hψX]; exact Ideal.zero_mem _
  have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal (MvPowerSeries σ B ⧸ I)) ψ hψ H
  have hx : (fun t : τ => ψ (X t)) = fun _ => (0 : MvPowerSeries σ B ⧸ I) := funext hψX
  rw [hx, adicEval_zero_eq, hH, map_zero] at h
  have h' : Ideal.Quotient.mk I (subst ρ H) = 0 := by
    have := h
    rw [AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h'

theorem span_stable (ρ : τ → MvPowerSeries σ B) {σ' : Type} (s : σ → MvPowerSeries σ' B) (hs : HasSubst s)
    (J : Ideal (MvPowerSeries σ' B)) (h : ∀ t, subst s (ρ t) ∈ J)
    (G : MvPowerSeries σ B) (hG : G ∈ Ideal.span (Set.range ρ)) : subst s G ∈ J := by
  have hle : Ideal.span (Set.range ρ) ≤
      J.comap ((MvPowerSeries.substAlgHom (R := B) hs : MvPowerSeries σ B →ₐ[B] MvPowerSeries σ' B) :
        MvPowerSeries σ B →+* MvPowerSeries σ' B) := by
    rw [Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    show MvPowerSeries.substAlgHom (R := B) hs (ρ t) ∈ J
    rw [MvPowerSeries.substAlgHom_apply]
    exact h t
  have := hle hG
  rw [Ideal.mem_comap] at this
  change MvPowerSeries.substAlgHom (R := B) hs G ∈ J at this
  rw [MvPowerSeries.substAlgHom_apply] at this
  exact this

end Span

section Kernel

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (Φ Y : FormalODModule p B)
  (ρ β : Series B) (hρ : FormalODModule.IsODHom Φ Y ρ) (hβ : FormalODModule.IsODHom Y Φ β)
  (N : ℕ) (hfac : β.comp ρ = Φ.act ((p : Zp2 p) ^ N))

include hρ hβ hfac in

theorem span_act_pow_le : Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N))) ≤ Ideal.span (Set.range ρ) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← hfac]
  show subst ρ (β i) ∈ Ideal.span (Set.range ρ)
  exact subst_mem_span ρ hρ.1.1 (β i) (hβ.1.1 i)

include hρ in

theorem subst_act_mem (a : Zp2 p) (G : MvPowerSeries (Fin 2) B) (hG : G ∈ Ideal.span (Set.range ρ)) :
    subst (Φ.act a) G ∈ Ideal.span (Set.range ρ) := by
  refine span_stable ρ (Φ.act a) (Φ.isLawHom_act a).hasSubst _ (fun j => ?_) G hG
  have h := congrFun (hρ.2.1 a) j

  change subst (Φ.act a) (ρ j) = subst ρ (Y.act a j) at h
  rw [h]
  exact subst_mem_span ρ hρ.1.1 _ ((Y.isLawHom_act a).1 j)

include hρ in

theorem subst_varpi_mem (G : MvPowerSeries (Fin 2) B) (hG : G ∈ Ideal.span (Set.range ρ)) :
    subst Φ.varpi G ∈ Ideal.span (Set.range ρ) := by
  refine span_stable ρ Φ.varpi Φ.isLawHom_varpi.hasSubst _ (fun j => ?_) G hG
  have h := congrFun hρ.2.2 j
  change subst Φ.varpi (ρ j) = subst ρ (Y.varpi j) at h
  rw [h]
  exact subst_mem_span ρ hρ.1.1 _ (Y.isLawHom_varpi.1 j)

noncomputable def inL (ρ : Series B) : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j)

noncomputable def inR (ρ : Series B) : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j)

include hρ in

theorem subst_law_mem (G : MvPowerSeries (Fin 2) B) (hG : G ∈ Ideal.span (Set.range ρ)) :
    subst Φ.F.toPowerSeries G ∈ Ideal.span (Set.range (inL ρ) ∪ Set.range (inR ρ)) := by
  refine span_stable ρ Φ.F.toPowerSeries Φ.F.hasSubst_toPowerSeries _ (fun i => ?_) G hG
  rw [hρ.1.2 i, ← Set.Sum.elim_range]
  have h0 : ∀ t, constantCoeff (Sum.elim (inL ρ) (inR ρ) t) = 0 := by
    rintro (j | j)
    · exact MvPowerSeries.constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _)
        (fun l => MvPowerSeries.constantCoeff_X _) (hρ.1.1 j)
    · exact MvPowerSeries.constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _)
        (fun l => MvPowerSeries.constantCoeff_X _) (hρ.1.1 j)
  exact subst_mem_span (Sum.elim (inL ρ) (inR ρ)) h0 _ (Y.F.constantCoeff_eq_zero i)

end Kernel

end P2mKA

open P2mKA in

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (Φ Y : FormalODModule p B)
    (ρ β : Series B) (hρ : FormalODModule.IsODHom Φ Y ρ) (hβ : FormalODModule.IsODHom Y Φ β)
    (N : ℕ) (hfac : β.comp ρ = Φ.act ((p : Zp2 p) ^ N)) :
    Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N))) ≤ Ideal.span (Set.range ρ) ∧
    (∀ (a : Zp2 p) (G : MvPowerSeries (Fin 2) B), G ∈ Ideal.span (Set.range ρ) →
      MvPowerSeries.subst (Φ.act a) G ∈ Ideal.span (Set.range ρ)) ∧
    (∀ G : MvPowerSeries (Fin 2) B, G ∈ Ideal.span (Set.range ρ) →
      MvPowerSeries.subst Φ.varpi G ∈ Ideal.span (Set.range ρ)) ∧
    (∀ G : MvPowerSeries (Fin 2) B, G ∈ Ideal.span (Set.range ρ) →
      MvPowerSeries.subst Φ.F.toPowerSeries G ∈
        Ideal.span (Set.range (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j)) ∪
          Set.range (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j)))) :=
  ⟨P2mKA.span_act_pow_le Φ Y ρ β hρ hβ N hfac, fun a G hG => P2mKA.subst_act_mem Φ Y ρ hρ a G hG,
    fun G hG => P2mKA.subst_varpi_mem Φ Y ρ hρ G hG, fun G hG => P2mKA.subst_law_mem Φ Y ρ hρ G hG⟩

end S_CerednikDrinfeld_FormalODModule_span_act_pow_le_span_and_subst_mem_span_of_isODHom_of_comp_eq_act_pow
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_span_act_pow_le_span_and_subst_mem_span_of_isODHom_of_comp_eq_act_pow (solution)
