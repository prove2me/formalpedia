-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_semilinear_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/42c52ffc-69a0-5ebf-a5bb-aa3ebe88abec

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_semilinear_tangent

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace B28QT

open CerednikDrinfeld CerednikDrinfeld.FormalODModule

variable {p : ℕ} [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B')

theorem lieVarpi_map (X : FormalODModule p B) (m : X.Lie) :
    (X.map f).lieVarpi (fun i => f (m i)) = fun i => f (X.lieVarpi m i) := by
  funext i
  simp only [FormalODModule.lieVarpi, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    MvFormalGroup.linearPart, Matrix.of_apply, FormalODModule.map_varpi, Series.map,
    MvPowerSeries.coeff_map, map_sum, map_mul]

def restr (S : Submodule B (Fin 2 → B)) (S' : Submodule B' (Fin 2 → B'))
    (h : ∀ m ∈ S, (fun i => f (m i)) ∈ S') : ↥S →ₛₗ[f] ↥S' where
  toFun m := ⟨fun i => f ((m : Fin 2 → B) i), h m m.2⟩
  map_add' m m' := by
    ext i
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
  map_smul' c m := by
    ext i
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]

@[scoped simp] theorem restr_apply_coe (S : Submodule B (Fin 2 → B)) (S' : Submodule B' (Fin 2 → B'))
    (h : ∀ m ∈ S, (fun i => f (m i)) ∈ S') (m : ↥S) (i : Fin 2) :
    ((restr f S S' h m : ↥S') : Fin 2 → B') i = f ((m : Fin 2 → B) i) := rfl

end B28QT
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_semilinear_tangent.B28QT"

open B28QT in
theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[p] B'] (ψ' : O →+* B')
    (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B') (hf : (f : B →+* B').comp ψ = ψ')
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (σ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (σ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q σ₀ σ₁)
    (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (σ₀' : Q'.T₀ ≃ₗ[B'] ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ')))
    (σ₁' : Q'.T₁ ≃ₗ[B'] ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ')))
    (hQ' : (t.map (f : B →+* B')).IsCartierQuadrupleVia ι hcΦ rΦ ψ' Q' σ₀' σ₁') :
    ∃ (τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀) (τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁),
      (Submodule.span B' (Set.range τ₀) = ⊤) ∧ (Submodule.span B' (Set.range τ₁) = ⊤) ∧
      (∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) ∧ (∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s)) ∧
      (∀ (s : Q.T₀) (i : Fin 2), ((σ₀' (τ₀ s) : ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i)) ∧
      (∀ (s : Q.T₁) (i : Fin 2), ((σ₁' (τ₁ s) : ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) i =
          f (((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i)) := by
  classical

  have hj : (f : B →+* B').comp (structureMap ι ψ) = structureMap ι ψ' := by
    show (f : B →+* B').comp (ψ.comp ι) = ψ'.comp ι
    rw [← RingHom.comp_assoc, hf]

  have hLie := CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image p (structureMap ι ψ) (f : B →+* B') t.X
  have hcpl : IsCompl (t.X.lieZero (structureMap ι ψ)) (t.X.lieOne (structureMap ι ψ)) := ht.1.1
  obtain ⟨⟨hle0, hle1⟩, heq⟩ := hLie
  obtain ⟨heq0, heq1⟩ := heq hcpl
  rw [hj] at hle0 hle1 heq0 heq1

  have hm0 : ∀ m ∈ t.X.lieZero (structureMap ι ψ),
      (fun i => (f : B →+* B') (m i)) ∈ (t.map (f : B →+* B')).X.lieZero (structureMap ι ψ') := fun m hm =>
    hle0 (Submodule.subset_span ⟨m, hm, rfl⟩)
  have hm1 : ∀ m ∈ t.X.lieOne (structureMap ι ψ),
      (fun i => (f : B →+* B') (m i)) ∈ (t.map (f : B →+* B')).X.lieOne (structureMap ι ψ') := fun m hm =>
    hle1 (Submodule.subset_span ⟨m, hm, rfl⟩)

  let F0 := restr (f : B →+* B') (t.X.lieZero (structureMap ι ψ)) ((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ')) hm0
  let F1 := restr (f : B →+* B') (t.X.lieOne (structureMap ι ψ)) ((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ')) hm1
  let τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀ :=
    { toFun := fun s => σ₀'.symm (F0 (σ₀ s))
      map_add' := fun s s' => by rw [map_add, map_add, map_add]
      map_smul' := fun c s => by rw [map_smul, LinearMap.map_smulₛₗ, map_smul] }
  let τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁ :=
    { toFun := fun s => σ₁'.symm (F1 (σ₁ s))
      map_add' := fun s s' => by rw [map_add, map_add, map_add]
      map_smul' := fun c s => by rw [map_smul, LinearMap.map_smulₛₗ, map_smul] }
  have hτ₀ : ∀ s, σ₀' (τ₀ s) = F0 (σ₀ s) := fun s => LinearEquiv.apply_symm_apply _ _
  have hτ₁ : ∀ s, σ₁' (τ₁ s) = F1 (σ₁ s) := fun s => LinearEquiv.apply_symm_apply _ _
  refine ⟨τ₀, τ₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [eq_top_iff]
    intro y _
    have hy : ((σ₀' y : ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) ∈
        Submodule.span B' ((fun m : t.X.Lie => fun i => (f : B →+* B') (m i)) '' (t.X.lieZero (structureMap ι ψ) : Set t.X.Lie)) := by
      rw [heq0]; exact (σ₀' y).2

    have key : ∀ w ∈ Submodule.span B' ((fun m : t.X.Lie => fun i => (f : B →+* B') (m i)) '' (t.X.lieZero (structureMap ι ψ) : Set t.X.Lie)),
        ∀ hw : w ∈ (t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'),
          σ₀'.symm ⟨w, hw⟩ ∈ Submodule.span B' (Set.range τ₀) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        intro hw'
        obtain ⟨m, hm, rfl⟩ := hw
        refine Submodule.subset_span ⟨σ₀.symm ⟨m, hm⟩, ?_⟩
        show σ₀'.symm (F0 (σ₀ (σ₀.symm ⟨m, hm⟩))) = _
        rw [LinearEquiv.apply_symm_apply]
        rfl
      | zero => intro hw'; have : (⟨0, hw'⟩ : ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))) = 0 := rfl; rw [this, map_zero]; exact Submodule.zero_mem _
      | add u w hu hw ihu ihw =>
        intro huw
        have hu' : u ∈ (t.map (f : B →+* B')).X.lieZero (structureMap ι ψ') := hle0 hu
        have hw' : w ∈ (t.map (f : B →+* B')).X.lieZero (structureMap ι ψ') := hle0 hw
        have : (⟨u + w, huw⟩ : ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))) = ⟨u, hu'⟩ + ⟨w, hw'⟩ := rfl
        rw [this, map_add]
        exact Submodule.add_mem _ (ihu hu') (ihw hw')
      | smul a w hw ihw =>
        intro haw
        have hw' : w ∈ (t.map (f : B →+* B')).X.lieZero (structureMap ι ψ') := hle0 hw
        have : (⟨a • w, haw⟩ : ↥((t.map (f : B →+* B')).X.lieZero (structureMap ι ψ'))) = a • ⟨w, hw'⟩ := rfl
        rw [this, map_smul]
        exact Submodule.smul_mem _ _ (ihw hw')
    have := key _ hy (σ₀' y).2
    rwa [LinearEquiv.symm_apply_apply] at this
  · rw [eq_top_iff]
    intro y _
    have hy : ((σ₁' y : ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))) : (t.map (f : B →+* B')).X.Lie) ∈
        Submodule.span B' ((fun m : t.X.Lie => fun i => (f : B →+* B') (m i)) '' (t.X.lieOne (structureMap ι ψ) : Set t.X.Lie)) := by
      rw [heq1]; exact (σ₁' y).2
    have key : ∀ w ∈ Submodule.span B' ((fun m : t.X.Lie => fun i => (f : B →+* B') (m i)) '' (t.X.lieOne (structureMap ι ψ) : Set t.X.Lie)),
        ∀ hw : w ∈ (t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'),
          σ₁'.symm ⟨w, hw⟩ ∈ Submodule.span B' (Set.range τ₁) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        intro hw'
        obtain ⟨m, hm, rfl⟩ := hw
        refine Submodule.subset_span ⟨σ₁.symm ⟨m, hm⟩, ?_⟩
        show σ₁'.symm (F1 (σ₁ (σ₁.symm ⟨m, hm⟩))) = _
        rw [LinearEquiv.apply_symm_apply]
        rfl
      | zero => intro hw'; have : (⟨0, hw'⟩ : ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))) = 0 := rfl; rw [this, map_zero]; exact Submodule.zero_mem _
      | add u w hu hw ihu ihw =>
        intro huw
        have hu' : u ∈ (t.map (f : B →+* B')).X.lieOne (structureMap ι ψ') := hle1 hu
        have hw' : w ∈ (t.map (f : B →+* B')).X.lieOne (structureMap ι ψ') := hle1 hw
        have : (⟨u + w, huw⟩ : ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))) = ⟨u, hu'⟩ + ⟨w, hw'⟩ := rfl
        rw [this, map_add]
        exact Submodule.add_mem _ (ihu hu') (ihw hw')
      | smul a w hw ihw =>
        intro haw
        have hw' : w ∈ (t.map (f : B →+* B')).X.lieOne (structureMap ι ψ') := hle1 hw
        have : (⟨a • w, haw⟩ : ↥((t.map (f : B →+* B')).X.lieOne (structureMap ι ψ'))) = a • ⟨w, hw'⟩ := rfl
        rw [this, map_smul]
        exact Submodule.smul_mem _ _ (ihw hw')
    have := key _ hy (σ₁' y).2
    rwa [LinearEquiv.symm_apply_apply] at this
  ·
    intro s
    apply σ₁'.injective
    apply Subtype.ext
    rw [hτ₁, hQ'.2.1 (τ₀ s), hτ₀]
    funext i
    rw [restr_apply_coe, hQ.2.1 s]
    show (f : B →+* B') (t.X.lieVarpi ((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i) =
      (t.X.map (f : B →+* B')).lieVarpi (fun i => (f : B →+* B') (((σ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i)) i
    rw [lieVarpi_map]
  · intro s
    apply σ₀'.injective
    apply Subtype.ext
    rw [hτ₀, hQ'.2.2.1 (τ₁ s), hτ₁]
    funext i
    rw [restr_apply_coe, hQ.2.2.1 s]
    show (f : B →+* B') (t.X.lieVarpi ((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i) =
      (t.X.map (f : B →+* B')).lieVarpi (fun i => (f : B →+* B') (((σ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i)) i
    rw [lieVarpi_map]
  · intro s i
    rw [hτ₀]; rfl
  · intro s i
    rw [hτ₁]; rfl

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_semilinear_tangent
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_semilinear_tangent (solution)
