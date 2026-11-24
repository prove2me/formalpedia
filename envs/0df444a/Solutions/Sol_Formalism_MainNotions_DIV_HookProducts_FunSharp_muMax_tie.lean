-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.FunSharp.muMax_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:53:04.329051+00:00
-- url     : https://prove2.me/submissions/8c647b0f-fa9b-48ea-a253-f329f2579074

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieSlope
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_NormAtEqSqrtMajAt
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HN_Rerealization_covol_rk_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open Module NumberField
noncomputable section
namespace Formalism.MainNotions.DIV.HookProducts.FunSharp
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem norm_realize_sq_eq_sum_majAt_re {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type, Formalism.HermitianLatticesTheory.majAt, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, Complex.mul_re]
  ring
private theorem slope_map_eq_of_norm_eq {G E F : Type} [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (H : AddSubgroup G) :
    Formalism.F.slope (H.map β).toIntSubmodule = Formalism.F.slope (H.map α).toIntSubmodule := by
  have hz : ∀ g, β g = 0 ↔ α g = 0 := fun g => by rw [← norm_eq_zero, hn g, norm_eq_zero]
  have key : ∀ {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
      (α₁ : G →+ E₁) (α₂ : G →+ E₂), (∀ g, ‖α₂ g‖ = ‖α₁ g‖) →
      DiscreteTopology (H.map α₁).toIntSubmodule → DiscreteTopology (H.map α₂).toIntSubmodule := by
    intro E₁ E₂ _ _ α₁ α₂ hn' hd
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at hd ⊢
    obtain ⟨ε, hε, h⟩ := hd
    refine ⟨ε, hε, fun y hy => ?_⟩
    obtain ⟨w, hw⟩ := y
    have hw' : w ∈ H.map α₂ := hw
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.1 hw'
    have hmem : α₁ g ∈ (H.map α₁).toIntSubmodule := AddSubgroup.mem_map_of_mem α₁ hg
    have h1 := h ⟨α₁ g, hmem⟩ (by
      have hy' := hy
      simp only [Subtype.dist_eq, ZeroMemClass.coe_zero, dist_zero_right] at hy' ⊢
      change ‖α₂ g‖ < ε at hy'
      change ‖α₁ g‖ < ε
      rw [← hn']
      exact hy')
    have h2 : α₁ g = 0 := congrArg Subtype.val h1
    have h3 : α₂ g = 0 := by rw [← norm_eq_zero, hn', h2, norm_zero]
    exact Subtype.ext h3
  have hd : DiscreteTopology (H.map β).toIntSubmodule ↔ DiscreteTopology (H.map α).toIntSubmodule :=
    ⟨key β α (fun g => (hn g).symm), key α β hn⟩
  by_cases hα : DiscreteTopology (H.map α).toIntSubmodule
  · obtain ⟨hc, hr⟩ := Formalism.HN.Rerealization.covol_rk_eq α β hn H hα (hd.2 hα)
    unfold Formalism.F.slope Formalism.F.deg
    rw [hc, hr]
  · have hβ : ¬ DiscreteTopology (H.map β).toIntSubmodule := fun h => hα (hd.1 h)
    unfold Formalism.F.slope Formalism.F.deg Formalism.F.covol
    rw [dif_neg hα, dif_neg hβ]
    simp
end Formalism.MainNotions.DIV.HookProducts.FunSharp
end
end

set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.FunSharp
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.DIV.HookProducts.FunSharp
theorem _root_.solution (A : Formalism.BasicNotions.HLat K) {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K))
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (e : (Fin n → K) ≃ₗ[K] A.V)
    (hlat : A.L = L.map ((e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K)))
    (hmet : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y) :
    Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)) XE L = A.muMax := by
  set f : (Fin n → K) →ₗ[𝓞 K] A.V := (e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K) with hf
  set g : A.V →ₗ[𝓞 K] (Fin n → K) := (e.symm : A.V →ₗ[K] (Fin n → K)).restrictScalars (𝓞 K) with hg
  have hgf : ∀ N : Submodule (𝓞 K) (Fin n → K), (N.map f).map g = N := by
    intro N
    rw [← Submodule.map_comp]
    have : g.comp f = LinearMap.id := by
      ext x; simp [hf, hg]
    rw [this, Submodule.map_id]
  have hfg : ∀ N : Submodule (𝓞 K) A.V, (N.map g).map f = N := by
    intro N
    rw [← Submodule.map_comp]
    have : f.comp g = LinearMap.id := by
      ext x; simp [hf, hg]
    rw [this, Submodule.map_id]
  have hn : ∀ x, ‖(Formalism.HermitianLatticesTheory.realize A.b A.X).comp f.toAddMonoidHom x‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE x‖ := by
    intro x
    have h1 := norm_realize_sq_eq_sum_majAt_re A.b A.X (e x)
    have h2 := norm_realize_sq_eq_sum_majAt_re (Pi.basisFun K (Fin n)) XE x
    simp_rw [hmet] at h1
    show ‖Formalism.HermitianLatticesTheory.realize A.b A.X (e x)‖ = _
    rw [← Real.sqrt_sq (norm_nonneg (Formalism.HermitianLatticesTheory.realize A.b A.X (e x))),
      ← Real.sqrt_sq (norm_nonneg (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE x)), h1, h2]
  have hslope : ∀ N : Submodule (𝓞 K) (Fin n → K),
      Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b A.X) (N.map f) =
        Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE) N := by
    intro N
    unfold Formalism.HN.slope Formalism.HN.zl
    rw [Submodule.map_toAddSubgroup, AddSubgroup.map_map]
    exact slope_map_eq_of_norm_eq _ _ hn N.toAddSubgroup
  have hne : ∀ N : Submodule (𝓞 K) (Fin n → K), N ≠ ⊥ → N.map f ≠ ⊥ := by
    intro N hN h
    apply hN
    rw [← hgf N, h, Submodule.map_bot]
  have hne' : ∀ N : Submodule (𝓞 K) A.V, N ≠ ⊥ → N.map g ≠ ⊥ := by
    intro N hN h
    apply hN
    rw [← hfg N, h, Submodule.map_bot]
  have hmu : Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE) L =
      Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize A.b A.X) A.L := by
    unfold Formalism.HN.muMax
    congr 1
    ext t
    constructor
    · rintro ⟨N, hNL, hN0, hs⟩
      refine ⟨N.map f, ?_, hne N hN0, (hslope N).trans hs⟩
      rw [hlat]; exact Submodule.map_mono hNL
    · rintro ⟨N, hNL, hN0, hs⟩
      refine ⟨N.map g, ?_, hne' N hN0, ?_⟩
      · rw [← hgf L]
        apply Submodule.map_mono
        rw [← hlat]; exact hNL
      · rw [← hslope, hfg]; exact hs
  unfold Formalism.BasicNotions.HLat.muMax Formalism.HN.muMaxDef
  rw [hmu]
end Formalism.MainNotions.DIV.HookProducts.FunSharp
