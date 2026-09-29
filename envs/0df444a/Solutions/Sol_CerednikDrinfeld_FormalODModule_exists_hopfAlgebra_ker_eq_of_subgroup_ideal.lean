-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_hopfAlgebra_ker_eq_of_subgroup_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9a120f6e-e336-58ad-978a-9c0f973ca039

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_of_subgroup_ideal

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open MvPowerSeries Function

universe u

namespace P2mHQ

variable {𝓞 : Type u} [CommRing 𝓞]

section Gen

private theorem map_span_le_radical {B C : Type*} [CommRing B] [Algebra 𝓞 B] [CommRing C] [Algebra 𝓞 C]
    (f : B →ₐ[𝓞] C) : ∀ s ∈ (⊥ : Ideal B), f s ∈ ((⊥ : Ideal C)).radical := by
  intro s hs
  rw [Submodule.mem_bot] at hs
  subst hs
  rw [map_zero]
  exact Ideal.zero_mem _

private theorem map_mem_radical {B C : Type*} [CommRing B] [Algebra 𝓞 B] [CommRing C] [Algebra 𝓞 C]
    (f : B →ₐ[𝓞] C) {b : B} (hb : b ∈ ((⊥ : Ideal B)).radical) :
    f b ∈ ((⊥ : Ideal C)).radical := by
  obtain ⟨n, hn⟩ := hb
  refine ⟨n, ?_⟩
  rw [Submodule.mem_bot] at hn
  rw [← map_pow, hn, map_zero]
  exact Ideal.zero_mem _

private theorem fg_span (B : Type*) [CommRing B] : ((⊥ : Ideal B)).FG := Submodule.fg_bot

end Gen

section Level

variable {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]
  {L : Type u} [CommRing L] [Algebra 𝓞 L] [Module.Finite 𝓞 L] [Module.Free 𝓞 L]
  (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L) (hπ : Surjective π) (hX : ∀ i, IsNilpotent (π (X i)))
  {I : Ideal (MvPowerSeries (Fin d) 𝓞)} (hker : RingHom.ker π = I)
  (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)
  (hmul : ∀ f ∈ I, subst Φ.toPowerSeries f ∈
    Ideal.span
      ((subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) '' (I : Set (MvPowerSeries (Fin d) 𝓞)) ∪
       (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) '' (I : Set (MvPowerSeries (Fin d) 𝓞))))

include hX in
omit [Φ.IsComm] [Module.Finite 𝓞 L] [Module.Free 𝓞 L] in

private theorem X_mem_radical (i : Fin d) : π (X i) ∈ ((⊥ : Ideal L)).radical := by
  obtain ⟨k, hk⟩ := hX i
  exact ⟨k, by rw [hk]; exact Ideal.zero_mem _⟩

include hX in
omit [Φ.IsComm] in

private theorem π_eq_adicEval (G : MvPowerSeries (Fin d) 𝓞) :
    π G = MvFormalGroup.adicEval ((⊥ : Ideal L)) (fun i => π (X i)) G :=
  MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical _ π (X_mem_radical π hX) G

private noncomputable def ξ : MvFormalGroup.Points Φ L ((⊥ : Ideal L)) :=
  ⟨fun i => π (X i), X_mem_radical π hX⟩

omit [Φ.IsComm] [Module.Free 𝓞 L] in
private theorem ξ_val (i : Fin d) : (ξ Φ π hX).val i = π (X i) := rfl

omit [Φ.IsComm] [Module.Finite 𝓞 L] [Module.Free 𝓞 L] in
include hπ in

private theorem algHom_ext {T : Type*} [Semiring T] [Algebra 𝓞 T] {f g : L →ₐ[𝓞] T}
    (h : ∀ a, f (π a) = g (π a)) : f = g := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨a, rfl⟩ := hπ y
  exact h a

private noncomputable def descend {T : Type*} [CommRing T] [Algebra 𝓞 T] (ψ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] T)
    (h : ∀ a, π a = 0 → ψ a = 0) : L →ₐ[𝓞] T :=
  (Ideal.Quotient.liftₐ (RingHom.ker π) ψ fun a ha => h a ha).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

omit [Φ.IsComm] [Module.Finite 𝓞 L] [Module.Free 𝓞 L] in
private theorem descend_apply {T : Type*} [CommRing T] [Algebra 𝓞 T] (ψ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] T)
    (h : ∀ a, π a = 0 → ψ a = 0) (a : MvPowerSeries (Fin d) 𝓞) : descend π hπ ψ h (π a) = ψ a := by
  rw [descend, AlgHom.comp_apply]
  have : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom (π a) = Ideal.Quotient.mk (RingHom.ker π) a := by
    rw [AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

private abbrev P (T : Type*) [CommRing T] := MvFormalGroup.Points Φ T ((⊥ : Ideal T))

private noncomputable def mp {T T' : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    [CommRing T'] [Algebra 𝓞 T'] [IsAdicComplete ((⊥ : Ideal T')) T'] (φ : T →ₐ[𝓞] T') :
    P Φ T →+ P Φ T' :=
  MvFormalGroup.Points.map φ (fg_span T) (map_span_le_radical φ)

private noncomputable def ptOf {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (φ : L →ₐ[𝓞] T) : P Φ T := mp Φ φ (ξ Φ π hX)

omit [Φ.IsComm] in
private theorem ptOf_val {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (φ : L →ₐ[𝓞] T) (j : Fin d) : (ptOf Φ π hX φ).val j = φ (π (X j)) := rfl

omit [Φ.IsComm] in
private theorem mp_ptOf {T T' : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    [CommRing T'] [Algebra 𝓞 T'] [IsAdicComplete ((⊥ : Ideal T')) T'] (ψ : T →ₐ[𝓞] T') (φ : L →ₐ[𝓞] T) :
    mp Φ ψ (ptOf Φ π hX φ) = ptOf Φ π hX (ψ.comp φ) := by
  ext j; rfl

omit [Φ.IsComm] in

private theorem ptOf_congr {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    {φ φ' : L →ₐ[𝓞] T} (h : ∀ j, φ (π (X j)) = φ' (π (X j))) : ptOf Φ π hX φ = ptOf Φ π hX φ' := by
  ext j; exact h j

private theorem apply_val_add {T T' : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    [CommRing T'] [Algebra 𝓞 T'] [IsAdicComplete ((⊥ : Ideal T')) T'] (ψ : T →ₐ[𝓞] T')
    (u v : P Φ T) (i : Fin d) : ψ ((u + v).val i) = (mp Φ ψ u + mp Φ ψ v).val i := by
  rw [← map_add]; rfl

omit [Φ.IsComm] in
private theorem apply_val {T T' : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    [CommRing T'] [Algebra 𝓞 T'] [IsAdicComplete ((⊥ : Ideal T')) T'] (ψ : T →ₐ[𝓞] T')
    (u : P Φ T) (i : Fin d) : ψ (u.val i) = (mp Φ ψ u).val i := rfl

private noncomputable def a₁ : P Φ (L ⊗[𝓞] L) :=
  ptOf Φ π hX (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L)
private noncomputable def a₂ : P Φ (L ⊗[𝓞] L) :=
  ptOf Φ π hX (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L)

omit [Φ.IsComm] in
private theorem a₁_val (j : Fin d) : (a₁ Φ π hX).val j = π (X j) ⊗ₜ[𝓞] (1 : L) := rfl
omit [Φ.IsComm] in
private theorem a₂_val (j : Fin d) : (a₂ Φ π hX).val j = (1 : L) ⊗ₜ[𝓞] π (X j) := rfl

omit [Φ.IsComm] in
private theorem mp_a₁ {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (ψ : L ⊗[𝓞] L →ₐ[𝓞] T) :
    mp Φ ψ (a₁ Φ π hX) = ptOf Φ π hX (ψ.comp (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L)) := by
  ext j; rfl
omit [Φ.IsComm] in
private theorem mp_a₂ {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (ψ : L ⊗[𝓞] L →ₐ[𝓞] T) :
    mp Φ ψ (a₂ Φ π hX) = ptOf Φ π hX (ψ.comp (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L)) := by
  ext j; rfl

omit [Φ.IsComm] [Module.Finite 𝓞 L] [Module.Free 𝓞 L] in

private theorem adicEval_a₁ (g : MvPowerSeries (Fin d) 𝓞) :
    MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (a₁ Φ π hX).val g = π g ⊗ₜ[𝓞] (1 : L) :=
  (MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ((⊥ : Ideal (L ⊗[𝓞] L)))
    ((Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L).comp π) (a₁ Φ π hX).mem_radical g).symm

omit [Φ.IsComm] [Module.Finite 𝓞 L] [Module.Free 𝓞 L] in

private theorem adicEval_a₂ (g : MvPowerSeries (Fin d) 𝓞) :
    MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (a₂ Φ π hX).val g = (1 : L) ⊗ₜ[𝓞] π g :=
  (MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ((⊥ : Ideal (L ⊗[𝓞] L)))
    ((Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L).comp π) (a₂ Φ π hX).mem_radical g).symm

private noncomputable def Δ₀ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L ⊗[𝓞] L :=
  MvFormalGroup.adicEvalAlgHom ((⊥ : Ideal (L ⊗[𝓞] L))) (a₁ Φ π hX + a₂ Φ π hX).mem_radical

private theorem Δ₀_apply (G : MvPowerSeries (Fin d) 𝓞) :
    Δ₀ Φ π hX G = MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (a₁ Φ π hX + a₂ Φ π hX).val G := by
  rw [Δ₀, MvFormalGroup.coe_adicEvalAlgHom]

include hker hmul in

private theorem Δ₀_vanish (G : MvPowerSeries (Fin d) 𝓞) (hG : π G = 0) : Δ₀ Φ π hX G = 0 := by
  rw [← RingHom.mem_ker, hker] at hG
  have hw : ∀ t, Sum.elim (a₁ Φ π hX).val (a₂ Φ π hX).val t ∈ ((⊥ : Ideal (L ⊗[𝓞] L))).radical := by
    rintro (j | j)
    · exact (a₁ Φ π hX).mem_radical j
    · exact (a₂ Φ π hX).mem_radical j
  have hl : HasSubst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hr : HasSubst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hvan : Ideal.span
      ((subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) '' (I : Set (MvPowerSeries (Fin d) 𝓞)) ∪
       (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) '' (I : Set (MvPowerSeries (Fin d) 𝓞))) ≤
      RingHom.ker (MvFormalGroup.adicEvalAlgHom ((⊥ : Ideal (L ⊗[𝓞] L))) hw) := by
    rw [Ideal.span_le]
    rintro _ (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
    · have hg0 : π g = 0 := by rw [← RingHom.mem_ker, hker]; exact hg
      rw [SetLike.mem_coe, RingHom.mem_ker, MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_subst _ hw hl g]
      have : (fun l => MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (Sum.elim (a₁ Φ π hX).val (a₂ Φ π hX).val)
          (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) = (a₁ Φ π hX).val := by
        funext l; rw [MvFormalGroup.adicEval_X]; rfl
      rw [this, adicEval_a₁, hg0, TensorProduct.zero_tmul]
    · have hg0 : π g = 0 := by rw [← RingHom.mem_ker, hker]; exact hg
      rw [SetLike.mem_coe, RingHom.mem_ker, MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_subst _ hw hr g]
      have : (fun l => MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (Sum.elim (a₁ Φ π hX).val (a₂ Φ π hX).val)
          (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) = (a₂ Φ π hX).val := by
        funext l; rw [MvFormalGroup.adicEval_X]; rfl
      rw [this, adicEval_a₂, hg0, TensorProduct.tmul_zero]
  have h := hvan (hmul G hG)
  rw [RingHom.mem_ker, MvFormalGroup.coe_adicEvalAlgHom,
    MvFormalGroup.adicEval_subst _ hw Φ.hasSubst_toPowerSeries G] at h
  rw [Δ₀_apply]

  have hval : (a₁ Φ π hX + a₂ Φ π hX).val =
      fun i => MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (Sum.elim (a₁ Φ π hX).val (a₂ Φ π hX).val)
        (Φ.toPowerSeries i) := funext fun i => MvFormalGroup.Points.val_add _ _ i
  rw [hval]
  exact h

private noncomputable def Δ : L →ₐ[𝓞] L ⊗[𝓞] L := descend π hπ (Δ₀ Φ π hX) (Δ₀_vanish Φ π hX hker hmul)

private theorem Δ_π (G : MvPowerSeries (Fin d) 𝓞) : Δ Φ π hπ hX hker hmul (π G) = Δ₀ Φ π hX G := descend_apply π hπ _ _ G

private theorem Δ_πX (i : Fin d) : Δ Φ π hπ hX hker hmul (π (X i)) = (a₁ Φ π hX + a₂ Φ π hX).val i := by
  rw [Δ_π, Δ₀_apply, MvFormalGroup.adicEval_X]

private theorem ptOf_Δ : ptOf Φ π hX (Δ Φ π hπ hX hker hmul) = a₁ Φ π hX + a₂ Φ π hX := by
  ext i; exact Δ_πX Φ π hπ hX hker hmul i

private noncomputable def ε₀ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] 𝓞 :=
  { MvPowerSeries.constantCoeff with commutes' := fun c => MvPowerSeries.constantCoeff_C c }

private theorem ε₀_apply (G : MvPowerSeries (Fin d) 𝓞) : ε₀ (𝓞 := 𝓞) (d := d) G = MvPowerSeries.constantCoeff G := rfl

include hker hunit in
private theorem ε₀_vanish (G : MvPowerSeries (Fin d) 𝓞) (hG : π G = 0) : ε₀ G = 0 := by
  rw [← RingHom.mem_ker, hker] at hG
  exact hunit G hG

private noncomputable def ε : L →ₐ[𝓞] 𝓞 := descend π hπ ε₀ (ε₀_vanish π hker hunit)

private theorem ε_π (G : MvPowerSeries (Fin d) 𝓞) : ε π hπ hker hunit (π G) = MvPowerSeries.constantCoeff G :=
  descend_apply π hπ _ _ G

private theorem ε_πX (i : Fin d) : ε π hπ hker hunit (π (X i)) = 0 := by rw [ε_π, constantCoeff_X]

private noncomputable def S₀ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L :=
  MvFormalGroup.adicEvalAlgHom ((⊥ : Ideal L)) (-ξ Φ π hX).mem_radical

private theorem S₀_apply (G : MvPowerSeries (Fin d) 𝓞) :
    S₀ Φ π hX G = MvFormalGroup.adicEval ((⊥ : Ideal L)) (-ξ Φ π hX).val G := by
  rw [S₀, MvFormalGroup.coe_adicEvalAlgHom]

include hπ in
private theorem algHom_ext_pt {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    {f g : L →ₐ[𝓞] T} (U V : P Φ T) (hU : ∀ i, f (π (X i)) = U.val i) (hV : ∀ i, g (π (X i)) = V.val i)
    (hUV : U = V) : f = g := by
  subst hUV
  refine algHom_ext π hπ fun G => ?_
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ((⊥ : Ideal T)) (f.comp π)
      (fun i => by rw [AlgHom.comp_apply, hU]; exact U.mem_radical i) G,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ((⊥ : Ideal T)) (g.comp π)
      (fun i => by rw [AlgHom.comp_apply, hV]; exact U.mem_radical i) G]
  congr 1
  funext i
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hU, hV]

private theorem ptOf_eq_zero {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    {φ : L →ₐ[𝓞] T} (h : ∀ j, φ (π (X j)) = 0) : ptOf Φ π hX φ = 0 := by
  ext j; exact h j

private theorem ptOf_id : ptOf Φ π hX (AlgHom.id 𝓞 L) = ξ Φ π hX := by
  ext j; rfl

private theorem ptOf_comp_Δ {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete ((⊥ : Ideal T)) T]
    (φ : L ⊗[𝓞] L →ₐ[𝓞] T) :
    ptOf Φ π hX (φ.comp (Δ Φ π hπ hX hker hmul)) =
      ptOf Φ π hX (φ.comp (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L)) +
        ptOf Φ π hX (φ.comp (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L)) := by
  rw [← mp_ptOf, ptOf_Δ, map_add, mp_a₁, mp_a₂]

section Axioms

private theorem coassoc :
    (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 L L L).toAlgHom.comp
        ((Algebra.TensorProduct.map (Δ Φ π hπ hX hker hmul) (AlgHom.id 𝓞 L)).comp (Δ Φ π hπ hX hker hmul)) =
      (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (Δ Φ π hπ hX hker hmul)).comp (Δ Φ π hπ hX hker hmul) := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 L L L).toAlgHom
      (mp Φ (Algebra.TensorProduct.map (Δ Φ π hπ hX hker hmul) (AlgHom.id 𝓞 L)) (a₁ Φ π hX) +
        mp Φ (Algebra.TensorProduct.map (Δ Φ π hπ hX hker hmul) (AlgHom.id 𝓞 L)) (a₂ Φ π hX)))
    (mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (Δ Φ π hπ hX hker hmul)) (a₁ Φ π hX) +
      mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (Δ Φ π hπ hX hker hmul)) (a₂ Φ π hX))
    (fun i => ?_) (fun i => ?_) ?_
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, Δ_πX]
    exact (congrArg _ (apply_val_add Φ _ _ _ i)).trans (apply_val Φ _ _ i)
  · rw [AlgHom.comp_apply, Δ_πX]
    exact apply_val_add Φ _ _ _ i
  ·
    rw [map_add, mp_a₁, mp_a₂, mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft,
      Algebra.TensorProduct.map_comp_includeRight, Algebra.TensorProduct.map_comp_includeLeft,
      Algebra.TensorProduct.map_comp_includeRight, ptOf_comp_Δ, map_add, mp_ptOf, mp_ptOf, mp_ptOf,
      AlgHom.comp_id, AlgHom.comp_id, ptOf_comp_Δ, add_assoc]

    congr 1

private theorem rTensor_counit :
    (Algebra.TensorProduct.map (ε π hπ hker hunit) (AlgHom.id 𝓞 L)).comp (Δ Φ π hπ hX hker hmul) =
      (Algebra.TensorProduct.lid 𝓞 L).symm.toAlgHom := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.map (ε π hπ hker hunit) (AlgHom.id 𝓞 L)) (a₁ Φ π hX) +
      mp Φ (Algebra.TensorProduct.map (ε π hπ hker hunit) (AlgHom.id 𝓞 L)) (a₂ Φ π hX))
    (ptOf Φ π hX (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] 𝓞 ⊗[𝓞] L))
    (fun i => ?_) (fun i => rfl) ?_
  · rw [AlgHom.comp_apply, Δ_πX]
    exact apply_val_add Φ _ _ _ i
  · rw [mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeRight,
      AlgHom.comp_id, ptOf_eq_zero Φ π hX (fun j => by rw [AlgHom.comp_apply, ε_πX, map_zero]), zero_add]

private theorem lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (ε π hπ hker hunit)).comp (Δ Φ π hπ hX hker hmul) =
      (Algebra.TensorProduct.rid 𝓞 𝓞 L).symm.toAlgHom := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (ε π hπ hker hunit)) (a₁ Φ π hX) +
      mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (ε π hπ hker hunit)) (a₂ Φ π hX))
    (ptOf Φ π hX (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] 𝓞))
    (fun i => ?_) (fun i => rfl) ?_
  · rw [AlgHom.comp_apply, Δ_πX]
    exact apply_val_add Φ _ _ _ i
  · rw [mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeRight,
      AlgHom.comp_id,
      ptOf_eq_zero Φ π hX (φ := (Algebra.TensorProduct.includeRight : 𝓞 →ₐ[𝓞] L ⊗[𝓞] 𝓞).comp (ε π hπ hker hunit))
        (fun j => by rw [AlgHom.comp_apply, ε_πX, map_zero]), add_zero]

@[reducible] private noncomputable def bialgebra : Bialgebra 𝓞 L :=
  Bialgebra.ofAlgHom (Δ Φ π hπ hX hker hmul) (ε π hπ hker hunit) (coassoc Φ π hπ hX hker hmul)
    (rTensor_counit Φ π hπ hX hker hunit hmul) (lTensor_counit Φ π hπ hX hker hunit hmul)

private noncomputable def τ : L ⊗[𝓞] L →ₐ[L] L ⊗[𝓞] L :=
  Algebra.TensorProduct.lift (Algebra.ofId L (L ⊗[𝓞] L)) (Δ Φ π hπ hX hker hmul) (fun _ _ => Commute.all _ _)

private theorem τ_tmul (a c : L) : τ Φ π hπ hX hker hmul (a ⊗ₜ[𝓞] c) = (a ⊗ₜ[𝓞] (1 : L)) * Δ Φ π hπ hX hker hmul c := by
  rw [τ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self_apply]

private theorem mp_τ_a₁ : mp Φ ((τ Φ π hπ hX hker hmul).restrictScalars 𝓞) (a₁ Φ π hX) = a₁ Φ π hX := by
  rw [mp_a₁]
  exact ptOf_congr Φ π hX fun j => by
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeLeft_apply, τ_tmul, map_one,
      mul_one]

private theorem mp_τ_a₂ :
    mp Φ ((τ Φ π hπ hX hker hmul).restrictScalars 𝓞) (a₂ Φ π hX) = a₁ Φ π hX + a₂ Φ π hX := by
  rw [mp_a₂, ← ptOf_Δ Φ π hπ hX hker hmul]
  exact ptOf_congr Φ π hX fun j => by
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply, τ_tmul,
      ← Algebra.TensorProduct.one_def, one_mul]

private theorem τ_adicEval (g : MvPowerSeries (Fin d) 𝓞) :
    τ Φ π hπ hX hker hmul (MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (a₂ Φ π hX + -a₁ Φ π hX).val g) =
      (1 : L) ⊗ₜ[𝓞] π g := by
  have hP : mp Φ ((τ Φ π hπ hX hker hmul).restrictScalars 𝓞) (a₂ Φ π hX + -a₁ Φ π hX) = a₂ Φ π hX := by
    rw [map_add, map_neg, mp_τ_a₁, mp_τ_a₂, add_comm (a₁ Φ π hX) (a₂ Φ π hX), add_neg_cancel_right]
  have h := MvFormalGroup.map_adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) ((⊥ : Ideal (L ⊗[𝓞] L)))
    ((τ Φ π hπ hX hker hmul).restrictScalars 𝓞) (fg_span _) (map_span_le_radical _)
    (a₂ Φ π hX + -a₁ Φ π hX).mem_radical g
  have hv : (fun s => (τ Φ π hπ hX hker hmul).restrictScalars 𝓞 ((a₂ Φ π hX + -a₁ Φ π hX).val s)) =
      (mp Φ ((τ Φ π hπ hX hker hmul).restrictScalars 𝓞) (a₂ Φ π hX + -a₁ Φ π hX)).val := rfl
  rw [hv, hP, adicEval_a₂, AlgHom.restrictScalars_apply] at h
  exact h

include hπ in

private theorem τ_surjective : Surjective (τ Φ π hπ hX hker hmul) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a c =>
    obtain ⟨g, rfl⟩ := hπ c
    refine ⟨(a ⊗ₜ[𝓞] (1 : L)) *
      MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (a₂ Φ π hX + -a₁ Φ π hX).val g, ?_⟩
    rw [map_mul, τ_adicEval, τ_tmul, map_one, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

private theorem τ_injective : Injective (τ Φ π hπ hX hker hmul) :=
  OrzechProperty.injective_of_surjective_endomorphism (τ Φ π hπ hX hker hmul).toLinearMap
    (τ_surjective Φ π hπ hX hker hmul)

include hπ hker hunit hmul in

private theorem S₀_vanish (G : MvPowerSeries (Fin d) 𝓞) (hG : π G = 0) : S₀ Φ π hX G = 0 := by
  have hz : MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) (a₂ Φ π hX + -a₁ Φ π hX).val G = 0 := by
    apply τ_injective Φ π hπ hX hker hmul
    rw [map_zero, τ_adicEval, hG, TensorProduct.tmul_zero]
  let ψ₀ : L ⊗[𝓞] L →ₐ[𝓞] L :=
    Algebra.TensorProduct.lift (AlgHom.id 𝓞 L) ((Algebra.ofId 𝓞 L).comp (ε π hπ hker hunit)) (fun _ _ => Commute.all _ _)
  have hψ₀ : ∀ a c : L, ψ₀ (a ⊗ₜ[𝓞] c) = a * algebraMap 𝓞 L (ε π hπ hker hunit c) := fun a c => by
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply]
  have hP : mp Φ ψ₀ (a₂ Φ π hX + -a₁ Φ π hX) = -ξ Φ π hX := by
    rw [map_add, map_neg, mp_a₁, mp_a₂]
    have h1 : ptOf Φ π hX (ψ₀.comp (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L)) = 0 :=
      ptOf_eq_zero Φ π hX fun j => by
        rw [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply, hψ₀, ε_πX, map_zero, mul_zero]
    have h2 : ptOf Φ π hX (ψ₀.comp (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L)) = ξ Φ π hX := by
      rw [← ptOf_id Φ π hX]
      exact ptOf_congr Φ π hX fun j => by
        rw [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, hψ₀, map_one, map_one, mul_one,
          AlgHom.id_apply]
    rw [h1, h2, zero_add]
  have h := MvFormalGroup.map_adicEval ((⊥ : Ideal (L ⊗[𝓞] L))) ((⊥ : Ideal L)) ψ₀ (fg_span _)
    (map_span_le_radical _) (a₂ Φ π hX + -a₁ Φ π hX).mem_radical G
  have hv : (fun s => ψ₀ ((a₂ Φ π hX + -a₁ Φ π hX).val s)) = (mp Φ ψ₀ (a₂ Φ π hX + -a₁ Φ π hX)).val := rfl
  rw [hz, map_zero, hv, hP] at h
  rw [S₀_apply]
  exact h.symm

private noncomputable def S : L →ₐ[𝓞] L := descend π hπ (S₀ Φ π hX) (S₀_vanish Φ π hπ hX hker hunit hmul)

private theorem S_π (G : MvPowerSeries (Fin d) 𝓞) : S Φ π hπ hX hker hunit hmul (π G) = S₀ Φ π hX G := descend_apply π hπ _ _ G

private theorem ptOf_S : ptOf Φ π hX (S Φ π hπ hX hker hunit hmul) = -ξ Φ π hX := by
  ext j
  rw [ptOf_val, S_π, S₀_apply, MvFormalGroup.adicEval_X]

private theorem antipode_right :
    (Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        ((Algebra.TensorProduct.map (S Φ π hπ hX hker hunit hmul) (AlgHom.id 𝓞 L)).comp (Δ Φ π hπ hX hker hmul)) =
      (Algebra.ofId 𝓞 L).comp (ε π hπ hker hunit) := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.lmul' 𝓞 (S := L))
      (mp Φ (Algebra.TensorProduct.map (S Φ π hπ hX hker hunit hmul) (AlgHom.id 𝓞 L)) (a₁ Φ π hX) +
        mp Φ (Algebra.TensorProduct.map (S Φ π hπ hX hker hunit hmul) (AlgHom.id 𝓞 L)) (a₂ Φ π hX)))
    (0 : P Φ L) (fun i => ?_) (fun i => ?_) ?_
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, Δ_πX]
    exact (congrArg _ (apply_val_add Φ _ _ _ i)).trans (apply_val Φ _ _ i)
  · rw [AlgHom.comp_apply, ε_πX, map_zero, MvFormalGroup.Points.val_zero]
  · rw [map_add, mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft,
      Algebra.TensorProduct.map_comp_includeRight, mp_ptOf, mp_ptOf, AlgHom.comp_id]
    have h1 : ptOf Φ π hX ((Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        ((Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L).comp (S Φ π hπ hX hker hunit hmul))) = -ξ Φ π hX := by
      rw [← ptOf_S Φ π hπ hX hker hunit hmul]
      exact ptOf_congr Φ π hX fun j => by
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lmul'_apply_tmul,
          mul_one]
    have h2 : ptOf Φ π hX ((Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L)) = ξ Φ π hX := by
      rw [← ptOf_id Φ π hX]
      exact ptOf_congr Φ π hX fun j => by
        simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
    rw [h1, h2, neg_add_cancel]

private theorem antipode_left :
    (Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        ((Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (S Φ π hπ hX hker hunit hmul)).comp (Δ Φ π hπ hX hker hmul)) =
      (Algebra.ofId 𝓞 L).comp (ε π hπ hker hunit) := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.lmul' 𝓞 (S := L))
      (mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (S Φ π hπ hX hker hunit hmul)) (a₁ Φ π hX) +
        mp Φ (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (S Φ π hπ hX hker hunit hmul)) (a₂ Φ π hX)))
    (0 : P Φ L) (fun i => ?_) (fun i => ?_) ?_
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, Δ_πX]
    exact (congrArg _ (apply_val_add Φ _ _ _ i)).trans (apply_val Φ _ _ i)
  · rw [AlgHom.comp_apply, ε_πX, map_zero, MvFormalGroup.Points.val_zero]
  · rw [map_add, mp_a₁, mp_a₂, Algebra.TensorProduct.map_comp_includeLeft,
      Algebra.TensorProduct.map_comp_includeRight, mp_ptOf, mp_ptOf, AlgHom.comp_id]
    have h1 : ptOf Φ π hX ((Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        (Algebra.TensorProduct.includeLeft : L →ₐ[𝓞] L ⊗[𝓞] L)) = ξ Φ π hX := by
      rw [← ptOf_id Φ π hX]
      exact ptOf_congr Φ π hX fun j => by
        simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
    have h2 : ptOf Φ π hX ((Algebra.TensorProduct.lmul' 𝓞 (S := L)).comp
        ((Algebra.TensorProduct.includeRight : L →ₐ[𝓞] L ⊗[𝓞] L).comp (S Φ π hπ hX hker hunit hmul))) = -ξ Φ π hX := by
      rw [← ptOf_S Φ π hπ hX hker hunit hmul]
      exact ptOf_congr Φ π hX fun j => by
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
    rw [h1, h2, add_neg_cancel]

private theorem comm_Δ :
    (Algebra.TensorProduct.comm 𝓞 L L).toAlgHom.comp (Δ Φ π hπ hX hker hmul) = Δ Φ π hπ hX hker hmul := by
  refine algHom_ext_pt Φ π hπ
    (mp Φ (Algebra.TensorProduct.comm 𝓞 L L).toAlgHom (a₁ Φ π hX) +
      mp Φ (Algebra.TensorProduct.comm 𝓞 L L).toAlgHom (a₂ Φ π hX))
    (a₁ Φ π hX + a₂ Φ π hX) (fun i => ?_) (fun i => Δ_πX Φ π hπ hX hker hmul i) ?_
  · rw [AlgHom.comp_apply, Δ_πX]
    exact apply_val_add Φ _ _ _ i
  · rw [mp_a₁, mp_a₂, add_comm, a₁, a₂]

    congr 1

@[reducible] private noncomputable def hopfAlgebra : HopfAlgebra 𝓞 L :=
  letI := bialgebra Φ π hπ hX hker hunit hmul
  { antipode := (S Φ π hπ hX hker hunit hmul).toLinearMap
    mul_antipode_rTensor_comul := by
      have hrT : (Algebra.TensorProduct.map (S Φ π hπ hX hker hunit hmul) (AlgHom.id 𝓞 L)).toLinearMap =
          (S Φ π hπ hX hker hunit hmul).toLinearMap.rTensor L := TensorProduct.ext' fun _ _ => rfl
      have h := congrArg AlgHom.toLinearMap (antipode_right Φ π hπ hX hker hunit hmul)
      rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap, hrT,
        AlgHom.comp_toLinearMap] at h
      exact h
    mul_antipode_lTensor_comul := by
      have hlT : (Algebra.TensorProduct.map (AlgHom.id 𝓞 L) (S Φ π hπ hX hker hunit hmul)).toLinearMap =
          (S Φ π hπ hX hker hunit hmul).toLinearMap.lTensor L := TensorProduct.ext' fun _ _ => rfl
      have h := congrArg AlgHom.toLinearMap (antipode_left Φ π hπ hX hker hunit hmul)
      rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap, hlT,
        AlgHom.comp_toLinearMap] at h
      exact h }

private theorem isCocomm : @Coalgebra.IsCocomm 𝓞 L _ _ _ (hopfAlgebra Φ π hπ hX hker hunit hmul).toCoalgebra :=
  letI := hopfAlgebra Φ π hπ hX hker hunit hmul
  ⟨congrArg AlgHom.toLinearMap (comm_Δ Φ π hπ hX hker hmul)⟩

private theorem comul_πX (i : Fin d) :
    (hopfAlgebra Φ π hπ hX hker hunit hmul).comul (π (X i)) =
      MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L)))
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : L)) (fun j => (1 : L) ⊗ₜ[𝓞] π (X j))) (Φ.toPowerSeries i) := by
  change Δ Φ π hπ hX hker hmul (π (X i)) = _
  rw [Δ_πX]
  rfl

private theorem counit_π (G : MvPowerSeries (Fin d) 𝓞) :
    (hopfAlgebra Φ π hπ hX hker hunit hmul).counit (π G) = MvPowerSeries.constantCoeff G :=
  ε_π π hπ hker hunit G

end Axioms

end Level

section Main

variable {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]
  {M : Type u} [CommRing M] [Algebra 𝓞 M] [Module.Finite 𝓞 M] [Module.Free 𝓞 M]
  (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] M) (hπ : Surjective π) (hX : ∀ i, IsNilpotent (π (X i)))
  {I : Ideal (MvPowerSeries (Fin d) 𝓞)} (hker : RingHom.ker π = I)
  (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)
  (hmul : ∀ f ∈ I, subst Φ.toPowerSeries f ∈
    Ideal.span
      ((subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) '' (I : Set (MvPowerSeries (Fin d) 𝓞)) ∪
       (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) '' (I : Set (MvPowerSeries (Fin d) 𝓞))))

include hπ hX hker hunit hmul in
theorem main :
    ∃ (L : Type u) (_ : CommRing L) (_ : HopfAlgebra 𝓞 L) (_ : Coalgebra.IsCocomm 𝓞 L)
      (_ : Module.Free 𝓞 L) (_ : Module.Finite 𝓞 L) (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L),
      Function.Surjective π ∧
      RingHom.ker π = I ∧
      (∀ i, IsNilpotent (π (X i))) ∧
      (∀ G, π G = MvFormalGroup.adicEval ((⊥ : Ideal L)) (fun i => π (X i)) G) ∧
      (∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
        MvFormalGroup.adicEval ((⊥ : Ideal (L ⊗[𝓞] L)))
          (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : L)) (fun j => (1 : L) ⊗ₜ[𝓞] π (X j)))
          (Φ.toPowerSeries i)) ∧
      (∀ i, Coalgebra.counit (R := 𝓞) (π (X i)) = 0) ∧
      (∀ G, Coalgebra.counit (R := 𝓞) (π G) = MvPowerSeries.constantCoeff G) := by
  exact ⟨M, inferInstance, hopfAlgebra Φ π hπ hX hker hunit hmul, isCocomm Φ π hπ hX hker hunit hmul, inferInstance, inferInstance,
    π, hπ, hker, hX, π_eq_adicEval π hX, comul_πX Φ π hπ hX hker hunit hmul,
    ε_πX π hπ hker hunit, counit_π Φ π hπ hX hker hunit hmul⟩

end Main

end P2mHQ

open P2mHQ CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hfree : Module.Free B (MvPowerSeries (Fin 2) B ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)))) :
    ∃ (L : Type) (_ : CommRing L) (_ : HopfAlgebra B L) (_ : Coalgebra.IsCocomm B L)
      (_ : Module.Free B L) (_ : Module.Finite B L) (π : MvPowerSeries (Fin 2) B →ₐ[B] L),
      Function.Surjective π ∧
      RingHom.ker π = I ∧
      (∀ i, IsNilpotent (π (MvPowerSeries.X i))) ∧
      (∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G) ∧
      (∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (X.F.toPowerSeries i)) ∧
      (∀ i, Coalgebra.counit (R := B) (π (MvPowerSeries.X i)) = 0) ∧
      (∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G) := by
  haveI := hfin
  haveI := hfree
  have hXn : ∀ i, IsNilpotent ((Ideal.Quotient.mkₐ B I) (MvPowerSeries.X i)) := by
    obtain ⟨q, hq⟩ := hnil
    intro i
    exact ⟨q, by rw [← map_pow, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hq i⟩
  exact main X.F (Ideal.Quotient.mkₐ B I) (Ideal.Quotient.mkₐ_surjective B I) hXn (Ideal.Quotient.mkₐ_ker B I)
    hunit hmul

end S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_of_subgroup_ideal
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_of_subgroup_ideal (solution)
