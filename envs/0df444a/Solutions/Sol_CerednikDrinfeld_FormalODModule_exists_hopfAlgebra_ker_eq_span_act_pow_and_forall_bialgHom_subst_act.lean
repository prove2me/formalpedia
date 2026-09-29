-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/35b2f815-9198-518d-b617-355c907da413

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_exists_hopfAlgebra_surjective_ker_eq_span_nthSeries_comul_eq_adicEval_bot_of_isNilpotent
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff X subst_X)

namespace P2mHKA

section Adic

variable {B : Type} [CommRing B] {σ : Type} [Finite σ]

noncomputable def constantCoeffAlgHom : MvPowerSeries σ B →ₐ[B] B :=
  { (MvPowerSeries.constantCoeff : MvPowerSeries σ B →+* B) with
    commutes' := fun r => MvPowerSeries.constantCoeff_C r }

@[scoped simp] theorem constantCoeffAlgHom_apply (G : MvPowerSeries σ B) :
    constantCoeffAlgHom (B := B) (σ := σ) G = constantCoeff G := rfl

theorem adicEval_zero_eq {T : Type} [CommRing T] [Algebra B T] (G : MvPowerSeries σ B) :
    MvFormalGroup.adicEval (⊥ : Ideal T) (fun _ : σ => (0 : T)) G = algebraMap B T (constantCoeff G) := by
  let ψ : MvPowerSeries σ B →ₐ[B] T := (Algebra.ofId B T).comp constantCoeffAlgHom
  have hψ : ∀ s : σ, ψ (X s) ∈ ((⊥ : Ideal T)).radical := by
    intro s
    show algebraMap B T (constantCoeff (X s : MvPowerSeries σ B)) ∈ ((⊥ : Ideal T)).radical
    rw [MvPowerSeries.constantCoeff_X, map_zero]
    exact Ideal.zero_mem _
  have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal T) ψ hψ G
  have hx : (fun s : σ => ψ (X s)) = fun _ => (0 : T) := by
    funext s
    show algebraMap B T (constantCoeff (X s : MvPowerSeries σ B)) = 0
    rw [MvPowerSeries.constantCoeff_X, map_zero]
  rw [hx] at h
  exact h.symm

end Adic

section Descend

variable {B : Type} [CommRing B] {d : ℕ} (F : MvFormalGroup d B)
  {L : Type} [CommRing L] [HopfAlgebra B L]
  (π : MvPowerSeries (Fin d) B →ₐ[B] L) (hπ : Function.Surjective π)
  (hX : ∀ i, IsNilpotent (π (X i)))
  (hΔ : ∀ i, Coalgebra.comul (R := B) (π (X i)) =
    MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
      (Sum.elim (fun j => π (X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (X j))) (F.toPowerSeries i))
  (hε : ∀ G, Coalgebra.counit (R := B) (π G) = constantCoeff G)
  (s : Fin d → MvPowerSeries (Fin d) B) (hs0 : ∀ i, constantCoeff (s i) = 0)
  (hker : ∀ G, π G = 0 → π (subst s G) = 0)
  (hlaw : ∀ i, subst F.toPowerSeries (s i) =
    subst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) B)) (s j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) B)) (s j)))
      (F.toPowerSeries i))

include hX in
theorem X_mem_radical (i : Fin d) : π (X i) ∈ ((⊥ : Ideal L)).radical := by
  obtain ⟨k, hk⟩ := hX i
  exact ⟨k, by rw [hk]; exact Ideal.zero_mem _⟩

include hX in

theorem π_eq_adicEval (G : MvPowerSeries (Fin d) B) :
    π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (X i)) G :=
  MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical _ π (X_mem_radical π hX) G

noncomputable def rhoTilde : MvPowerSeries (Fin d) B →ₐ[B] L :=
  π.comp (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs0))

theorem rhoTilde_apply (G : MvPowerSeries (Fin d) B) : rhoTilde π s hs0 G = π (subst s G) := by
  show π (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs0) G) = _
  rw [MvPowerSeries.substAlgHom_apply]

noncomputable def rho : L →ₐ[B] L :=
  (Ideal.Quotient.liftₐ (RingHom.ker π) (rhoTilde π s hs0) fun a ha => by
      rw [rhoTilde_apply]; exact hker a ha).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

theorem rho_π (G : MvPowerSeries (Fin d) B) : rho π hπ s hs0 hker (π G) = π (subst s G) := by
  rw [rho, AlgHom.comp_apply]
  have : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom (π G) = Ideal.Quotient.mk (RingHom.ker π) G := by
    rw [AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_eq]
    rfl
  rw [this]
  show rhoTilde π s hs0 G = _
  exact rhoTilde_apply π s hs0 G

include hX hs0 in

theorem π_s_mem_radical (j : Fin d) : π (s j) ∈ ((⊥ : Ideal L)).radical := by
  rw [π_eq_adicEval π hX]
  exact MvFormalGroup.adicEval_mem_radical _ (X_mem_radical π hX) (hs0 j)

include hX hε in

theorem counit_rho : (Bialgebra.counitAlgHom B L).comp (rho π hπ s hs0 hker) = Bialgebra.counitAlgHom B L := by
  apply AlgHom.ext
  intro y
  obtain ⟨G, rfl⟩ := hπ y
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, rho_π, hε, hε]

  have h1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal B)
    ((constantCoeffAlgHom (B := B) (σ := Fin d)).comp (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs0)))
    (fun i => by
      show constantCoeff (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs0) (X i)) ∈ ((⊥ : Ideal B)).radical
      rw [MvPowerSeries.substAlgHom_apply, subst_X (hasSubst_of_constantCoeff_zero hs0), hs0]
      exact Ideal.zero_mem _) G
  have hx : (fun i : Fin d => ((constantCoeffAlgHom (B := B) (σ := Fin d)).comp
      (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs0))) (X i)) = fun _ => (0 : B) := by
    funext i
    show constantCoeff (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs0) (X i)) = 0
    rw [MvPowerSeries.substAlgHom_apply, subst_X (hasSubst_of_constantCoeff_zero hs0), hs0]
  rw [hx, adicEval_zero_eq] at h1
  have h1' : constantCoeff (subst s G) = constantCoeff G := by
    have := h1
    rw [AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply, constantCoeffAlgHom_apply] at this
    rw [this]
    rfl
  rw [h1']

end Descend

end P2mHKA
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act.P2mHKA"

namespace P2mHKA

section Comul

variable {B : Type} [CommRing B] {d : ℕ} (F : MvFormalGroup d B)
  {L : Type} [CommRing L] [HopfAlgebra B L]
  (π : MvPowerSeries (Fin d) B →ₐ[B] L) (hπ : Function.Surjective π)
  (hX : ∀ i, IsNilpotent (π (X i)))
  (hΔ : ∀ i, Coalgebra.comul (R := B) (π (X i)) =
    MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
      (Sum.elim (fun j => π (X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (X j))) (F.toPowerSeries i))
  (hε : ∀ G, Coalgebra.counit (R := B) (π G) = constantCoeff G)
  (s : Fin d → MvPowerSeries (Fin d) B) (hs0 : ∀ i, constantCoeff (s i) = 0)
  (hker : ∀ G, π G = 0 → π (subst s G) = 0)
  (hlaw : ∀ i, subst F.toPowerSeries (s i) =
    subst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) B)) (s j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) B)) (s j)))
      (F.toPowerSeries i))

include hX in

theorem w_mem_radical : ∀ t : Fin d ⊕ Fin d,
    Sum.elim (fun j => π (X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (X j)) t ∈
      ((⊥ : Ideal (L ⊗[B] L))).radical := by
  rintro (j | j)
  · obtain ⟨k, hk⟩ := hX j
    refine ⟨k, ?_⟩
    show (π (X j) ⊗ₜ[B] (1 : L)) ^ k ∈ (⊥ : Ideal (L ⊗[B] L))
    rw [Algebra.TensorProduct.tmul_pow, hk, TensorProduct.zero_tmul]
    exact Ideal.zero_mem _
  · obtain ⟨k, hk⟩ := hX j
    refine ⟨k, ?_⟩
    show ((1 : L) ⊗ₜ[B] π (X j)) ^ k ∈ (⊥ : Ideal (L ⊗[B] L))
    rw [Algebra.TensorProduct.tmul_pow, hk, TensorProduct.tmul_zero]
    exact Ideal.zero_mem _

theorem map_mem_radical_bot {T T' : Type} [CommRing T] [Algebra B T] [CommRing T'] [Algebra B T']
    (f : T →ₐ[B] T') {x : T} (hx : x ∈ ((⊥ : Ideal T)).radical) : f x ∈ ((⊥ : Ideal T')).radical := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  rw [Submodule.mem_bot] at hk
  rw [← map_pow, hk, map_zero]
  exact Ideal.zero_mem _

include hX in

theorem includeLeft_π (H : MvPowerSeries (Fin d) B) :
    (π H) ⊗ₜ[B] (1 : L) = MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L)) (fun l => π (X l) ⊗ₜ[B] (1 : L)) H := by
  have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal (L ⊗[B] L))
    ((Algebra.TensorProduct.includeLeft : L →ₐ[B] L ⊗[B] L).comp π)
    (fun l => w_mem_radical π hX (Sum.inl l)) H
  exact h

include hX in
theorem includeRight_π (H : MvPowerSeries (Fin d) B) :
    (1 : L) ⊗ₜ[B] (π H) = MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L)) (fun l => (1 : L) ⊗ₜ[B] π (X l)) H := by
  have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal (L ⊗[B] L))
    ((Algebra.TensorProduct.includeRight : L →ₐ[B] L ⊗[B] L).comp π)
    (fun l => w_mem_radical π hX (Sum.inr l)) H
  exact h

include hX hΔ hs0 hlaw in

theorem comul_π_s (i : Fin d) :
    Coalgebra.comul (R := B) (π (s i)) =
      MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
        (Sum.elim (fun j => π (s j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (s j))) (F.toPowerSeries i) := by

  have hc : ∀ j : Fin d, ((Bialgebra.comulAlgHom B L).comp π) (X j) ∈ ((⊥ : Ideal (L ⊗[B] L))).radical := by
    intro j
    show Coalgebra.comul (R := B) (π (X j)) ∈ _
    rw [hΔ]
    exact MvFormalGroup.adicEval_mem_radical _ (w_mem_radical π hX) (F.constantCoeff_eq_zero j)
  have h1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal (L ⊗[B] L))
    ((Bialgebra.comulAlgHom B L).comp π) hc (s i)
  change Coalgebra.comul (R := B) (π (s i)) = _ at h1
  rw [h1]
  have hcj : (fun j : Fin d => ((Bialgebra.comulAlgHom B L).comp π) (X j)) =
      fun j => MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
        (Sum.elim (fun l => π (X l) ⊗ₜ[B] (1 : L)) (fun l => (1 : L) ⊗ₜ[B] π (X l))) (F.toPowerSeries j) := by
    funext j
    exact hΔ j
  rw [hcj, ← MvFormalGroup.adicEval_subst _ (w_mem_radical π hX) F.hasSubst_toPowerSeries (s i), hlaw i,
    MvFormalGroup.adicEval_subst_elim F _ (w_mem_radical π hX)
      (fun j => MvPowerSeries.constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _) (fun l => MvPowerSeries.constantCoeff_X _) (hs0 j))
      (fun j => MvPowerSeries.constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _) (fun l => MvPowerSeries.constantCoeff_X _) (hs0 j))]
  congr 1
  funext t
  rcases t with j | j
  · simp only [Sum.elim_inl]
    rw [MvFormalGroup.adicEval_subst _ (w_mem_radical π hX) (hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _)]
    simp only [MvFormalGroup.adicEval_X, Sum.elim_inl]
    exact (includeLeft_π π hX (s j)).symm
  · simp only [Sum.elim_inr]
    rw [MvFormalGroup.adicEval_subst _ (w_mem_radical π hX) (hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _)]
    simp only [MvFormalGroup.adicEval_X, Sum.elim_inr]
    exact (includeRight_π π hX (s j)).symm

include hX hΔ hlaw in

theorem comul_rho :
    (Algebra.TensorProduct.map (rho π hπ s hs0 hker) (rho π hπ s hs0 hker)).comp (Bialgebra.comulAlgHom B L) =
      (Bialgebra.comulAlgHom B L).comp (rho π hπ s hs0 hker) := by
  apply AlgHom.ext
  intro y
  obtain ⟨G, rfl⟩ := hπ y

  let Ψ₁ : MvPowerSeries (Fin d) B →ₐ[B] L ⊗[B] L :=
    ((Algebra.TensorProduct.map (rho π hπ s hs0 hker) (rho π hπ s hs0 hker)).comp (Bialgebra.comulAlgHom B L)).comp π
  let Ψ₂ : MvPowerSeries (Fin d) B →ₐ[B] L ⊗[B] L := ((Bialgebra.comulAlgHom B L).comp (rho π hπ s hs0 hker)).comp π
  have key : ∀ i, Ψ₁ (X i) = Ψ₂ (X i) := by
    intro i
    show Algebra.TensorProduct.map (rho π hπ s hs0 hker) (rho π hπ s hs0 hker) (Coalgebra.comul (R := B) (π (X i))) =
      Coalgebra.comul (R := B) (rho π hπ s hs0 hker (π (X i)))
    rw [rho_π, subst_X (hasSubst_of_constantCoeff_zero hs0), comul_π_s F π hX hΔ s hs0 hlaw i, hΔ]

    have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal (L ⊗[B] L))
      ((Algebra.TensorProduct.map (rho π hπ s hs0 hker) (rho π hπ s hs0 hker)).comp
        (MvFormalGroup.adicEvalAlgHom (R := B) (⊥ : Ideal (L ⊗[B] L)) (w_mem_radical π hX)))
      (fun t => by
        rw [AlgHom.comp_apply]
        apply map_mem_radical_bot
        rw [MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_X]
        exact w_mem_radical π hX t)
      (F.toPowerSeries i)
    rw [AlgHom.comp_apply, MvFormalGroup.coe_adicEvalAlgHom] at h
    rw [h]
    congr 1
    funext t
    rw [AlgHom.comp_apply, MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_X]
    rcases t with j | j
    · simp only [Sum.elim_inl]
      rw [Algebra.TensorProduct.map_tmul, map_one, rho_π, subst_X (hasSubst_of_constantCoeff_zero hs0)]
    · simp only [Sum.elim_inr]
      rw [Algebra.TensorProduct.map_tmul, map_one, rho_π, subst_X (hasSubst_of_constantCoeff_zero hs0)]
  have hr1 : ∀ i, Ψ₁ (X i) ∈ ((⊥ : Ideal (L ⊗[B] L))).radical := by
    intro i
    rw [key i]
    show Coalgebra.comul (R := B) (rho π hπ s hs0 hker (π (X i))) ∈ _
    rw [rho_π, subst_X (hasSubst_of_constantCoeff_zero hs0)]
    exact map_mem_radical_bot (Bialgebra.comulAlgHom B L) (π_s_mem_radical π hX s hs0 i)
  have hr2 : ∀ i, Ψ₂ (X i) ∈ ((⊥ : Ideal (L ⊗[B] L))).radical := fun i => (key i) ▸ hr1 i
  have e1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical _ Ψ₁ hr1 G
  have e2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical _ Ψ₂ hr2 G
  have hfun : (fun i => Ψ₁ (X i)) = fun i => Ψ₂ (X i) := funext key
  change Ψ₁ G = Ψ₂ G
  rw [e1, e2, hfun]

noncomputable def rhoBialgHom : L →ₐc[B] L :=
  BialgHom.ofAlgHom (rho π hπ s hs0 hker) (counit_rho π hπ hX hε s hs0 hker) (comul_rho F π hπ hX hΔ s hs0 hker hlaw)

theorem rhoBialgHom_π (G : MvPowerSeries (Fin d) B) :
    rhoBialgHom F π hπ hX hΔ hε s hs0 hker hlaw (π G) = π (subst s G) :=
  rho_π π hπ s hs0 hker G

end Comul
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act.P2mHKA"

end P2mHKA
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act.P2mHKA"

namespace P2mHKA

section KerStable

variable {B : Type} [CommRing B] {d : ℕ}
  {L : Type} [CommRing L] [HopfAlgebra B L]
  (π : MvPowerSeries (Fin d) B →ₐ[B] L) (hX : ∀ i, IsNilpotent (π (X i)))
  (φN : Fin d → MvPowerSeries (Fin d) B) (hφN0 : ∀ i, constantCoeff (φN i) = 0)
  (hkerπ : RingHom.ker π = Ideal.span (Set.range φN))
  (s : Fin d → MvPowerSeries (Fin d) B) (hs0 : ∀ i, constantCoeff (s i) = 0)
  (t : Fin d → MvPowerSeries (Fin d) B) (ht0 : ∀ j, constantCoeff (t j) = 0)
  (hcomm : ∀ j, subst s (φN j) = subst φN (t j))

include hX hφN0 hkerπ hs0 ht0 hcomm in

theorem ker_stable (G : MvPowerSeries (Fin d) B) (hG : π G = 0) : π (subst s G) = 0 := by
  have hGmem : G ∈ Ideal.span (Set.range φN) := by rw [← hkerπ]; exact hG
  let θ : MvPowerSeries (Fin d) B →ₐ[B] L := π.comp (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs0))
  have hφker : ∀ i, π (φN i) = 0 := by
    intro i
    have : φN i ∈ RingHom.ker π := by rw [hkerπ]; exact Ideal.subset_span ⟨i, rfl⟩
    exact this
  have hle : Ideal.span (Set.range φN) ≤ RingHom.ker (θ : MvPowerSeries (Fin d) B →+* L) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    show θ (φN j) = 0
    show π (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs0) (φN j)) = 0
    rw [MvPowerSeries.substAlgHom_apply, hcomm j, π_eq_adicEval π hX,
      MvFormalGroup.adicEval_subst _ (X_mem_radical π hX) (hasSubst_of_constantCoeff_zero hφN0)]
    have h0 : (fun i => MvFormalGroup.adicEval (⊥ : Ideal L) (fun k => π (X k)) (φN i)) = fun _ => (0 : L) := by
      funext i
      rw [← π_eq_adicEval π hX]
      exact hφker i
    rw [h0, adicEval_zero_eq, ht0, map_zero]
  have h := hle hGmem
  have h' : θ G = 0 := h
  have : θ G = π (subst s G) := by
    show π (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs0) G) = _
    rw [MvPowerSeries.substAlgHom_apply]
  rw [← this]
  exact h'

end KerStable
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act.P2mHKA"

section OD

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (Φ : FormalODModule p B) (N : ℕ)

theorem act_pow_eq_nthSeries : Φ.act ((p : Zp2 p) ^ N) = Φ.F.nthSeries (p ^ N) := by
  rw [← Nat.cast_pow]
  exact Φ.act_natCast (p ^ N)

theorem subst_act_actPow (a : Zp2 p) (j : Fin 2) :
    subst (Φ.act a) (Φ.act ((p : Zp2 p) ^ N) j) = subst (Φ.act ((p : Zp2 p) ^ N)) (Φ.act a j) := by
  have h1 : (Φ.act ((p : Zp2 p) ^ N)).comp (Φ.act a) = (Φ.act a).comp (Φ.act ((p : Zp2 p) ^ N)) := by
    rw [← Φ.act_mul, ← Φ.act_mul, mul_comm]
  exact congrFun h1 j

theorem subst_varpi_actPow (j : Fin 2) :
    subst Φ.varpi (Φ.act ((p : Zp2 p) ^ N) j) = subst (Φ.act ((p : Zp2 p) ^ N)) (Φ.varpi j) := by
  have h1 : Φ.varpi.comp (Φ.act ((p : Zp2 p) ^ N)) = (Φ.act ((p : Zp2 p) ^ N)).comp Φ.varpi := by
    rw [Φ.varpi_comp_act, map_pow, map_natCast]
  exact (congrFun h1 j).symm

end OD
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act.P2mHKA"

end P2mHKA
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act.P2mHKA"

open P2mHKA in

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (Φ : FormalODModule p B) (N : ℕ)
    [Module.Finite B (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N)))]
    [Module.Free B (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N)))]
    (hX : ∀ i, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N)))) (MvPowerSeries.X i))) :
    ∃ (L : Type) (_ : CommRing L) (_ : HopfAlgebra B L) (_ : Coalgebra.IsCocomm B L)
      (_ : Module.Free B L) (_ : Module.Finite B L) (π : MvPowerSeries (Fin 2) B →ₐ[B] L),
      Function.Surjective π ∧
      RingHom.ker π = Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N))) ∧
      Module.finrank B L = Module.finrank B (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N))) ∧
      (∀ i, IsNilpotent (π (MvPowerSeries.X i))) ∧
      (∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G) ∧
      (∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (Φ.F.toPowerSeries i)) ∧
      (∀ i, Coalgebra.counit (R := B) (π (MvPowerSeries.X i)) = 0) ∧
      (∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G) ∧
      (∀ a : Zp2 p, ∃ ρ : L →ₐc[B] L, ∀ G, ρ (π G) = π (MvPowerSeries.subst (Φ.act a) G)) ∧
      (∃ ϖ : L →ₐc[B] L, ∀ G, ϖ (π G) = π (MvPowerSeries.subst Φ.varpi G)) := by
  have hact := act_pow_eq_nthSeries Φ N
  haveI : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range (Φ.F.nthSeries (p ^ N)))) := by
    rw [← hact]; infer_instance
  haveI : Module.Free B (MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range (Φ.F.nthSeries (p ^ N)))) := by
    rw [← hact]; infer_instance
  have hX' : ∀ i, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.F.nthSeries (p ^ N)))) (MvPowerSeries.X i)) := by
    rw [← hact]; exact hX
  obtain ⟨L, _, _, _, _, _, π, hπ, hker, hrank, hXn, hev, hΔ, hε0, hε⟩ :=
    MvFormalGroup.exists_hopfAlgebra_surjective_ker_eq_span_nthSeries_comul_eq_adicEval_bot_of_isNilpotent Φ.F (p ^ N) hX'
  rw [← hact] at hker hrank
  have hφN0 : ∀ i, constantCoeff (Φ.act ((p : Zp2 p) ^ N) i) = 0 := (Φ.isLawHom_act _).1
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, π, hπ, hker, hrank, hXn, hev,
    hΔ, hε0, hε, fun a => ?_, ?_⟩
  · refine ⟨rhoBialgHom Φ.F π hπ hXn hΔ hε (Φ.act a) (Φ.isLawHom_act a).1
      (ker_stable π hXn (Φ.act ((p : Zp2 p) ^ N)) hφN0 hker (Φ.act a) (Φ.isLawHom_act a).1 (Φ.act a)
        (Φ.isLawHom_act a).1 (subst_act_actPow Φ N a))
      (Φ.isLawHom_act a).2, fun G => ?_⟩
    exact rhoBialgHom_π Φ.F π hπ hXn hΔ hε _ _ _ _ G
  · refine ⟨rhoBialgHom Φ.F π hπ hXn hΔ hε Φ.varpi Φ.isLawHom_varpi.1
      (ker_stable π hXn (Φ.act ((p : Zp2 p) ^ N)) hφN0 hker Φ.varpi Φ.isLawHom_varpi.1 Φ.varpi
        Φ.isLawHom_varpi.1 (subst_varpi_actPow Φ N))
      Φ.isLawHom_varpi.2, fun G => ?_⟩
    exact rhoBialgHom_π Φ.F π hπ hXn hΔ hε _ _ _ _ G

end S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act (solution)
