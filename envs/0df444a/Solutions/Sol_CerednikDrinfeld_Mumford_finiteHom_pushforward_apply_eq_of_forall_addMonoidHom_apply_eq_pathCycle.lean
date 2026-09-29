-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.finiteHom_pushforward_apply_eq_of_forall_addMonoidHom_apply_eq_pathCycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d2eb1b3d-04be-5d86-a89e-f747ec30eaab

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Transfer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_finiteHom_pushforward_apply_eq_of_forall_addMonoidHom_apply_eq_pathCycle

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

namespace NatOmegaBS

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

section generic

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (Γ' : Subgroup G) [GraphAction ↥Γ' 𝒯]

theorem subgroup_smul_dart (γ : ↥Γ') (d : 𝒯.Dart) : γ • d = (γ : G) • d := rfl

theorem mk_out_eq (d : 𝒯.Dart) :
    (Quotient.mk (orbitRel G 𝒯.Dart) ((Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d : QuotEdge ↥Γ' 𝒯).out) : QuotEdge G 𝒯) =
      Quotient.mk (orbitRel G 𝒯.Dart) d := by
  have h : (orbitRel ↥Γ' 𝒯.Dart) ((Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d : QuotEdge ↥Γ' 𝒯).out) d :=
    Quotient.mk_out d
  rw [orbitRel_apply, mem_orbit_iff] at h
  obtain ⟨γ, hγ⟩ := h
  rw [← hγ, subgroup_smul_dart, quotEdge_mk_smul]

theorem tau_out_fst_eq (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (d : 𝒯.Dart) :
    τ ((Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out).fst = τ d.fst := by
  have h : (orbitRel G 𝒯.Dart) ((Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out) d := Quotient.mk_out d
  rw [orbitRel_apply, mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  rw [← hg, smul_dart_fst, hτ]

end generic

theorem sum_list_map_sum {ι α β : Type} [AddCommMonoid β] (s : Finset ι) (l : List α) (f : ι → α → β) :
    ∑ i ∈ s, (l.map (f i)).sum = (l.map fun a => ∑ i ∈ s, f i a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

end NatOmegaBS

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction NatOmegaBS in
theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    (Γ' : Subgroup G) [GraphAction ↥Γ' 𝒯]
    [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotEdge ↥Γ' 𝒯)]
    {E₁ V₁ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] (D₁ : DegeneracyData E₁ V₁)
    (eE₁ : E₁ ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0})
    {E₂ V₂ : Type} [Fintype E₂] [DecidableEq E₂] [DecidableEq V₂] (D₂ : DegeneracyData E₂ V₂)
    (eE₂ : E₂ ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (μ : D₁.FiniteHom D₂)
    (hμE : ∀ e₁ : E₁, ((eE₂ (μ.mapE e₁)).1 : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out)
    (v₀ : W)
    (Φ₁ : Additive (Abelianization ↥Γ') →+ ↥(ribbonKernel D₁))
    (hΦ₁ : ∀ g : ↥Γ', (Φ₁ (Additive.ofMul (Abelianization.of g)) : E₁ → ℤ) = pathCycle 𝒯 (fun e => (eE₁ e).1) v₀ g)
    (Φ₂ : Additive (Abelianization G) →+ ↥(ribbonKernel D₂))
    (hΦ₂ : ∀ g : G, (Φ₂ (Additive.ofMul (Abelianization.of g)) : E₂ → ℤ) = pathCycle 𝒯 (fun e => (eE₂ e).1) v₀ g)
    (γ' : ↥Γ') :
    μ.pushforward (Φ₁ (Additive.ofMul (Abelianization.of γ'))) = Φ₂ (Additive.ofMul (Abelianization.of (γ' : G))) := by
  classical
  apply Subtype.ext
  funext e₂
  rw [DegeneracyData.FiniteHom.pushforward_apply, hΦ₂]
  simp_rw [hΦ₁]

  obtain ⟨p⟩ := hT.connected.preconnected v₀ ((γ' : G) • v₀)
  let P : 𝒯.Path v₀ ((γ' : G) • v₀) := p.toPath
  have h1 : pathCycle 𝒯 (fun e => (eE₁ e).1) v₀ γ' = walkCycle 𝒯 (fun e => (eE₁ e).1) (P : 𝒯.Walk v₀ ((γ' : G) • v₀)) :=
    pathCycle_eq_walkCycle 𝒯 (fun e => (eE₁ e).1) hT.isAcyclic v₀ γ' P
  have h2 : pathCycle 𝒯 (fun e => (eE₂ e).1) v₀ (γ' : G) =
      walkCycle 𝒯 (fun e => (eE₂ e).1) (P : 𝒯.Walk v₀ ((γ' : G) • v₀)) :=
    pathCycle_eq_walkCycle 𝒯 (fun e => (eE₂ e).1) hT.isAcyclic v₀ (γ' : G) P
  rw [h2]
  simp_rw [h1]
  simp only [walkCycle]
  rw [sum_list_map_sum]
  congr 1
  apply List.map_congr_left
  intro d _

  have key : ∀ d : 𝒯.Dart,
      (∑ e₁ ∈ Finset.univ.filter (fun e₁ => μ.mapE e₁ = e₂),
          (if (Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d : QuotEdge ↥Γ' 𝒯) = (eE₁ e₁).1 then (1 : ℤ) else 0)) =
        if (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯) = (eE₂ e₂).1 then 1 else 0 := by
    intro d
    by_cases hd : (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯) = (eE₂ e₂).1
    · rw [if_pos hd]

      have hτd : τ ((Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d : QuotEdge ↥Γ' 𝒯).out).fst = 0 := by
        have h0 := (eE₂ e₂).2
        rw [← hd, tau_out_fst_eq 𝒯 τ hτ] at h0
        have h' : (orbitRel ↥Γ' 𝒯.Dart) ((Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d : QuotEdge ↥Γ' 𝒯).out) d :=
          Quotient.mk_out d
        rw [orbitRel_apply, mem_orbit_iff] at h'
        obtain ⟨γ, hγ⟩ := h'
        rw [← hγ, subgroup_smul_dart, smul_dart_fst, hτ]
        exact h0
      set eStar : E₁ := eE₁.symm ⟨Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d, hτd⟩ with he
      have he₁ : (eE₁ eStar).1 = Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) d := by
        rw [he, Equiv.apply_symm_apply]
      have hmap : μ.mapE eStar = e₂ := by
        apply eE₂.injective
        apply Subtype.ext
        rw [hμE, he₁, mk_out_eq, hd]
      rw [Finset.sum_eq_single_of_mem eStar (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmap⟩)]
      · rw [if_pos he₁.symm]
      · intro e₁ _ hne
        rw [if_neg]
        intro heq
        apply hne
        apply eE₁.injective
        exact Subtype.ext (heq.symm.trans he₁.symm)
    · rw [if_neg hd]
      refine Finset.sum_eq_zero fun e₁ he₁ => ?_
      rw [if_neg]
      intro heq
      apply hd
      have hm := (Finset.mem_filter.mp he₁).2
      rw [← hm, hμE, ← heq, mk_out_eq]
  simp only [dartIndex, Finset.sum_sub_distrib]
  rw [key d, key d.symm]

end S_CerednikDrinfeld_Mumford_finiteHom_pushforward_apply_eq_of_forall_addMonoidHom_apply_eq_pathCycle
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_finiteHom_pushforward_apply_eq_of_forall_addMonoidHom_apply_eq_pathCycle (solution)
