-- Prove2me | solution 1 for CharacterModule.natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e9e42b4e-8f5f-5a24-9bfc-3e055bc2c24a

import Mathlib
import Theorems.Thm_CharacterModule_natCard_eq_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet

set_option autoImplicit false

namespace P2MPontryagin

theorem natCard_characterModule (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card (CharacterModule M) = Nat.card M :=
  CharacterModule.natCard_eq_of_finite M

end P2MPontryagin

namespace P2MPontryagin

open Submodule

variable {A : Type*} [CommRing A] {G : Type*} [AddCommGroup G] [Module A G]

noncomputable def descend {P : Type*} [AddCommGroup P] [Module A P] (f : G →ₗ[A] P)
    (φ : CharacterModule G) (h : ∀ x ∈ LinearMap.ker f, φ x = 0) :
    CharacterModule ↥(LinearMap.range f) where
  toFun y := φ (Classical.choose y.2)
  map_zero' := by
    have hs := Classical.choose_spec (0 : LinearMap.range f).2
    exact h _ (by rw [LinearMap.mem_ker, hs]; rfl)
  map_add' y y' := by
    have e1 := Classical.choose_spec y.2
    have e2 := Classical.choose_spec y'.2
    have e3 := Classical.choose_spec (y + y').2
    have hk : Classical.choose (y + y').2 - Classical.choose y.2 - Classical.choose y'.2
        ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, map_sub, e1, e2, e3, Submodule.coe_add, add_sub_cancel_left, sub_self]
    have := h _ hk
    rw [map_sub, map_sub, sub_sub, sub_eq_zero] at this
    exact this

theorem descend_apply {P : Type*} [AddCommGroup P] [Module A P] (f : G →ₗ[A] P)
    (φ : CharacterModule G) (h : ∀ x ∈ LinearMap.ker f, φ x = 0) (x : G) :
    descend f φ h ⟨f x, LinearMap.mem_range_self f x⟩ = φ x := by
  show φ (Classical.choose _) = φ x
  have e := Classical.choose_spec (⟨f x, LinearMap.mem_range_self f x⟩ : LinearMap.range f).2
  have hk : Classical.choose (⟨f x, LinearMap.mem_range_self f x⟩ : LinearMap.range f).2 - x
      ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, e, sub_self]
  have := h _ hk
  rwa [map_sub, sub_eq_zero] at this

def genMap {s : ℕ} (b : Fin s → A) : G →ₗ[A] (Fin s → G) := LinearMap.pi fun i => b i • LinearMap.id

theorem genMap_apply {s : ℕ} (b : Fin s → A) (x : G) (i : Fin s) : genMap b x i = b i • x := rfl

theorem ker_genMap {s : ℕ} (b : Fin s → A) :
    LinearMap.ker (genMap (G := G) b) = torsionBySet A G (Set.range b) := by
  ext x
  rw [LinearMap.mem_ker, mem_torsionBySet_iff]
  constructor
  · rintro h ⟨_, i, rfl⟩; exact congr_fun h i
  · intro h; funext i; exact h ⟨b i, i, rfl⟩

omit [Module A G] in
theorem charSum_apply {ι : Type*} (t : Finset ι) (c : ι → CharacterModule G) (x : G) :
    (∑ i ∈ t, c i) x = ∑ i ∈ t, c i x := by
  classical
  refine Finset.induction_on t ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]; rfl
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

theorem ker_dual_subtype_torsionBySet {s : ℕ} (b : Fin s → A) :
    LinearMap.ker (CharacterModule.dual (torsionBySet A G (Set.range b)).subtype)
      = Ideal.span (Set.range b) • (⊤ : Submodule A (CharacterModule G)) := by
  classical
  apply le_antisymm
  · intro φ hφ
    rw [LinearMap.mem_ker] at hφ
    have hφ0 : ∀ x ∈ torsionBySet A G (Set.range b), φ x = 0 := fun x hx => by
      have := DFunLike.congr_fun hφ ⟨x, hx⟩
      exact this
    have hker : ∀ x ∈ LinearMap.ker (genMap (G := G) b), φ x = 0 := by
      rw [ker_genMap]; exact hφ0
    obtain ⟨ψ, hψ⟩ := CharacterModule.dual_surjective_of_injective
      (LinearMap.range (genMap (G := G) b)).subtype (Submodule.subtype_injective _)
      (descend (genMap b) φ hker)
    have hφeq : φ = ∑ i, b i • CharacterModule.dual (LinearMap.single A (fun _ : Fin s => G) i) ψ := by
      ext x
      rw [charSum_apply]
      have step : ∀ i, (b i • CharacterModule.dual (LinearMap.single A (fun _ : Fin s => G) i) ψ) x
          = ψ (Pi.single i (b i • x)) := fun i => rfl
      simp only [step]
      rw [← map_sum, Finset.univ_sum_single (fun i => b i • x)]
      have h1 : (fun i => b i • x) = genMap b x := rfl
      rw [h1, ← descend_apply (genMap b) φ hker x, ← hψ]
      rfl
    rw [hφeq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) Submodule.mem_top
  · rw [Submodule.smul_le]
    intro a ha φ _
    rw [LinearMap.mem_ker]
    ext ⟨x, hx⟩
    rw [torsionBySet_eq_torsionBySet_span] at hx
    have hax : a • x = 0 := (mem_torsionBySet_iff _ _).1 hx ⟨a, ha⟩
    show φ (a • x) = 0
    rw [hax, map_zero]

theorem natCard_quotient_span_smul_top {s : ℕ} (b : Fin s → A)
    [Finite ↥(torsionBySet A G (Set.range b))] :
    Nat.card (CharacterModule G ⧸ Ideal.span (Set.range b) • (⊤ : Submodule A (CharacterModule G)))
      = Nat.card ↥(torsionBySet A G (Set.range b)) := by
  have hs := CharacterModule.dual_surjective_of_injective
    (torsionBySet A G (Set.range b)).subtype (Submodule.subtype_injective _)
  rw [← ker_dual_subtype_torsionBySet b, Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hs).toEquiv,
    natCard_characterModule]

theorem natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet (s : Set A) (hs : s.Finite)
    (hfin : Finite ↥(torsionBySet A G s)) :
    Nat.card (CharacterModule G ⧸ (Ideal.span s • (⊤ : Submodule A (CharacterModule G))))
      = Nat.card ↥(torsionBySet A G s) := by
  obtain ⟨n, b, hb⟩ := hs.fin_embedding

  subst hb
  haveI := hfin
  exact natCard_quotient_span_smul_top (fun i => (b i : A))

end P2MPontryagin

theorem solution
    (A : Type*) [CommRing A] (G : Type*) [AddCommGroup G] [Module A G]
    (s : Set A) (hs : s.Finite) (hfin : Finite ↥(Submodule.torsionBySet A G s)) :
    Nat.card (CharacterModule G ⧸ (Ideal.span s • (⊤ : Submodule A (CharacterModule G))))
      = Nat.card ↥(Submodule.torsionBySet A G s) :=
  P2MPontryagin.natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet s hs hfin

end S_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet
end P2MW
export P2MW.S_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet (solution)
