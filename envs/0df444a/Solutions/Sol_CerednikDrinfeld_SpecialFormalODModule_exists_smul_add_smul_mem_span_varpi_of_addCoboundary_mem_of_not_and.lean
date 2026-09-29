-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/316a4df8-95e1-59c4-8055-5737fbcd05fc

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_subst_eq_X_and_span_subst_varpi_eq_of_not_and
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_conj_of_subst_eq_X
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

universe u

noncomputable section

namespace S3Asm

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X constantCoeff_X constantCoeff_subst_eq_zero)

section generic

variable {k : Type u} [CommRing k]

abbrev XL (m : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) k := MvPowerSeries.X (Sum.inl m)
abbrev XR (m : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) k := MvPowerSeries.X (Sum.inr m)

theorem hasSubst_XL : HasSubst (XL (k := k)) := hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _
theorem hasSubst_XR : HasSubst (XR (k := k)) := hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _

def pullF (φ : Fin 2 → MvPowerSeries (Fin 2) k) : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  Sum.elim (fun m => subst (XL (k := k)) (φ m)) fun m => subst (XR (k := k)) (φ m)

theorem pullF_cc {φ : Fin 2 → MvPowerSeries (Fin 2) k} (hφ : ∀ i, constantCoeff (φ i) = 0) (s : Fin 2 ⊕ Fin 2) :
    constantCoeff (pullF φ s) = 0 := by
  rcases s with i | i
  · exact constantCoeff_subst_eq_zero hasSubst_XL (fun m => constantCoeff_X _) (hφ i)
  · exact constantCoeff_subst_eq_zero hasSubst_XR (fun m => constantCoeff_X _) (hφ i)

theorem hasSubst_pullF {φ : Fin 2 → MvPowerSeries (Fin 2) k} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    HasSubst (pullF φ) := hasSubst_of_constantCoeff_zero (pullF_cc hφ)

theorem subst_mem_span_range {ι τ : Type*} {φ : Fin 2 → MvPowerSeries τ k} (hφ : HasSubst φ)
    {v : ι → MvPowerSeries (Fin 2) k} {f : MvPowerSeries (Fin 2) k} (hf : f ∈ Ideal.span (Set.range v)) :
    subst φ f ∈ Ideal.span (Set.range fun j => subst φ (v j)) := by
  have h := Ideal.mem_map_of_mem (MvPowerSeries.substAlgHom hφ).toRingHom hf
  rw [Ideal.map_span, ← Set.range_comp] at h
  simpa [MvPowerSeries.substAlgHom_apply, Function.comp_def] using h

theorem subst_mem_span_range₂ {ι : Type*} {T : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k} (hT : HasSubst T)
    {v : ι → MvPowerSeries (Fin 2 ⊕ Fin 2) k} {f : MvPowerSeries (Fin 2 ⊕ Fin 2) k}
    (hf : f ∈ Ideal.span (Set.range v)) :
    subst T f ∈ Ideal.span (Set.range fun j => subst T (v j)) := by
  have h := Ideal.mem_map_of_mem (MvPowerSeries.substAlgHom hT).toRingHom hf
  rw [Ideal.map_span, ← Set.range_comp] at h
  simpa [MvPowerSeries.substAlgHom_apply, Function.comp_def] using h

theorem mem_span_X_of_constantCoeff {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ∀ (T : Finset σ) (f : MvPowerSeries σ k), (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      f ∈ Ideal.span ((fun s => (MvPowerSeries.X s : MvPowerSeries σ k)) '' (T : Set σ)) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext d
      rw [map_zero]
      exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [h0]
    exact Ideal.zero_mem _
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ k := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (MvPowerSeries.X s : MvPowerSeries σ k) ∣ f - f₀ := by
      rw [MvPowerSeries.X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨g, hg⟩ := hdvd
    have hmem₀ : f₀ ∈ Ideal.span ((fun s => (MvPowerSeries.X s : MvPowerSeries σ k)) '' (T : Set σ)) := by
      apply ih
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl
    have hsub : Ideal.span ((fun s => (MvPowerSeries.X s : MvPowerSeries σ k)) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (MvPowerSeries.X s : MvPowerSeries σ k)) '' ((insert s T : Finset σ) : Set σ)) := by
      apply Ideal.span_mono
      apply Set.image_mono
      simp
    have hX : (MvPowerSeries.X s : MvPowerSeries σ k) ∈
        Ideal.span ((fun s => (MvPowerSeries.X s : MvPowerSeries σ k)) '' ((insert s T : Finset σ) : Set σ)) :=
      Ideal.subset_span ⟨s, by simp, rfl⟩
    have hf01 : f = f₀ + MvPowerSeries.X s * g := by rw [← hg]; ring
    rw [hf01]
    exact Ideal.add_mem _ (hsub hmem₀) (Ideal.mul_mem_right _ _ hX)

theorem subst_mem_span_of_constantCoeff {τ : Type*} {a : Fin 2 → MvPowerSeries τ k}
    (ha : HasSubst a) {f : MvPowerSeries (Fin 2) k} (hf : constantCoeff f = 0) :
    subst a f ∈ Ideal.span (Set.range a) := by
  classical
  have h := mem_span_X_of_constantCoeff (k := k) (Finset.univ : Finset (Fin 2)) f (fun d hd => by
    have hd0 : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
    rw [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf])
  have h' : f ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k)) := by
    simpa [Set.image_univ] using h
  have h2 := subst_mem_span_range ha h'
  simp only [subst_X ha] at h2
  exact h2

theorem span_eq_of_subst {u v : Fin 2 → MvPowerSeries (Fin 2) k} {a b : Fin 2 → MvPowerSeries (Fin 2) k}
    (hv0 : ∀ i, constantCoeff (v i) = 0) (hu0 : ∀ i, constantCoeff (u i) = 0)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (hb0 : ∀ i, constantCoeff (b i) = 0)
    (hu : ∀ i, u i = subst v (a i)) (hv : ∀ i, v i = subst u (b i)) :
    Ideal.span (Set.range u) = Ideal.span (Set.range v) := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [hu i]
    exact subst_mem_span_of_constantCoeff (hasSubst_of_constantCoeff_zero hv0) (ha0 i)
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [hv i]
    exact subst_mem_span_of_constantCoeff (hasSubst_of_constantCoeff_zero hu0) (hb0 i)

end generic

end S3Asm

namespace S3Asm

section main

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X constantCoeff_X constantCoeff_subst_eq_zero)

variable {q : ℕ} [Fact q.Prime]
variable {k : Type u} [Field k] [CharP k q] {j₀ : Zp2 q →+* k}

theorem linearPart_comp {φ ψ : Series k} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    MvFormalGroup.linearPart (Series.comp ψ φ) = MvFormalGroup.linearPart ψ * MvFormalGroup.linearPart φ :=
  MvFormalGroup.linearPart_subst hφ ψ

theorem linearPart_X' : MvFormalGroup.linearPart (fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) = 1 :=
  MvFormalGroup.linearPart_X

theorem transport (X₀ X₁ : SpecialFormalODModule q j₀)
    (α β : Fin 2 → MvPowerSeries (Fin 2) k)
    (hα0 : ∀ i, constantCoeff (α i) = 0) (hβ0 : ∀ i, constantCoeff (β i) = 0)
    (hαβ : ∀ i, subst α (β i) = MvPowerSeries.X i) (hβα : ∀ i, subst β (α i) = MvPowerSeries.X i)
    (hF₁ : ∀ i, X₁.F.toPowerSeries i =
      subst (fun j => subst (pullF α) (X₀.F.toPowerSeries j)) (β i))
    (hact₁ : ∀ a, X₁.act a = Series.comp β (Series.comp (X₀.act a) α))
    (hvp1 : X₁.varpi = Series.comp β (Series.comp X₀.varpi α)) :

    Ideal.span (Set.range X₁.varpi) = Ideal.span (Set.range fun i => subst α (X₀.varpi i)) ∧

    ((¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) →
      ¬ ((∀ m ∈ X₁.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₁.varpi) m = 0) ∧
        (∀ m ∈ X₁.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₁.varpi) m = 0))) ∧

    (∀ (ψ : Zp2 q → k) (g : MvPowerSeries (Fin 2) k), constantCoeff g = 0 →
      X₀.F.addCoboundary g ∈ Ideal.span (Set.range (Sum.elim
        (fun i => subst (XL (k := k)) (X₀.varpi i)) (fun i => subst (XR (k := k)) (X₀.varpi i)))) →
      (∀ a : Zp2 q, subst (X₀.act a) g - ψ a • g ∈ Ideal.span (Set.range X₀.varpi)) →
      constantCoeff (subst α g) = 0 ∧
      X₁.F.addCoboundary (subst α g) ∈ Ideal.span (Set.range (Sum.elim
        (fun i => subst (XL (k := k)) (X₁.varpi i)) (fun i => subst (XR (k := k)) (X₁.varpi i)))) ∧
      (∀ a : Zp2 q, subst (X₁.act a) (subst α g) - ψ a • subst α g ∈ Ideal.span (Set.range X₁.varpi))) ∧

    (∀ f : MvPowerSeries (Fin 2) k, f ∈ Ideal.span (Set.range X₁.varpi) →
      subst β f ∈ Ideal.span (Set.range X₀.varpi)) ∧
    (∀ g : MvPowerSeries (Fin 2) k, subst β (subst α g) = g) := by
  classical
  have hαS : HasSubst α := hasSubst_of_constantCoeff_zero hα0
  have hβS : HasSubst β := hasSubst_of_constantCoeff_zero hβ0
  have hvp0 : ∀ i, constantCoeff (X₀.varpi i) = 0 := X₀.isLawHom_varpi.1
  have hvp10 : ∀ i, constantCoeff (X₁.varpi i) = 0 := X₁.isLawHom_varpi.1

  have hβαg : ∀ g : MvPowerSeries (Fin 2) k, subst β (subst α g) = g := fun g => by
    rw [subst_comp_subst_apply hαS hβS]
    have : (fun m => subst β (α m)) = (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k) := funext hβα
    rw [this]
    exact congrFun MvPowerSeries.subst_self g
  have hαβg : ∀ g : MvPowerSeries (Fin 2) k, subst α (subst β g) = g := fun g => by
    rw [subst_comp_subst_apply hβS hαS]
    have : (fun m => subst α (β m)) = (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k) := funext hαβ
    rw [this]
    exact congrFun MvPowerSeries.subst_self g

  have hPa0 : ∀ j, constantCoeff (subst α (X₀.varpi j)) = 0 := fun j =>
    constantCoeff_subst_eq_zero hαS hα0 (hvp0 j)
  have hvp1_eq : ∀ i, X₁.varpi i = subst (fun j => subst α (X₀.varpi j)) (β i) := fun i => by
    rw [hvp1]; rfl
  have hPa_eq : ∀ j, subst α (X₀.varpi j) = subst X₁.varpi (α j) := fun j => by
    have e : subst X₁.varpi (α j) = subst (fun i => subst (fun j => subst α (X₀.varpi j)) (β i)) (α j) :=
      congrArg (fun T : Fin 2 → MvPowerSeries (Fin 2) k => subst T (α j)) (funext hvp1_eq)
    rw [e, ← subst_comp_subst_apply hβS (hasSubst_of_constantCoeff_zero hPa0), hβα]
    exact (subst_X (hasSubst_of_constantCoeff_zero hPa0) j).symm
  have hI : Ideal.span (Set.range X₁.varpi) = Ideal.span (Set.range fun i => subst α (X₀.varpi i)) :=
    span_eq_of_subst hPa0 hvp10 hβ0 hα0 hvp1_eq hPa_eq

  have hLαβ : MvFormalGroup.linearPart α * MvFormalGroup.linearPart β = 1 := by
    rw [← MvFormalGroup.linearPart_subst hβ0 α, ← linearPart_X' (k := k)]; congr 1; exact funext hβα
  have hLβα : MvFormalGroup.linearPart β * MvFormalGroup.linearPart α = 1 := by
    rw [← MvFormalGroup.linearPart_subst hα0 β, ← linearPart_X' (k := k)]; congr 1; exact funext hαβ
  have hLact : ∀ a, MvFormalGroup.linearPart (X₁.act a) =
      MvFormalGroup.linearPart β * MvFormalGroup.linearPart (X₀.act a) * MvFormalGroup.linearPart α := fun a => by
    have hccA : ∀ i, constantCoeff (Series.comp (X₀.act a) α i) = 0 := fun i =>
      constantCoeff_subst_eq_zero hαS hα0 ((X₀.isLawHom_act a).1 i)
    rw [hact₁ a, linearPart_comp hccA, linearPart_comp hα0, Matrix.mul_assoc]
  have hLvp : MvFormalGroup.linearPart X₁.varpi =
      MvFormalGroup.linearPart β * MvFormalGroup.linearPart X₀.varpi * MvFormalGroup.linearPart α := by
    have hccV : ∀ i, constantCoeff (Series.comp X₀.varpi α i) = 0 := fun i =>
      constantCoeff_subst_eq_zero hαS hα0 (hvp0 i)
    rw [hvp1, linearPart_comp hccV, linearPart_comp hα0, Matrix.mul_assoc]

  have hL0 : ∀ m, m ∈ X₁.toFormalODModule.lieZero j₀ ↔
      (MvFormalGroup.linearPart α).mulVec m ∈ X₀.toFormalODModule.lieZero j₀ := by
    intro m
    simp only [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]
    constructor
    · intro h a
      have := congrArg ((MvFormalGroup.linearPart α).mulVec) (h a)
      rw [hLact a, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLαβ, Matrix.one_mul,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_smul] at this
      exact this
    · intro h a
      rw [hLact a, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h a, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        hLβα, Matrix.one_mulVec]
  have hL1 : ∀ m, m ∈ X₁.toFormalODModule.lieOne j₀ ↔
      (MvFormalGroup.linearPart α).mulVec m ∈ X₀.toFormalODModule.lieOne j₀ := by
    intro m
    simp only [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]
    constructor
    · intro h a
      have := congrArg ((MvFormalGroup.linearPart α).mulVec) (h a)
      rw [hLact a, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLαβ, Matrix.one_mul,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_smul] at this
      exact this
    · intro h a
      rw [hLact a, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h a, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        hLβα, Matrix.one_mulVec]
  have hsm : (¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) →
      ¬ ((∀ m ∈ X₁.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₁.varpi) m = 0) ∧
        (∀ m ∈ X₁.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₁.varpi) m = 0)) := by
    intro h0 h1
    apply h0

    have back : ∀ {S₀ : Submodule k (Fin 2 → k)} {S₁ : Submodule k (Fin 2 → k)},
        (∀ m, m ∈ S₁ ↔ (MvFormalGroup.linearPart α).mulVec m ∈ S₀) →
        (∀ m ∈ S₁, Matrix.mulVecLin (MvFormalGroup.linearPart X₁.varpi) m = 0) →
        ∀ m ∈ S₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0 := by
      intro S₀ S₁ hS hk m hm
      have hm' : (MvFormalGroup.linearPart β).mulVec m ∈ S₁ := by
        rw [hS, Matrix.mulVec_mulVec, hLαβ, Matrix.one_mulVec]; exact hm
      have := hk _ hm'
      rw [Matrix.mulVecLin_apply, hLvp] at this
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hLαβ, Matrix.mul_one] at this
      have := congrArg ((MvFormalGroup.linearPart α).mulVec) this
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hLαβ, Matrix.one_mul, Matrix.mulVec_zero] at this
      rw [Matrix.mulVecLin_apply]; exact this
    exact ⟨back hL0 h1.1, back hL1 h1.2⟩

  have tr : ∀ (ψ : Zp2 q → k) (g : MvPowerSeries (Fin 2) k), constantCoeff g = 0 →
      X₀.F.addCoboundary g ∈ Ideal.span (Set.range (Sum.elim
        (fun i => subst (XL (k := k)) (X₀.varpi i)) (fun i => subst (XR (k := k)) (X₀.varpi i)))) →
      (∀ a : Zp2 q, subst (X₀.act a) g - ψ a • g ∈ Ideal.span (Set.range X₀.varpi)) →
      constantCoeff (subst α g) = 0 ∧
      X₁.F.addCoboundary (subst α g) ∈ Ideal.span (Set.range (Sum.elim
        (fun i => subst (XL (k := k)) (X₁.varpi i)) (fun i => subst (XR (k := k)) (X₁.varpi i)))) ∧
      (∀ a : Zp2 q, subst (X₁.act a) (subst α g) - ψ a • subst α g ∈ Ideal.span (Set.range X₁.varpi)) := by
    intro ψ g hg0 hgP hgT
    have hG0 : constantCoeff (subst α g) = 0 := constantCoeff_subst_eq_zero hαS hα0 hg0
    refine ⟨hG0, ?_, ?_⟩
    ·
      have hPS : HasSubst (pullF α) := hasSubst_pullF hα0
      have e1 : subst X₁.F.toPowerSeries (subst α g) = subst (pullF α) (subst X₀.F.toPowerSeries g) := by
        rw [subst_comp_subst_apply hαS (hasSubst_of_constantCoeff_zero X₁.F.constantCoeff_eq_zero),
          subst_comp_subst_apply (hasSubst_of_constantCoeff_zero X₀.F.constantCoeff_eq_zero) hPS]
        congr 1
        funext m
        have : X₁.F.toPowerSeries = fun i => subst (fun j => subst (pullF α) (X₀.F.toPowerSeries j)) (β i) :=
          funext hF₁
        rw [this, ← subst_comp_subst_apply hβS (hasSubst_of_constantCoeff_zero fun j =>
          constantCoeff_subst_eq_zero hPS (pullF_cc hα0) (X₀.F.constantCoeff_eq_zero j)), hβα, subst_X]
        exact hasSubst_of_constantCoeff_zero fun j =>
          constantCoeff_subst_eq_zero hPS (pullF_cc hα0) (X₀.F.constantCoeff_eq_zero j)
      have e2 : subst (XL (k := k)) (subst α g) = subst (pullF α) (subst (XL (k := k)) g) := by
        rw [subst_comp_subst_apply hαS hasSubst_XL, subst_comp_subst_apply hasSubst_XL hPS]
        congr 1; funext m; rw [subst_X hPS]; rfl
      have e3 : subst (XR (k := k)) (subst α g) = subst (pullF α) (subst (XR (k := k)) g) := by
        rw [subst_comp_subst_apply hαS hasSubst_XR, subst_comp_subst_apply hasSubst_XR hPS]
        congr 1; funext m; rw [subst_X hPS]; rfl
      have e4 : X₁.F.addCoboundary (subst α g) = subst (pullF α) (X₀.F.addCoboundary g) := by
        show subst X₁.F.toPowerSeries (subst α g) - subst (fun l => XL l) (subst α g) - subst (fun l => XR l) (subst α g)
          = subst (pullF α) (subst X₀.F.toPowerSeries g - subst (fun l => XL l) g - subst (fun l => XR l) g)
        rw [MvPowerSeries.subst_sub hPS, MvPowerSeries.subst_sub hPS, e1]
        change _ - subst XL (subst α g) - subst XR (subst α g) = _ - subst (pullF α) (subst XL g) - subst (pullF α) (subst XR g)
        rw [e2, e3]
      rw [e4]
      have h := subst_mem_span_range₂ hPS hgP
      have hP1S : HasSubst X₁.varpi := hasSubst_of_constantCoeff_zero hvp10
      have gen_mem : ∀ j, subst (pullF α) ((Sum.elim (fun i => subst (XL (k := k)) (X₀.varpi i))
            (fun i => subst (XR (k := k)) (X₀.varpi i))) j) ∈
          Ideal.span (Set.range (Sum.elim (fun i => subst (XL (k := k)) (X₁.varpi i))
            (fun i => subst (XR (k := k)) (X₁.varpi i)))) := by
        rintro (i | i)
        · have e1 : (fun s => subst (pullF α) (XL (k := k) s)) = fun s => subst (XL (k := k)) (α s) :=
            funext fun s => by rw [subst_X hPS]; rfl
          have e : subst (pullF α) (subst (XL (k := k)) (X₀.varpi i)) =
              subst (fun m => subst (XL (k := k)) (X₁.varpi m)) (α i) := by
            rw [subst_comp_subst_apply hasSubst_XL hPS, e1, ← subst_comp_subst_apply hαS hasSubst_XL, hPa_eq i,
              subst_comp_subst_apply hP1S hasSubst_XL]
          have hsub : Set.range (fun m => subst (XL (k := k)) (X₁.varpi m)) ⊆
              Set.range (Sum.elim (fun i => subst (XL (k := k)) (X₁.varpi i)) (fun i => subst (XR (k := k)) (X₁.varpi i))) :=
            Set.range_subset_iff.mpr fun m => ⟨Sum.inl m, rfl⟩
          show subst (pullF α) (subst (XL (k := k)) (X₀.varpi i)) ∈ _
          rw [e]
          exact Ideal.span_mono hsub
            (subst_mem_span_of_constantCoeff (hasSubst_of_constantCoeff_zero fun m =>
              constantCoeff_subst_eq_zero hasSubst_XL (fun l => constantCoeff_X _) (hvp10 m)) (hα0 i))
        · have e1 : (fun s => subst (pullF α) (XR (k := k) s)) = fun s => subst (XR (k := k)) (α s) :=
            funext fun s => by rw [subst_X hPS]; rfl
          have e : subst (pullF α) (subst (XR (k := k)) (X₀.varpi i)) =
              subst (fun m => subst (XR (k := k)) (X₁.varpi m)) (α i) := by
            rw [subst_comp_subst_apply hasSubst_XR hPS, e1, ← subst_comp_subst_apply hαS hasSubst_XR, hPa_eq i,
              subst_comp_subst_apply hP1S hasSubst_XR]
          have hsub : Set.range (fun m => subst (XR (k := k)) (X₁.varpi m)) ⊆
              Set.range (Sum.elim (fun i => subst (XL (k := k)) (X₁.varpi i)) (fun i => subst (XR (k := k)) (X₁.varpi i))) :=
            Set.range_subset_iff.mpr fun m => ⟨Sum.inr m, rfl⟩
          show subst (pullF α) (subst (XR (k := k)) (X₀.varpi i)) ∈ _
          rw [e]
          exact Ideal.span_mono hsub
            (subst_mem_span_of_constantCoeff (hasSubst_of_constantCoeff_zero fun m =>
              constantCoeff_subst_eq_zero hasSubst_XR (fun l => constantCoeff_X _) (hvp10 m)) (hα0 i))
      exact (Ideal.span_le.mpr (Set.range_subset_iff.mpr gen_mem)) h
    · intro a
      have e1 : subst (X₁.act a) (subst α g) = subst α (subst (X₀.act a) g) := by
        rw [subst_comp_subst_apply hαS (hasSubst_of_constantCoeff_zero (X₁.isLawHom_act a).1),
          subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (X₀.isLawHom_act a).1) hαS]
        congr 1
        funext m
        rw [hact₁ a]
        show subst (fun i => subst (fun j => subst α (X₀.act a j)) (β i)) (α m) = subst α (X₀.act a m)
        rw [← subst_comp_subst_apply hβS (hasSubst_of_constantCoeff_zero fun j =>
          constantCoeff_subst_eq_zero hαS hα0 ((X₀.isLawHom_act a).1 j)), hβα, subst_X
          (hasSubst_of_constantCoeff_zero fun j => constantCoeff_subst_eq_zero hαS hα0 ((X₀.isLawHom_act a).1 j))]
      rw [e1, ← MvPowerSeries.subst_smul hαS, ← MvPowerSeries.subst_sub hαS, hI]
      exact subst_mem_span_range hαS (hgT a)
  refine ⟨hI, hsm, tr, ?_, hβαg⟩
  intro f hf
  rw [hI] at hf
  have h := subst_mem_span_range hβS hf
  simp only [hβαg] at h
  simpa using h

end main

end S3Asm

open S3Asm CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (ψ : Zp2 q → k) (g g' : MvPowerSeries (Fin 2) k)
    (hg0 : MvPowerSeries.constantCoeff g = 0) (hg0' : MvPowerSeries.constantCoeff g' = 0)
    (hgP : X₀.F.addCoboundary g ∈ Ideal.span (Set.range (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i)))))
    (hgP' : X₀.F.addCoboundary g' ∈ Ideal.span (Set.range (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i)))))
    (hgT : ∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) g - ψ a • g ∈ Ideal.span (Set.range X₀.varpi))
    (hgT' : ∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) g' - ψ a • g' ∈ Ideal.span (Set.range X₀.varpi)) :
    ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • g + c' • g' ∈ Ideal.span (Set.range X₀.varpi) := by
  classical
  obtain ⟨α, β, hα0, hβ0, hαβ, hβα, hNF⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_subst_eq_X_and_span_subst_varpi_eq_of_not_and X₀ hsmooth
  obtain ⟨X₁, hF₁, hact₁, hvp1⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_conj_of_subst_eq_X X₀ α β hα0 hβ0 hαβ hβα
  obtain ⟨hI, hsm, tr, back, hβαg⟩ := S3Asm.transport X₀ X₁ α β hα0 hβ0 hαβ hβα hF₁ hact₁ hvp1
  obtain ⟨hG0, hGP, hGT⟩ := tr ψ g hg0 hgP hgT
  obtain ⟨hG0', hGP', hGT'⟩ := tr ψ g' hg0' hgP' hgT'
  obtain ⟨c, c', hcc, hmem⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq
      X₁ (hsm hsmooth) (hI.trans hNF) ψ (MvPowerSeries.subst α g) (MvPowerSeries.subst α g') hG0 hG0' hGP hGP' hGT hGT'
  refine ⟨c, c', hcc, ?_⟩
  have h := back _ hmem
  rw [MvPowerSeries.subst_add (MvPowerSeries.hasSubst_of_constantCoeff_zero hβ0),
    MvPowerSeries.subst_smul (MvPowerSeries.hasSubst_of_constantCoeff_zero hβ0),
    MvPowerSeries.subst_smul (MvPowerSeries.hasSubst_of_constantCoeff_zero hβ0), hβαg, hβαg] at h
  exact h

end

end S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and (solution)
