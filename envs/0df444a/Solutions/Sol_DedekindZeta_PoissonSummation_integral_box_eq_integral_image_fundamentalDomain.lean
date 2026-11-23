-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.integral_box_eq_integral_image_fundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:45.760654+00:00
-- url     : https://prove2.me/submissions/0ce05714-9279-4a99-bb2a-d11341ade6e1

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_latticeEquivFun_map_volume

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_908
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ y in Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1),
        g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))
      = ∫ y in (latticeEquivFun L b) '' D,
          g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) := by
  classical
  set Φ := latticeEquivFun L b with hΦ
  -- The integrand on `ℝ^d`, `F y = g (red y)` with `red y i = (y i : AddCircle 1)`.
  set F : (Fin d → ℝ) → ℂ := fun y => g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) with hF
  -- The integer lattice `Γ = ℤ^d ⊆ (Fin d → ℝ)`.
  set Γ : AddSubgroup (Fin d → ℝ) :=
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup with hΓ
  -- Membership in `Γ`: integer coordinates.
  have hΓmem : ∀ z : Fin d → ℝ, z ∈ Γ ↔ ∀ i, z i ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro z
    rw [hΓ, Submodule.mem_toAddSubgroup,
      (Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ z]
    simp only [Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom]
  -- `Γ` as a set is exactly `Φ '' L` (`latticeEquivFun_image_lattice`).
  have hΓimg : (Γ : Set (Fin d → ℝ)) = Φ '' (L : Set V) := by
    rw [hΦ, latticeEquivFun_image_lattice]
    ext z
    rw [SetLike.mem_coe, hΓmem]
    rfl
  -- `Φ` carries `L` into `Γ` and `Φ.symm` carries `Γ` into `L`.
  have hmemΓ : ∀ x : V, x ∈ L → Φ x ∈ Γ := by
    intro x hx
    rw [← SetLike.mem_coe, hΓimg]
    exact ⟨x, hx, rfl⟩
  have hmemL : ∀ z : Fin d → ℝ, z ∈ Γ → Φ.symm z ∈ L := by
    intro z hz
    rw [← SetLike.mem_coe, hΓimg] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  -- The group equivalence `e : Γ ≃ L.toAddSubgroup` induced by `Φ`.
  let e : Γ ≃ (↥L.toAddSubgroup) :=
    { toFun := fun z => ⟨Φ.symm z, hmemL z z.2⟩
      invFun := fun x => ⟨Φ x, hmemΓ x x.2⟩
      left_inv := fun z => by
        apply Subtype.ext; simp [ContinuousLinearEquiv.apply_symm_apply]
      right_inv := fun x => by
        apply Subtype.ext; simp [ContinuousLinearEquiv.symm_apply_apply] }
  -- `Φ.symm` is quasi-measure-preserving (it scales volume by `(covolume L)⁻¹`).
  have hmap := latticeEquivFun_map_volume L b
  set c := ENNReal.ofReal (ZLattice.covolume L) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (ZLattice.covolume_pos L volume)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsymm_map : Measure.map Φ.symm volume = c⁻¹ • volume := by
    have h1 : Measure.map Φ.symm (Measure.map Φ volume) = volume := by
      rw [Measure.map_map Φ.symm.continuous.measurable Φ.continuous.measurable]
      simp
    rw [hmap, Measure.map_smul] at h1
    rw [← h1, smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
  have hqmp : Measure.QuasiMeasurePreserving (⇑Φ.symm) volume volume :=
    ⟨Φ.symm.continuous.measurable, by
      rw [hsymm_map]; exact Measure.smul_absolutelyContinuous⟩
  -- `Φ '' D` is a fundamental domain of `Γ`.
  have himg : IsAddFundamentalDomain Γ (Φ '' D) volume := by
    have h := hD.image_of_equiv (ν := (volume : Measure (Fin d → ℝ)))
      Φ.toHomeomorph.toEquiv ?_ e ?_
    · simpa using h
    · simpa using hqmp
    · intro z x
      show Φ ((e z : V) + x) = (z : Fin d → ℝ) + Φ x
      rw [map_add]
      congr 1
      show Φ (Φ.symm z) = (z : Fin d → ℝ)
      rw [ContinuousLinearEquiv.apply_symm_apply]
  -- The Ico-box (= `ZSpan.fundamentalDomain (Pi.basisFun)`) is a fundamental domain of `Γ`.
  haveI : Countable ↥Γ := by
    rw [hΓ]
    exact inferInstanceAs
      (Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))))
  have hbox_ico : IsAddFundamentalDomain Γ
      (Set.univ.pi fun _ : Fin d => Set.Ico (0 : ℝ) 1) volume := by
    rw [← ZSpan.fundamentalDomain_pi_basisFun]
    exact ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin d)) volume
  -- `F` is `Γ`-invariant: `red` collapses integer translations.
  have hFinv : ∀ (z : Γ) (y : Fin d → ℝ), F (z +ᵥ y) = F y := by
    intro z y
    rw [hF]
    refine congrArg g ?_
    funext i
    have hzi : (z : Fin d → ℝ) i ∈ Set.range ((↑) : ℤ → ℝ) := (hΓmem _).1 z.2 i
    obtain ⟨n, hn⟩ := hzi
    have hvadd : (z +ᵥ y) = (z : Fin d → ℝ) + y := rfl
    rw [hvadd]
    show (((z : Fin d → ℝ) i + y i : ℝ) : AddCircle (1 : ℝ)) = ((y i : ℝ) : AddCircle (1 : ℝ))
    rw [← hn, add_comm, AddCircle.coe_add,
      show (((n : ℝ)) : AddCircle (1 : ℝ)) = 0 from by
        rw [AddCircle.coe_eq_zero_iff]; exact ⟨n, by simp⟩,
      add_zero]
  -- `(Ioc 0 1)^d =ᵐ (Ico 0 1)^d` (boundaries are null).
  have hae : (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) 1)
      =ᵐ[volume] (Set.univ.pi fun _ : Fin d => Set.Ico (0 : ℝ) 1) := by
    have h1 := Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
      (s := Set.univ) (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
    have h2 := Measure.pi_Ico_ae_eq_pi_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
      (s := Set.univ) (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
    rw [← volume_pi] at h1 h2
    exact h1.trans h2.symm
  calc
    (∫ y in Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) 1, F y)
        = ∫ y in Set.univ.pi fun _ : Fin d => Set.Ico (0 : ℝ) 1, F y :=
          setIntegral_congr_set hae
    _ = ∫ y in Φ '' D, F y := hbox_ico.setIntegral_eq himg hFinv
end DedekindZeta.PoissonSummation
