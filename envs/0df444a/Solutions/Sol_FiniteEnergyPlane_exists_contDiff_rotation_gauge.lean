-- Prove2me | solution 1 for FiniteEnergyPlane.exists_contDiff_rotation_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T11:42:57.501818+00:00
-- url     : https://prove2.me/submissions/ea7cdcc1-b168-495e-85c9-879d04492270

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_eq_comp_rotation_of_mem_embeddedFastPlaneSet
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_of_apply_eq_of_injective_fderiv
import Theorems.Thm_FiniteEnergyPlane_continuousOn_of_apply_eq_of_injOn
import Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_exp_eq



/-!
# Hryniewicz Lemma 7.4 (`exists_contDiff_rotation_gauge`)

* Lemma 7.1: for `t ∈ I ∩ I'`, `W (t, e^{iφ} z) = U (t, z)` for some `φ`; put `ρ t = e^{iφ}`;
* `W (t, ρ t) = U (t, 1)` and `W (t, ·)` is an embedding, so `ρ` is continuous (compactness of
  the circle) and then `C^l` (implicit function theorem);
* a `C^l` angle `θ` with `ρ = e^{2π i θ}` on the interval `I ∩ I'`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_contDiff_rotation_gauge_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I I' : Set ℝ) (hI : IsOpen I) (hI' : IsOpen I')
    (hIc : Convex ℝ I) (hIc' : Convex ℝ I') (U W : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (hW : IsPageFamilyOn H J P γ y l I' W) :
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ l θ (I ∩ I') ∧ ∀ t ∈ I ∩ I', ∀ z,
      U (t, z) = W (t, Complex.exp (((2 * π * θ t : ℝ) : ℂ) * Complex.I) * z) := by
  set S := I ∩ I' with hSdef
  have hS : IsOpen S := hI.inter hI'
  have hSc : Convex ℝ S := hIc.inter hIc'
  have hrot : ∀ t, ∃ φ : ℝ, t ∈ S → ∀ z,
      W (t, Complex.exp ((φ : ℂ) * Complex.I) * z) = U (t, z) := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨φ, hφ⟩ := eq_comp_rotation_of_mem_embeddedFastPlaneSet H hH J hJ P hcz γ (y t)
        (fun z => W (t, z)) (fun z => U (t, z)) (hW.2 t ht.2) (hU.2 t ht.1)
      exact ⟨φ, fun _ => hφ⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose φ hφ using hrot
  set ρ : ℝ → ℂ := fun t => Complex.exp ((φ t : ℂ) * Complex.I) with hρdef
  have hρ1 : ∀ t ∈ S, ‖ρ t‖ = 1 := fun t _ => by
    simp only [hρdef]
    exact Complex.norm_exp_ofReal_mul_I (φ t)
  have heq : ∀ t ∈ S, W (t, ρ t) = (fun t => U (t, 1)) t := fun t ht => by
    simpa using hφ t ht 1
  have hpair : ContDiff ℝ l (fun t : ℝ => ((t, (1 : ℂ)) : ℝ × ℂ)) :=
    contDiff_id.prodMk contDiff_const
  have hg : ContDiffOn ℝ l (fun t => U (t, 1)) S :=
    (hU.1.comp hpair.contDiffOn (fun t ht => ⟨ht.1, Set.mem_univ _⟩))
  have hWS : ContDiffOn ℝ l W (S ×ˢ Set.univ) :=
    hW.1.mono (Set.prod_mono Set.inter_subset_right le_rfl)
  have hemb : ∀ t ∈ S, IsEmbeddedPlane (fun z => W (t, z)) := fun t ht => (hW.2 t ht.2).2
  have hρc : ContinuousOn ρ S :=
    continuousOn_of_apply_eq_of_injOn (isCompact_sphere (0 : ℂ) 1)
      (hWS.continuousOn.mono (Set.prod_mono le_rfl (Set.subset_univ _))) hg.continuousOn
      (fun t ht => by simpa using hρ1 t ht) heq
      (fun t ht => (hemb t ht).1.injOn)
  have hρd : ContDiffOn ℝ l ρ S :=
    contDiffOn_of_apply_eq_of_injective_fderiv hl hS hWS hg hρc heq
      (fun t ht => (hemb t ht).2 (ρ t))
  obtain ⟨θ, hθ, hθρ⟩ := exists_contDiffOn_exp_eq hl hS hSc hρd hρ1
  refine ⟨θ, hθ, fun t ht z => ?_⟩
  rw [hθρ t ht]
  exact (hφ t ht z).symm

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I I' : Set ℝ) (hI : IsOpen I) (hI' : IsOpen I')
    (hIc : Convex ℝ I) (hIc' : Convex ℝ I') (U W : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (hW : IsPageFamilyOn H J P γ y l I' W) :
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ l θ (I ∩ I') ∧ ∀ t ∈ I ∩ I', ∀ z,
      U (t, z) = W (t, Complex.exp (((2 * π * θ t : ℝ) : ℂ) * Complex.I) * z) :=
  exists_contDiff_rotation_gauge_aux H hH J hJ P hcz γ y hy l hl I I' hI hI' hIc hIc' U W hU hW
