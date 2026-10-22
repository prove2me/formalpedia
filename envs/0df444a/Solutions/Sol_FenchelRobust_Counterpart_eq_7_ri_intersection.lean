-- Prove2me | solution 1 for FenchelRobust.Counterpart.eq_7_ri_intersection
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:27:22.538486+00:00
-- url     : https://prove2.me/submissions/2c32d386-29da-4ab1-aa72-eea7588c0436

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model

set_option autoImplicit false
open FenchelRobust.Counterpart

lemma FRC_ri_char {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set E) (x : E) :
    x ∈ intrinsicInterior ℝ s ↔
      x ∈ affineSpan ℝ s ∧ ∃ ε > 0, ∀ y ∈ affineSpan ℝ s, dist y x < ε → y ∈ s := by
  rw [mem_intrinsicInterior]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
    obtain ⟨ε, hε, hball⟩ := hy
    refine ⟨ε, hε, fun z hz hzd => ?_⟩
    have : (⟨z, hz⟩ : affineSpan ℝ s) ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, Subtype.dist_eq]
      simpa using hzd
    exact hball this
  · rintro ⟨hx, ε, hε, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨ε, hε, fun z hz => ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq] at hz
    exact h z.1 z.2 (by simpa using hz)

lemma FRC_ri_image {m L : ℕ} (a0 : Fin m → ℝ) (A : Matrix (Fin m) (Fin L) ℝ)
    (Z : Set (Fin L → ℝ)) (hZ : (0 : Fin L → ℝ) ∈ intrinsicInterior ℝ Z) :
    a0 ∈ intrinsicInterior ℝ (uncertaintySet a0 A Z) := by
  have h0Z : (0 : Fin L → ℝ) ∈ Z := intrinsicInterior_subset hZ
  rw [FRC_ri_char] at hZ ⊢
  obtain ⟨hZ0, δ, hδ, hZδ⟩ := hZ
  set S : AffineSubspace ℝ (Fin L → ℝ) := affineSpan ℝ Z with hS
  set V : Submodule ℝ (Fin L → ℝ) := S.direction with hV
  have hSV : ∀ v, v ∈ S ↔ v ∈ V := by
    intro v
    rw [hV, ← AffineSubspace.vsub_right_mem_direction_iff_mem hZ0 v]
    simp
  set f : (Fin L → ℝ) →ₗ[ℝ] (Fin m → ℝ) := Matrix.mulVecLin A with hf
  set W : Submodule ℝ (Fin m → ℝ) := V.map f with hW
  refine ⟨?_, ?_⟩
  · exact subset_affineSpan ℝ _ ⟨0, h0Z, by simp⟩
  have hUT : uncertaintySet a0 A Z ⊆ (AffineSubspace.mk' a0 W : Set (Fin m → ℝ)) := by
    rintro a ⟨ζ, hζ, rfl⟩
    rw [SetLike.mem_coe, AffineSubspace.mem_mk']
    simp only [vsub_eq_sub, add_sub_cancel_left]
    exact ⟨ζ, (hSV ζ).1 (subset_affineSpan ℝ _ hζ), by simp [hf]⟩
  have hAU : affineSpan ℝ (uncertaintySet a0 A Z) ≤ AffineSubspace.mk' a0 W :=
    affineSpan_le.2 hUT
  let g : V →ₗ[ℝ] W := f.restrict (fun v hv => Submodule.mem_map_of_mem hv)
  have hg : Function.Surjective g := by
    rintro ⟨w, hw⟩
    obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.1 hw
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  have hopen := LinearMap.isOpenMap_of_finiteDimensional g hg
  have hmem : (0 : W) ∈ g '' Metric.ball (0 : V) δ :=
    ⟨0, Metric.mem_ball_self hδ, map_zero g⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hopen _ Metric.isOpen_ball) 0 hmem
  refine ⟨ε, hε, fun u hu hd => ?_⟩
  have huT : u ∈ (AffineSubspace.mk' a0 W) := hAU hu
  rw [AffineSubspace.mem_mk'] at huT
  simp only [vsub_eq_sub] at huT
  have hwball : (⟨u - a0, huT⟩ : W) ∈ Metric.ball (0 : W) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    simpa [dist_eq_norm] using hd
  obtain ⟨v', hv'B, hv'eq⟩ := hball hwball
  have hfv : f v'.1 = u - a0 := congrArg Subtype.val hv'eq
  have hvS : v'.1 ∈ S := (hSV _).2 v'.2
  have hvd : dist v'.1 0 < δ := by
    have := Metric.mem_ball.1 hv'B
    rw [dist_zero_right] at this ⊢
    simpa using this
  have hvZ : v'.1 ∈ Z := hZδ _ hvS hvd
  refine ⟨v'.1, hvZ, ?_⟩
  have : A.mulVec v'.1 = u - a0 := hfv
  rw [this]
  abel

theorem solution {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (hZconvex : Convex ℝ Z) (hZzero : (0 : Fin L → ℝ) ∈ intrinsicInterior ℝ Z)
    (hregular : Regular a0 D) :
    ∀ x : Fin n → ℝ,
      (intrinsicInterior ℝ (uncertaintySet a0 A Z) ∩
        intrinsicInterior ℝ (D x)).Nonempty := by
  intro x
  exact ⟨a0, FRC_ri_image a0 A Z hZzero, hregular x⟩
