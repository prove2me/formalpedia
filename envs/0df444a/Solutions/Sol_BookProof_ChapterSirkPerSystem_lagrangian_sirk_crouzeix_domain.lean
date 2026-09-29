-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystem.lagrangian_sirk_crouzeix_domain
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:45:48.564819+00:00
-- url     : https://prove2.me/submissions/95b53bd1-8b03-4378-8716-07bc49614816

import Definitions.Def_ChapterSirkPerSystem
-- Adapted prerequisite proofs: Leonardo Pedro, timepiece 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology
namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {Dom : Submodule ℂ F}
private theorem IsShiftInvertC.mem {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) : X u ∈ Dom := (h.2 u).choose

private theorem IsShiftInvertC.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) :
    γ • X u - A ⟨X u, h.mem u⟩ = u := (h.2 u).choose_spec

private theorem IsShiftInvertC.norm_apply_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) (u : F) :
    ‖X u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hb : |γ.im| * ‖((⟨X u, h.mem u⟩ : Dom) : F)‖ ≤ ‖cshiftMap A γ ⟨X u, h.mem u⟩‖ :=
    norm_cshiftMap_ge hsym _ _
  rw [show cshiftMap A γ ⟨X u, h.mem u⟩ = u from h.shift_apply u] at hb
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  simpa using hb

private theorem IsShiftInvertC.opNorm_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) :
    ‖X‖ ≤ |γ.im|⁻¹ :=
  X.opNorm_le_bound (by positivity) (h.norm_apply_le hsym hγ)

private theorem exists_isShiftInvertC {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    {γ : ℂ} (hγ : γ.im ≠ 0) (hsurj : Function.Surjective (cshiftMap A γ)) :
    ∃ X : F →L[ℂ] F, IsShiftInvertC A γ X := by
  classical
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hinj : Function.Injective (cshiftMap A γ) := cshiftMap_injective hsym hγ
  choose g hg using hsurj
  have hgshift : ∀ x : Dom, g (cshiftMap A γ x) = x := fun x => hinj (hg _)
  have hadd : ∀ u v : F, ((g (u + v) : Dom) : F) = (g u : F) + (g v : F) := by
    intro u v
    have : cshiftMap A γ (g (u + v)) = cshiftMap A γ (g u + g v) := by
      rw [hg, map_add, hg, hg]
    exact congrArg Subtype.val (hinj this)
  have hsmul : ∀ (c : ℂ) (u : F), ((g (c • u) : Dom) : F) = c • (g u : F) := by
    intro c u
    have : cshiftMap A γ (g (c • u)) = cshiftMap A γ (c • g u) := by
      rw [hg, map_smul, hg]
    exact congrArg Subtype.val (hinj this)
  let L : F →ₗ[ℂ] F :=
    { toFun := fun u => (g u : F)
      map_add' := hadd
      map_smul' := by intro c u; simpa using hsmul c u }
  have hbound : ∀ u : F, ‖L u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
    intro u
    have hb : |γ.im| * ‖((g u : Dom) : F)‖ ≤ ‖cshiftMap A γ (g u)‖ := norm_cshiftMap_ge hsym _ _
    rw [hg u] at hb
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact hb
  refine ⟨L.mkContinuous |γ.im|⁻¹ hbound, fun x => ?_, fun u => ?_⟩
  · change ((g (cshiftMap A γ x) : Dom) : F) = (x : F)
    rw [hgshift x]
  · refine ⟨(g u).2, ?_⟩
    have hsub : (⟨((g u : Dom) : F), (g u).2⟩ : Dom) = g u := Subtype.ext rfl
    change cshiftMap A γ ⟨((g u : Dom) : F), _⟩ = u
    rw [hsub, hg u]

end BookProof.HashimotoShiftInvert
namespace SirkComplexGeometryAux
open BookProof.ChapterH4 BookProof.ChapterH9 BookProof.HashimotoShiftInvert BookProof.FarisLavine
variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {Dom : Submodule ℂ F}
private theorem krylov_rayleigh_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E) (y : F) :
    inner ℂ y (compress V X y) = inner ℂ (V y) (X (V y)) := by
  rw [compress]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_right V y (X (V y))

private theorem numRange_compress_subset (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : numRange (compress V X) ⊆ numRange X := by
  rintro c ⟨y, hy, rfl⟩
  exact ⟨V y, by rw [hViso, hy], (krylov_rayleigh_transfer V X y).symm⟩

private theorem numRange_subset_closedBall (X : E →L[ℂ] E) :
    numRange X ⊆ Metric.closedBall (0 : ℂ) ‖X‖ := by
  rintro c ⟨x, hx, rfl⟩
  have hcs : ‖(inner ℂ x (X x) : ℂ)‖ ≤ ‖x‖ * ‖X x‖ := norm_inner_le_norm _ _
  have hXb : ‖X x‖ ≤ ‖X‖ := by simpa [hx] using X.le_opNorm x
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖(inner ℂ x (X x) : ℂ)‖ ≤ ‖x‖ * ‖X x‖ := hcs
    _ = ‖X x‖ := by rw [hx, one_mul]
    _ ≤ ‖X‖ := hXb

private theorem crouzeix_domain_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S)
    (hS : numRange X ⊆ S) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ S :=
  convexHull_min ((numRange_compress_subset V X hViso).trans hS) hconv

private theorem numRange_subset_closedBall_of_shiftInvertC {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) :
    numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ :=
  (numRange_subset_closedBall X).trans
    (Metric.closedBall_subset_closedBall (hX.opNorm_le hsym hγ))

private theorem crouzeix_domain_shiftInvertC {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0)
    (V : G →L[ℂ] F) (hViso : ∀ x : G, ‖V x‖ = ‖x‖) :
    convexHull ℝ (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ :=
  crouzeix_domain_transfer V X hViso _ (convex_closedBall _ _)
    (numRange_subset_closedBall_of_shiftInvertC hX hsym hγ)

end SirkComplexGeometryAux
namespace BookProof.NavierStokesFlow.FullEsa
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
private theorem IsSymmetricDom.add {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) :
    IsSymmetricDom (A + B) := by
  intro x y
  simp only [LinearMap.add_apply, Submodule.coe_add, inner_add_left, inner_add_right, hA x y,
    hB x y]

private theorem IsSymmetricDom.sum {ι : Type*} (s : Finset ι) {A : ι → (D →ₗ[ℂ] D)}
    (hA : ∀ i ∈ s, IsSymmetricDom (A i)) : IsSymmetricDom (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (IsSymmetricDom.zero (D := D))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hA a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

private theorem IsSymmetricDom.comp_of_commute {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A)
    (hB : IsSymmetricDom B) (hcomm : A.comp B = B.comp A) : IsSymmetricDom (A.comp B) := by
  intro x y
  have h1 : (inner ℂ ((A (B x) : F)) (y : F) : ℂ) = inner ℂ ((B x : F)) ((A y : F)) := hA _ _
  have h2 : (inner ℂ ((B x : F)) ((A y : F)) : ℂ) = inner ℂ (x : F) ((B (A y) : F)) := hB _ _
  have h3 : B (A y) = A (B y) := by
    have := congrArg (fun T : D →ₗ[ℂ] D => T y) hcomm
    simpa using this.symm
  simpa [h3] using h1.trans h2

end BookProof.NavierStokesFlow.FullEsa
namespace BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData
open BookProof.NavierStokesFlow.FullEsa
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
private theorem isSymmetricDom_sq {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) :
    IsSymmetricDom (A.comp A) :=
  hA.comp_of_commute hA rfl

private theorem kinetic_isSymmetricDom : IsSymmetricDom L.kinetic :=
  IsSymmetricDom.real_smul
    (IsSymmetricDom.sum Finset.univ fun i _ => isSymmetricDom_sq (L.P_symm i)) _

private theorem viscous_isSymmetricDom : IsSymmetricDom L.viscous :=
  IsSymmetricDom.real_smul
    (IsSymmetricDom.sum Finset.univ fun i _ => isSymmetricDom_sq (L.Q_symm i)) _

private theorem drift_isSymmetricDom : IsSymmetricDom L.drift :=
  IsSymmetricDom.sum Finset.univ fun i _ => (L.drive_symm i).real_smul _

private theorem hFull_isSymmetricDom : IsSymmetricDom L.hFull :=
  ((L.kinetic_isSymmetricDom.add L.viscous_isSymmetricDom).add
      L.drift_isSymmetricDom).add L.constraint_symm

end BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData

-- Generated from ChapterSirkPerSystem.lean — theorem BookProof.ChapterSirkPerSystem.lagrangian_sirk_crouzeix_domain
open BookProof.ChapterSirkPerSystem









noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH9 BookProof.ChapterSirkSpectralGeometry
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.EsaClosure
open BookProof.YangMillsFriedrichs BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.NSHashimoto
open BookProof.NavierStokesFlow.DiffHashimoto BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.LagrangianEsa BookProof.NavierStokesFlow.LagrangianKatoRellich
theorem solution {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (L : LagrangianFullData F)
    (hesa : EssentiallySelfAdjointOn L.D (lagrangianCore L)) {γ : ℂ} (hγ : γ.im ≠ 0) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (X : F →L[ℂ] F),
      IsSelfAdjointExtension (lagrangianCore L) A ∧ IsShiftInvertC A γ X ∧
      ‖X‖ ≤ |γ.im|⁻¹ ∧
      numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ ∧
      ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] F), (∀ x, ‖V x‖ = ‖x‖) →
        convexHull ℝ (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ := by
  have hsym : SymmetricOn L.D (lagrangianCore L) := fun x y => L.hFull_isSymmetricDom x y
  obtain ⟨Dom, A, hA⟩ := exists_isSelfAdjointExtension_of_esa (lagrangianCore L) L.dense hsym hesa
  obtain ⟨X, hX⟩ := exists_isShiftInvertC hA.2.1 hγ
    (cshiftMap_surjective hA.2.1 hA.2.2 hγ)
  exact ⟨Dom, A, X, hA, hX, hX.opNorm_le hA.2.1 hγ,
    SirkComplexGeometryAux.numRange_subset_closedBall_of_shiftInvertC hX hA.2.1 hγ,
    fun _ V hViso => SirkComplexGeometryAux.crouzeix_domain_shiftInvertC hX hA.2.1 hγ V hViso⟩
#print axioms solution
