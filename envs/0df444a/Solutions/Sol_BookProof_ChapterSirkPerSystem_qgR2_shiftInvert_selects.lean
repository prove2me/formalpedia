-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystem.qgR2_shiftInvert_selects
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:45:49.455098+00:00
-- url     : https://prove2.me/submissions/7e60f4b7-cd99-41e5-aee0-d53bdb47b520

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
namespace SirkMultiplicationAux
open BookProof.FarisLavine BookProof.EsaClosure
@[simp] private theorem mulSymbolOp_coe (lam s : ℕ → ℝ) (hs : ∀ n, |s n| ≤ |lam n|)
    (f : mulSymbolDomain lam) :
    ((mulSymbolOp lam s hs f : L2Nat) : ℕ → ℂ) = mulSymbolFun s ((f : L2Nat) : ℕ → ℂ) := rfl

private theorem mulSymbolOp_symmetric (lam s : ℕ → ℝ) (hs : ∀ n, |s n| ≤ |lam n|) :
    SymmetricOn (mulSymbolDomain lam) (mulSymbolOp lam s hs) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [mulSymbolOp_coe, mulSymbolFun, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

private theorem mulHamiltonian_self_extension (lam : ℕ → ℝ) :
    IsSelfAdjointExtension (mulHamiltonian lam) (mulHamiltonian lam) := by
  refine ⟨fun x => ⟨x.2, rfl⟩, mulSymbolOp_symmetric lam lam (fun _ => le_rfl), ?_⟩
  intro w u hu
  have hc : ∀ n, (lam n : ℂ) * w n = u n := by
    intro n
    have h := hu (mulBasis lam n)
    have hval : mulHamiltonian lam (mulBasis lam n) =
        (lp.single 2 n (lam n : ℂ) : L2Nat) := by
      ext k
      by_cases hkn : k = n
      · subst hkn; simp [mulHamiltonian, mulBasis, mulSymbolOp_coe, mulSymbolFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
      · simp [mulHamiltonian, mulBasis, mulSymbolOp_coe, mulSymbolFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_eq_of_ne hkn]
    rw [hval] at h
    simpa [mulBasis, lp.inner_single_left, RCLike.inner_apply, Complex.conj_ofReal, mul_comm] using h
  have heq : mulSymbolFun lam ((w : L2Nat) : ℕ → ℂ) = ((u : L2Nat) : ℕ → ℂ) := funext hc
  have hw : w ∈ mulSymbolDomain lam := by
    change Memℓp (mulSymbolFun lam ((w : L2Nat) : ℕ → ℂ)) 2
    rw [heq]
    exact lp.memℓp u
  refine ⟨hw, ?_⟩
  apply lp.ext
  funext n
  exact hc n
end SirkMultiplicationAux

-- Generated from ChapterSirkPerSystem.lean — theorem BookProof.ChapterSirkPerSystem.qgR2_shiftInvert_selects
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
theorem solution (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)
    {γ : ℂ} (hγ : γ.im ≠ 0) :
    ∃ (Dom : Submodule ℂ L2Nat) (A : Dom →ₗ[ℂ] L2Nat) (X : L2Nat →L[ℂ] L2Nat),
      IsSelfAdjointExtension (qgR2ModeHamiltonian a b M alpha Rc) A ∧
      IsShiftInvertC A γ X ∧ ‖X‖ ≤ |γ.im|⁻¹ := by
  let lam : ℕ → ℝ := BookProof.QuantumGravityDensitized.qgModeSymbol a b (qgR2ModePotential M alpha Rc)
  have hext : IsSelfAdjointExtension (qgR2ModeHamiltonian a b M alpha Rc)
      (qgR2ModeHamiltonian a b M alpha Rc) := SirkMultiplicationAux.mulHamiltonian_self_extension lam
  obtain ⟨X, hX⟩ := exists_isShiftInvertC hext.2.1 hγ
    (cshiftMap_surjective hext.2.1 hext.2.2 hγ)
  exact ⟨mulSymbolDomain lam, qgR2ModeHamiltonian a b M alpha Rc, X, hext, hX, hX.opNorm_le hext.2.1 hγ⟩
#print axioms solution
