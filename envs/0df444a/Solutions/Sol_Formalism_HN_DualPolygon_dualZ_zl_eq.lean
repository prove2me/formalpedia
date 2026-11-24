-- Prove2me | solution 1 for Formalism.HN.DualPolygon.dualZ_zl_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:43.129509+00:00
-- url     : https://prove2.me/submissions/e6a8a30c-116c-4de4-8bb1-264d69dcc40d

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_DualPolygon_inner_realize_alt
import Theorems.Thm_Formalism_HN_DualPolygon_ident_mem_zl
import Theorems.Thm_Formalism_HN_DualPolygon_span_zl_top
import Theorems.Thm_Formalism_HN_DualPolygon_ident_inner_span_eq_zero
import Theorems.Thm_Formalism_HN_DualPolygon_ident_inner_spanZ_eq_zero
import Theorems.Thm_Formalism_HN_PlaceLattice_zl_span_eq
import Theorems.Thm_Formalism_HN_duality_mem_dualZ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V) :
    dualZ (zl (Formalism.HermitianLatticesTheory.realize b X) A) ⊓
        ((Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))ᗮ).restrictScalars ℤ =
      (zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (tdualLat A ⊓ annO N)).map
        (((2 : ℝ) • (cE : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _)).restrictScalars ℤ) := by
  classical
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) with hρ'
  set T : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := (2 : ℝ) • cE with hTdef
  have hT : ∀ (x : V) (f : Module.Dual K V), inner ℝ (ρ x) (T (ρ' f)) =
      ((Algebra.trace ℚ K (f x) : ℚ) : ℝ) := by
    intro x f
    rw [hTdef, LinearMap.smul_apply]
    exact inner_realize_alt b X hX x f
  have hspanA := span_zl_top b X hX A hA hsp
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map,
    LinearMap.restrictScalars_apply]
  constructor
  · rintro ⟨hy1, hy2⟩
    rw [duality_mem_dualZ] at hy1
    obtain ⟨-, hy1⟩ := hy1
    obtain ⟨s, hsA, hspan, hli⟩ := exists_linearIndependent K (A : Set V)
    have : FiniteDimensional K V := Module.Finite.of_basis b
    let _ : Fintype s := hli.setFinite.fintype
    let e : s → V := Subtype.val
    have he : ∀ j : s, (j : V) ∈ A := fun j => hsA j.2
    have hmemA : ∀ (k : Free.ChooseBasisIndex ℤ (𝓞 K)) (j : s), integralBasis K k • (j : V) ∈ A := by
      intro k j
      rw [integralBasis_apply, algebraMap_smul]
      exact A.smul_mem _ (he j)
    have hex : ∀ (j : s) (k : Free.ChooseBasisIndex ℤ (𝓞 K)),
        ∃ n : ℤ, (n : ℝ) = inner ℝ (ρ (integralBasis K k • (j : V))) y :=
      fun j k => hy1 _ ⟨_, hmemA k j, rfl⟩
    choose t ht using hex
    let ω' := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)
    have hω : ∀ k l, Algebra.trace ℚ K (integralBasis K l * ω' k) = if l = k then 1 else 0 := by
      intro k l
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left _ _ k l
    let c : s → K := fun j => ∑ k, ((t j k : ℚ)) • ω' k
    have hc : ∀ j l, Algebra.trace ℚ K (integralBasis K l * c j) = (t j l : ℚ) := by
      intro j l
      simp only [c, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hω, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hsp' : ⊤ ≤ Submodule.span K (Set.range e) := by
      rw [show Set.range e = s from Subtype.range_coe, hspan, hsp]
    let eB : Basis s K V := Basis.mk hli hsp'
    let f : Module.Dual K V := ∑ j, c j • eB.coord j
    have hfe : ∀ j : s, f (j : V) = c j := by
      intro j
      have : (j : V) = eB j := by simp [eB]
      rw [this]
      simp [f, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    have hTy : T (ρ' f) = y := by
      set z := T (ρ' f) - y
      have hgen : ∀ u ∈ Set.range (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × s =>
          ρ (integralBasis K p.1 • e p.2)), inner ℝ u z = 0 := by
        rintro u ⟨⟨k, j⟩, rfl⟩
        simp only [z, inner_sub_right, hT, map_smul, smul_eq_mul, e, hfe, hc, ← ht]
        push_cast; ring
      have hM : Submodule.span K ((Submodule.span (𝓞 K) (Set.range e) : Submodule (𝓞 K) V) :
          Set V) = ⊤ := by
        rw [Submodule.span_span_of_tower]; exact top_le_iff.mp hsp'
      have hsM := span_zl_top b X hX _ (Submodule.fg_span (Set.finite_range e)) hM
      have hzl := PlaceLattice.zl_span_eq (K := K) ρ e
      have h1 : ∀ u ∈ (zl ρ (Submodule.span (𝓞 K) (Set.range e)) : Set _), inner ℝ u z = 0 := by
        intro u hu
        rw [hzl] at hu
        exact ident_inner_spanZ_eq_zero _ z hgen u hu
      have h2 := ident_inner_span_eq_zero _ z h1 z (by rw [hsM]; trivial)
      have : z = 0 := inner_self_eq_zero.mp h2
      exact sub_eq_zero.mp this
    refine ⟨ρ' f, ⟨f, Submodule.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩, hTy⟩
    · intro x hx
      obtain ⟨n, hn⟩ := hy1 (ρ x) ⟨x, hx, rfl⟩
      refine ⟨n, ?_⟩
      have h3 := hT x f
      rw [hTy, ← hn] at h3
      exact_mod_cast h3.symm
    · intro x hx
      have h0 : ∀ r : 𝓞 K, Algebra.trace ℚ K ((r : K) * f x) = 0 := by
        intro r
        have hm : ρ (r • x) ∈ Submodule.span ℝ (zl ρ N : Set _) :=
          Submodule.subset_span ⟨r • x, N.smul_mem r hx, rfl⟩
        have h1 := Submodule.inner_right_of_mem_orthogonal hm hy2
        rw [← hTy, hT] at h1
        have h4 : f (r • x) = (r : K) * f x := by
          rw [← algebraMap_smul K r x, map_smul, smul_eq_mul]
        rw [h4] at h1
        exact_mod_cast h1
      have hz : Algebra.traceForm ℚ K (f x) = 0 :=
        (integralBasis K).ext (fun k => by
          rw [LinearMap.zero_apply, Algebra.traceForm_apply, integralBasis_apply, mul_comm]
          exact h0 _)
      exact (traceForm_nondegenerate ℚ K).1 (f x) (fun n => by rw [hz]; rfl)
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨f, hf, rfl⟩ := (ident_mem_zl _ _ _).1 hw
    have hf' := Submodule.mem_inf.mp hf
    refine ⟨?_, ?_⟩
    · rw [duality_mem_dualZ]
      refine ⟨by rw [hspanA]; trivial, ?_⟩
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (ident_mem_zl _ _ _).1 hz
      obtain ⟨n, hn⟩ := hf'.1 x hx
      exact ⟨n, by rw [hT, hn]; simp⟩
    · rw [Submodule.mem_orthogonal]
      intro u hu
      refine ident_inner_span_eq_zero _ _ (fun u hu => ?_) u hu
      obtain ⟨x, hx, rfl⟩ := (ident_mem_zl _ _ _).1 hu
      rw [hT, hf'.2 x hx]
      simp
end Formalism.HN.DualPolygon
