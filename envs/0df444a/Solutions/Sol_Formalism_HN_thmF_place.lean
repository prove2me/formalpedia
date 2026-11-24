-- Prove2me | solution 1 for Formalism.HN.thmF_place
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:11.631806+00:00
-- url     : https://prove2.me/submissions/0c4cc738-c3fe-445a-8298-a16dd7a95b39

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TheoremFSharp
import Theorems.Thm_Formalism_HN_PlaceDecomposition_finrank_span_complex
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_fcoord_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (hLA : FrameLA1)
    (b' : Basis κ K W) (b : ∀ i, Basis (ι i) K (V i)) (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (c : I → ℝ)
    (e η ε : ℝ) (Nt : ∀ i, Submodule (𝓞 K) (V i))
    (hY : ∀ i, IsUnit (Y i).det) (hY' : IsUnit Y'.det) (hc : ∀ i, 0 < c i)
    (hpos : 0 < ∑ i, Fintype.card (ι i))
    (hBall : ∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)
    (hF2 : (∑ i, hs2 (frK (c i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ))
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4) (hη : 0 ≤ η)
    (hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ c (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ))
    (hcor : (∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt i))) ≤ ε * ∑ i, (Fintype.card (ι i) : ℝ)) :
    (Fintype.card κ : ℝ) - rkK (⨆ i, (Nt i).map ((B i).restrictScalars (𝓞 K))) ≤
      (η + 4 * ε + 4 * Real.sqrt e) * (Fintype.card (κ ⊕ κ₁) : ℝ) := by
  classical
  set Bv : ∀ i, EuclideanSpace ℂ (ι i) →ₗ[ℂ] EuclideanSpace ℂ κ := fun i => Matrix.toEuclideanLin
    (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) with hBv
  set Ba : ∀ i, EuclideanSpace ℂ (ι i) →ₗ[ℂ] EuclideanSpace ℂ (κ ⊕ κ₁) := fun i =>
    Matrix.toEuclideanLin (Ball i) with hBa
  let M := ⨆ i, (Nt i).map ((B i).restrictScalars (𝓞 K))
  let eq : ∀ (α : Type) [Fintype α], (α → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ α :=
    fun α _ => (WithLp.linearEquiv 2 ℂ (α → ℂ)).symm
  let Nτ : ∀ i, Submodule ℂ (EuclideanSpace ℂ (ι i)) := fun i =>
    (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (b i) (fun _ => Y i) v '' (Nt i : Set (V i)))).map
      (eq (ι i)).toLinearMap
  have hNτ : ∀ i, finrank ℂ (Nτ i) = rkK (Nt i) := by
    intro i
    rw [LinearEquiv.finrank_map_eq]
    exact PlaceDecomposition.finrank_span_complex (b i) (fun _ => Y i) (fun _ => hY i) (Nt i) v
  let T : Submodule ℂ (EuclideanSpace ℂ κ) :=
    (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b' (fun _ => Y') v '' (M : Set W))).map (eq κ).toLinearMap
  have hT : finrank ℂ T = rkK M := by
    rw [LinearEquiv.finrank_map_eq]
    exact PlaceDecomposition.finrank_span_complex b' (fun _ => Y') (fun _ => hY') M v
  have hST : (⨆ i, (Nτ i).map (Bv i)) ≤ T := by
    refine iSup_le fun i => ?_
    rw [Submodule.map_le_iff_le_comap]
    show Submodule.map _ _ ≤ _
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Submodule.mem_comap, SetLike.mem_coe]
    refine Submodule.mem_map.2 ⟨Formalism.HermitianLatticesTheory.fcoord b' (fun _ => Y') v (B i x),
      Submodule.subset_span ⟨B i x, ?_, rfl⟩, ?_⟩
    · exact Submodule.mem_iSup_of_mem i
        (Submodule.mem_map_of_mem (f := (B i).restrictScalars (𝓞 K)) hx)
    · rw [PlaceOperatorNorms.fcoord_map (b i) (fun _ => Y i) b' (fun _ => Y') (fun _ => hY i) v
        (B i) x]
      simp only [LinearEquiv.coe_coe, hBv, Matrix.toLpLin_apply, Matrix.toEuclideanLin, eq]
      rfl

  let P : EuclideanSpace ℂ (κ ⊕ κ₁) →ₗ[ℂ] EuclideanSpace ℂ κ :=
    (eq κ).toLinearMap ∘ₗ LinearMap.funLeft ℂ ℂ Sum.inl ∘ₗ (eq (κ ⊕ κ₁)).symm.toLinearMap
  have hPB : ∀ i, P ∘ₗ Ba i = Bv i := by
    intro i
    apply LinearMap.ext
    intro x
    ext k
    have e1 : ∀ (A : Matrix (κ ⊕ κ₁) (ι i) ℂ),
        (P (Matrix.toEuclideanLin A x)) k = ∑ j, A (Sum.inl k) j * x j := by
      intro A; simp [P, eq, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
    have e2 : ∀ (A : Matrix κ (ι i) ℂ), (Matrix.toEuclideanLin A x) k = ∑ j, A k j * x j := by
      intro A; simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
    rw [LinearMap.comp_apply]
    simp only [Ba, Bv]
    rw [e1, e2]
    simp only [hBall]
  have hPsurj : LinearMap.range P = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨(eq (κ ⊕ κ₁)) (Sum.elim ((eq κ).symm y) 0), ?_⟩
    ext k
    simp [P, eq, LinearMap.funLeft]
  have hkerP : finrank ℂ (LinearMap.ker P) = Fintype.card κ₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker P
    rw [hPsurj, finrank_top, finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_sum] at h
    omega
  let S := ⨆ i, (Nτ i).map (Ba i)
  have hPS : S.map P ≤ T := by
    have : S.map P = ⨆ i, (Nτ i).map (Bv i) := by
      simp only [S, Submodule.map_iSup, ← Submodule.map_comp, hPB]
    rw [this]; exact hST
  have hSdim : finrank ℂ S ≤ finrank ℂ (S.map P) + Fintype.card κ₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (P ∘ₗ S.subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at h
    have hk : finrank ℂ (LinearMap.ker (P ∘ₗ S.subtype)) ≤ finrank ℂ (LinearMap.ker P) := by
      rw [LinearMap.ker_comp, ← Submodule.finrank_map_subtype_eq]
      exact Submodule.finrank_mono (Submodule.map_comap_le _ _)
    omega
  have h1 : 0 < ∑ i, finrank ℂ (EuclideanSpace ℂ (ι i)) := by
    simp only [finrank_euclideanSpace]; exact hpos
  have h2 : (∑ i, hs2 (frK (c i) (Ba i) - LinearMap.id)) ≤
      e * ∑ i, (finrank ℂ (EuclideanSpace ℂ (ι i)) : ℝ) := by
    simp only [finrank_euclideanSpace]; exact hF2
  have h3 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁)) (frQ c Ba ∘ₗ frQ c Ba)).re
      ≤ (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁)) (frQ c Ba)).re ^ 2 /
        (finrank ℂ (EuclideanSpace ℂ (κ ⊕ κ₁)) : ℝ) := by
    simp only [finrank_euclideanSpace]; exact hF1
  have h4 : (∑ i, ((finrank ℂ (EuclideanSpace ℂ (ι i)) : ℝ) - finrank ℂ (Nτ i))) ≤
      ε * ∑ i, (finrank ℂ (EuclideanSpace ℂ (ι i)) : ℝ) := by
    simp only [finrank_euclideanSpace, hNτ]; exact hcor
  have hLA' := hLA I (fun i => EuclideanSpace ℂ (ι i)) (EuclideanSpace ℂ (κ ⊕ κ₁)) Ba c Nτ e η ε
    hc h1 h2 he0 he1 hη h3 h4
  rw [finrank_euclideanSpace] at hLA'
  have hsum := Submodule.finrank_add_finrank_orthogonal S
  rw [finrank_euclideanSpace, Fintype.card_sum] at hsum
  have hmono := Submodule.finrank_mono hPS
  rw [hT] at hmono
  have hsum' : (finrank ℂ S : ℝ) + (finrank ℂ Sᗮ : ℝ) =
      (Fintype.card κ : ℝ) + Fintype.card κ₁ := by exact_mod_cast hsum
  have hmono' : (finrank ℂ (S.map P) : ℝ) ≤ (rkK M : ℝ) := by exact_mod_cast hmono
  have hSdim' : (finrank ℂ S : ℝ) ≤ finrank ℂ (S.map P) + Fintype.card κ₁ := by
    exact_mod_cast hSdim
  have hLA'' : (finrank ℂ Sᗮ : ℝ) ≤ (η + 4 * ε + 4 * Real.sqrt e) *
      (Fintype.card (κ ⊕ κ₁) : ℝ) := hLA'
  linarith
end Formalism.HN
