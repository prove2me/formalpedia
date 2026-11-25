-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.exists_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:19.007736+00:00
-- url     : https://prove2.me/submissions/73e30e2d-8b7b-47a0-97a9-e588ba697f01

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CosetFd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MeasurablePhiInv
import Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_phiMap_phiInv
import Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_phiInv_phiMap
import Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_phiInv_add
import Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_measurable_phiInv
import Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_idealLattice_fd
import Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_coset_fd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
section Inv
variable {K : Type} [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]
end Inv
private theorem mem_idealLattice_iff' (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (x : mixedSpace K) :
    x ∈ idealLattice K I ↔ ∃ a : K, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ∧ mixedEmbedding K a = x := by
  first
  | (rw [mem_idealLattice]; rfl)
  | exact mem_idealLattice K I
  | simp [idealLattice]
private theorem existsUnique_add_mem_preimage_of_additive_equiv {V W : Type} [AddCommGroup V] [AddCommGroup W]
    (f : V → W) (g : W → V) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (hg : ∀ y z, g (y + z) = g y + g z) (L : AddSubgroup V) (M : AddSubgroup W)
    (hLM : ∀ w, w ∈ M ↔ g w ∈ L) (F : Set V) (h : ∀ x, ∃! l : L, (l : V) + x ∈ F) :
    ∀ y, ∃! m : M, (m : W) + y ∈ g ⁻¹' F := by
  intro y
  obtain ⟨l, hl, hu⟩ := h (g y)
  have hfl : f l ∈ M := (hLM _).2 (by rw [hgf]; exact l.2)
  refine ⟨⟨f l, hfl⟩, ?_, ?_⟩
  · show g (f l + y) ∈ F
    rw [hg, hgf]
    exact hl
  · rintro ⟨m, hm⟩ hm'
    have hm'' : g m + g y ∈ F := by
      have h3 := hm'
      rw [Set.mem_preimage, hg] at h3
      exact h3
    have h2 : g m = l := congrArg Subtype.val (hu ⟨g m, (hLM m).1 hm⟩ hm'')
    apply Subtype.ext
    show m = f l
    rw [← h2, hfg]
private theorem phiMap_mixedEmbedding_eq {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding) (a : K) :
    phiMap σ (fun i => φ i ≠ (σ i).1.embedding) (mixedEmbedding K a) = fun i => φ i a := by
  funext i
  simp only [phiMap]
  split_ifs with h
  · rw [(hφ i).resolve_left h, ComplexEmbedding.conjugate_coe_eq]
    first
    | rfl
    | simp [mixedEmbedding]
  · have h' : φ i = (σ i).1.embedding := by simpa using h
    rw [h']
    first
    | rfl
    | simp [mixedEmbedding]
end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : AddSubgroup K)
    (hΛ : ∀ a ∈ Λ, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
    (hk0 : Λ.relIndex (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) ≠ 0)
    (s : ℂ) (hs : s ≠ 0) :
    ∃ F : Set (ι → ℂ), MeasurableSet F ∧ ∀ v, ∃! a : Λ, (fun i => s * φ i a) + v ∈ F := by
  have hne : Nonempty ι := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    have hw : w.IsComplex := (w.isReal_or_isComplex).resolve_left
      (fun h => isEmptyElim (⟨w, h⟩ : {w : InfinitePlace K // w.IsReal}))
    exact ⟨σ.symm ⟨w, hw⟩⟩
  let cj : ι → Prop := fun i => φ i ≠ (σ i).1.embedding
  let IA : AddSubgroup K := ((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup
  let E : K →+ (ι → ℂ) :=
    { toFun := fun a i => s * φ i a
      map_zero' := by
        funext i
        simp
      map_add' := fun a b => by
        funext i
        simp [mul_add] }
  have hE : Function.Injective E := by
    intro a b hab
    obtain ⟨i0⟩ := hne
    have h1 : s * φ i0 a = s * φ i0 b := congrFun hab i0
    exact (φ i0).injective (mul_left_cancel₀ hs h1)
  let f : mixedSpace K → (ι → ℂ) := fun x i => s * phiMap σ cj x i
  let g : (ι → ℂ) → mixedSpace K := fun v => phiInv σ cj (fun i => s⁻¹ * v i)
  have hgf : ∀ x, g (f x) = x := fun x => by
    show phiInv σ cj (fun i => s⁻¹ * (s * phiMap σ cj x i)) = x
    simp only [inv_mul_cancel_left₀ hs]
    exact phiInv_phiMap σ cj x
  have hfg : ∀ y, f (g y) = y := fun y => by
    show (fun i => s * phiMap σ cj (phiInv σ cj (fun j => s⁻¹ * y j)) i) = y
    simp only [phiMap_phiInv, mul_inv_cancel_left₀ hs]
  have hg : ∀ y z, g (y + z) = g y + g z := fun y z => by
    show phiInv σ cj (fun i => s⁻¹ * (y + z) i) =
      phiInv σ cj (fun i => s⁻¹ * y i) + phiInv σ cj (fun i => s⁻¹ * z i)
    rw [← phiInv_add]
    congr 1
    funext i
    simp [mul_add]
  have hfE : ∀ a, f (mixedEmbedding K a) = E a := fun a => by
    funext i
    exact congrArg (s * ·) (congrFun (phiMap_mixedEmbedding_eq φ σ hφ a) i)
  let L : AddSubgroup (ι → ℂ) := IA.map E
  have hLM : ∀ w, w ∈ L ↔ g w ∈ (idealLattice K I).toAddSubgroup := by
    intro w
    constructor
    · intro hw
      obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hw
      have h1 : g (E a) = mixedEmbedding K a := by rw [← hfE a, hgf]
      rw [h1, Submodule.mem_toAddSubgroup, mem_idealLattice_iff']
      exact ⟨a, ha, rfl⟩
    · intro hw
      rw [Submodule.mem_toAddSubgroup, mem_idealLattice_iff'] at hw
      obtain ⟨a, ha, hae⟩ := hw
      refine AddSubgroup.mem_map.2 ⟨a, ha, ?_⟩
      rw [← hfE a, hae, hfg]
  obtain ⟨FL, hFLm, hFL⟩ := idealLattice_fd K I
  have hgm : Measurable g :=
    (measurable_phiInv σ cj).comp (measurable_pi_lambda _ fun i => measurable_const.mul (measurable_pi_apply i))
  have hdL : ∀ y, ∃! m : L, (m : ι → ℂ) + y ∈ g ⁻¹' FL :=
    existsUnique_add_mem_preimage_of_additive_equiv f g hgf hfg hg _ L hLM FL hFL
  let Λ' : AddSubgroup (ι → ℂ) := Λ.map E
  have hle : Λ' ≤ L := AddSubgroup.map_mono (fun a ha => hΛ a ha)
  have hri : Λ'.relIndex L ≠ 0 := by
    show Λ'.relIndex (IA.map E) ≠ 0
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq_self_of_injective hE]
    exact hk0
  have hfin : (Λ'.addSubgroupOf L).FiniteIndex := ⟨hri⟩
  obtain ⟨G, hGm, hG⟩ := coset_fd L Λ' hle hfin (g ⁻¹' FL) (hFLm.preimage hgm) hdL
  refine ⟨G, hGm, fun v => ?_⟩
  obtain ⟨⟨w, hw⟩, hwG, hu⟩ := hG v
  obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hw
  refine ⟨⟨a, ha⟩, hwG, ?_⟩
  rintro ⟨b, hb⟩ hbG
  have h3 := hu ⟨E b, AddSubgroup.mem_map_of_mem E hb⟩ hbG
  exact Subtype.ext (hE (congrArg Subtype.val h3))
end Formalism.L2.SG.NGCut.SplitEmbedding
