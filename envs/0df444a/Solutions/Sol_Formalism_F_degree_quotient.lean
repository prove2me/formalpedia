-- Prove2me | solution 1 for Formalism.F.degree_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:45.571802+00:00
-- url     : https://prove2.me/submissions/eeac588d-1f71-4884-8937-200a58b7727a

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Theorems.Thm_P2M_Formalism_F_linearIndependent_coe_basis____9cab7951c4f4
import Theorems.Thm_Formalism_F_discreteTopology_span_range_of_linearIndependent
import Theorems.Thm_P2M_Formalism_F_span_range_coe_basis__24da96608575
import Theorems.Thm_Formalism_F_covol_eq_gram
import Theorems.Thm_Formalism_F_discreteTopology_of_le
import Theorems.Thm_Formalism_F_gram_sum_smul_eq_transpose_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
set_option maxHeartbeats 800000
namespace Formalism.F
theorem _root_.solution : DegQuot := by
  intro E _ _ _ L N hL hsat
  classical
  obtain ⟨hNL, hsat'⟩ := hsat
  haveI := hL
  haveI : DiscreteTopology N := discreteTopology_of_le hNL
  let W : Submodule ℝ E := Submodule.span ℝ (N : Set E)
  let P : E →L[ℝ] E := Wᗮ.starProjection
  have hPmem : ∀ x : E, P x ∈ Wᗮ := fun x => by
    show Wᗮ.starProjection x ∈ Wᗮ
    rw [Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  have hPsub : ∀ x : E, x - P x ∈ W := fun x => by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at h
  have horth : ∀ u ∈ W, ∀ w ∈ Wᗮ, inner ℝ u w = 0 := by
    intro u hu w hw
    first
      | exact (Submodule.mem_orthogonal W w).1 hw u hu
      | exact (Submodule.mem_orthogonal w).1 hw u hu
      | exact Submodule.inner_right_of_mem_orthogonal hu hw
  have hPW : ∀ x ∈ W, P x = 0 := by
    intro x hx
    have h2 : P x ∈ W := by
      have h := W.sub_mem hx (hPsub x)
      rwa [sub_sub_cancel] at h
    exact inner_self_eq_zero.mp (horth _ h2 _ (hPmem x))
  have hNW : ∀ x ∈ N, x ∈ W := fun x hx => Submodule.subset_span hx
  have hker : ∀ x ∈ L, P x = 0 → x ∈ N := by
    intro x hx h0
    apply hsat' x hx
    have h := hPsub x
    rwa [h0, sub_zero] at h
  set Q := quot L N with hQdef
  have hQmem : ∀ y : E, y ∈ Q ↔ ∃ x ∈ L, P x = y := by
    intro y
    show y ∈ L.map _ ↔ _
    rw [Submodule.mem_map]
    rfl
  haveI : Module.Finite ℤ Q := by
    show Module.Finite ℤ (L.map _)
    first
      | exact Module.Finite.map L _
      | exact Module.Finite.iff_fg.mpr (Submodule.FG.map _ (Module.Finite.iff_fg.mp inferInstance))
  haveI : Module.IsTorsionFree ℤ Q := Module.IsTorsionFree.mk fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    apply Subtype.ext
    have h : ((r • x : Q) : E) = ((r • y : Q) : E) := congrArg Subtype.val hxy
    rw [Submodule.coe_smul, Submodule.coe_smul] at h
    have h' : (r : ℝ) • (x : E) = (r : ℝ) • (y : E) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact h
    exact smul_right_injective E (Int.cast_ne_zero.mpr hr0) h'
  haveI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  let eQ := Module.Free.chooseBasis ℤ Q
  let bN := Module.Free.chooseBasis ℤ N
  have hlift : ∀ j, ∃ x ∈ L, P x = (eQ j : E) := fun j => (hQmem _).1 (eQ j).2
  choose ℓ hℓL hℓP using hlift
  let v : Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q → L :=
    Sum.elim (fun i => ⟨(bN i : E), hNL (bN i).2⟩) (fun j => ⟨ℓ j, hℓL j⟩)
  have hvE : ∀ k, ((v k : L) : E) = Sum.elim (fun i => (bN i : E)) ℓ k := by
    intro k
    cases k <;> rfl
  have hli : LinearIndependent ℤ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hgE : ∑ i, g (Sum.inl i) • (bN i : E) + ∑ j, g (Sum.inr j) • ℓ j = 0 := by
      have h := congrArg (fun z : L => (z : E)) hg
      simpa [Fintype.sum_sum_type, v] using h
    have hPg : ∑ j, g (Sum.inr j) • (eQ j : E) = 0 := by
      have h := congrArg P hgE
      have h1 : ∀ i, P (g (Sum.inl i) • (bN i : E)) = 0 := fun i => by
        rw [map_zsmul, hPW _ (hNW _ (bN i).2), smul_zero]
      have h2 : ∀ j, P (g (Sum.inr j) • ℓ j) = g (Sum.inr j) • (eQ j : E) := fun j => by
        rw [map_zsmul, hℓP]
      rw [map_add, map_sum, map_sum, map_zero, Finset.sum_congr rfl (fun i _ => h1 i),
        Finset.sum_const_zero, zero_add, Finset.sum_congr rfl (fun j _ => h2 j)] at h
      exact h
    have hQz : ∀ j, g (Sum.inr j) = 0 := by
      have h : ∑ j, g (Sum.inr j) • eQ j = 0 := by
        apply Subtype.ext
        simpa using hPg
      exact Fintype.linearIndependent_iff.1 eQ.linearIndependent _ h
    have hNz : ∀ i, g (Sum.inl i) = 0 := by
      have h0 : ∑ i, g (Sum.inl i) • (bN i : E) = 0 := by
        have h := hgE
        simp only [hQz, zero_smul, Finset.sum_const_zero, add_zero] at h
        exact h
      have h : ∑ i, g (Sum.inl i) • bN i = 0 := by
        apply Subtype.ext
        simpa using h0
      exact Fintype.linearIndependent_iff.1 bN.linearIndependent _ h
    intro k
    cases k with
    | inl i => exact hNz i
    | inr j => exact hQz j
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    rintro ⟨x, hx⟩ -
    have hPx : P x ∈ Q := (hQmem _).2 ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r : Module.Free.ChooseBasisIndex ℤ Q → ℤ,
        ∑ j, r j • (eQ j : E) = P x := by
      have h2 := congrArg (fun z : Q => (z : E)) (eQ.sum_repr ⟨P x, hPx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact ⟨_, h2⟩
    have hy : x - ∑ j, r j • ℓ j ∈ N := by
      apply hker
      · exact L.sub_mem hx (L.sum_mem fun j _ => L.smul_mem _ (hℓL j))
      · rw [map_sub, map_sum, ← hr]
        simp only [map_zsmul, hℓP]
        exact sub_self _
    obtain ⟨s, hs⟩ : ∃ s : Module.Free.ChooseBasisIndex ℤ N → ℤ,
        ∑ i, s i • (bN i : E) = x - ∑ j, r j • ℓ j := by
      have h2 := congrArg (fun z : N => (z : E)) (bN.sum_repr ⟨_, hy⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact ⟨_, h2⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨Sum.elim s r, ?_⟩
    apply Subtype.ext
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Submodule.coe_add,
      Submodule.coe_sum, Submodule.coe_smul, v, Submodule.coe_mk]
    rw [hs]
    abel
  let cB := Module.Basis.mk hli hsp
  have hcB : ∀ k, ((cB k : L) : E) = Sum.elim (fun i => (bN i : E)) ℓ k := by
    intro k
    rw [Module.Basis.mk_apply]
    exact hvE k
  have hindR : LinearIndependent ℝ (Sum.elim (fun i => (bN i : E)) ℓ) := by
    have h := linearIndependent_coe_basis''' L cB
    have he : (fun k => ((cB k : L) : E)) = Sum.elim (fun i => (bN i : E)) ℓ := funext hcB
    rwa [he] at h
  have hWspan : W = Submodule.span ℝ (Set.range fun i => (bN i : E)) := by
    show Submodule.span ℝ (N : Set E) = _
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (bN i : E)),
      span_range_coe_basis' N bN]
  have heQW : ∀ j, (eQ j : E) ∈ Wᗮ := fun j => by
    rw [← hℓP j]
    exact hPmem _
  have heQ : LinearIndependent ℝ (fun j => (eQ j : E)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hmem : ∑ j, a j • ℓ j ∈ W := by
      have h1 : P (∑ j, a j • ℓ j) = 0 := by
        rw [map_sum]
        simp only [map_smul, hℓP]
        exact ha
      have h := hPsub (∑ j, a j • ℓ j)
      rwa [h1, sub_zero] at h
    rw [hWspan, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨β, hβ⟩ := hmem
    have hrel : ∑ k, (Sum.elim (fun i => -β i) a k) • Sum.elim (fun i => (bN i : E)) ℓ k = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
      rw [hβ]
      exact neg_add_cancel _
    intro j
    exact Fintype.linearIndependent_iff.1 hindR _ hrel (Sum.inr j)
  haveI hQd : DiscreteTopology Q := by
    have h := discreteTopology_span_range_of_linearIndependent (fun j => (eQ j : E)) heQ
    rwa [span_range_coe_basis' Q eQ] at h
  have hrk : rk L = rk N + rk Q := by
    unfold rk
    rw [Module.finrank_eq_card_basis cB, Module.finrank_eq_card_basis bN,
      Module.finrank_eq_card_basis eQ, Fintype.card_sum]
  have hα : ∀ j, ∃ α : Module.Free.ChooseBasisIndex ℤ N → ℝ,
      ∑ i, α i • (bN i : E) = ℓ j - (eQ j : E) := by
    intro j
    have h := hPsub (ℓ j)
    rw [hℓP, hWspan, Submodule.mem_span_range_iff_exists_fun] at h
    exact h
  choose α hα using hα
  let v2 : Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q → E :=
    Sum.elim (fun i => (bN i : E)) (fun j => (eQ j : E))
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q)
      (Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q) ℝ :=
    Matrix.fromBlocks 1 (Matrix.of fun i j => α j i) 0 1
  have hcomb : (fun k => ((cB k : L) : E)) = fun k => ∑ k', M k' k • v2 k' := by
    funext k
    rw [hcB, Fintype.sum_sum_type]
    cases k with
    | inl i0 =>
      simp only [M, v2, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Sum.elim_inl,
        Sum.elim_inr, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
        Matrix.one_apply, ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    | inr j0 =>
      simp only [M, v2, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Sum.elim_inl,
        Sum.elim_inr, Matrix.of_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hα, sub_add_cancel]
  have hdetM : M.det = 1 := by
    simp only [M]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]
  have hgram : Matrix.gram ℝ v2 = Matrix.fromBlocks (Matrix.gram ℝ fun i => (bN i : E)) 0 0
      (Matrix.gram ℝ fun j => (eQ j : E)) := by
    ext a b
    rcases a with i | j <;> rcases b with i' | j' <;>
      simp only [Matrix.gram_apply, v2, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]
    all_goals first
      | rfl
      | exact horth _ (hNW _ (bN i).2) _ (heQW j')
      | (rw [real_inner_comm]; exact horth _ (hNW _ (bN i').2) _ (heQW j))
  have hdet : (Matrix.gram ℝ fun k => ((cB k : L) : E)).det =
      (Matrix.gram ℝ fun i => (bN i : E)).det * (Matrix.gram ℝ fun j => (eQ j : E)).det := by
    rw [hcomb, gram_sum_smul_eq_transpose_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      hdetM, hgram, Matrix.det_fromBlocks_zero₂₁]
    ring
  have hcovL : covol L = Real.sqrt (Matrix.gram ℝ fun k => ((cB k : L) : E)).det :=
    covol_eq_gram E L _ cB
  have hcovN : covol N = Real.sqrt (Matrix.gram ℝ fun i => (bN i : E)).det :=
    covol_eq_gram E N _ bN
  have hcovQ : covol Q = Real.sqrt (Matrix.gram ℝ fun j => (eQ j : E)).det :=
    covol_eq_gram E Q _ eQ
  have hposN : 0 < (Matrix.gram ℝ fun i => (bN i : E)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis''' N bN)).det_pos
  have hposQ : 0 < (Matrix.gram ℝ fun j => (eQ j : E)).det :=
    (Matrix.posDef_gram_of_linearIndependent heQ).det_pos
  refine ⟨hQd, hrk, ?_⟩
  unfold deg
  rw [hcovL, hcovN, hcovQ, hdet, Real.sqrt_mul hposN.le,
    Real.log_mul (Real.sqrt_pos.2 hposN).ne' (Real.sqrt_pos.2 hposQ).ne']
  ring
end Formalism.F
