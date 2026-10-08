-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.card_le_rank_of_indep_transversal
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:37:07.518632+00:00
-- url     : https://prove2.me/submissions/1ab10a7d-4ecf-40e8-9cc1-f992bdbe58cb

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
import Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_eq_card_of_nonzero_transversal
import Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_map_algebraMap
import Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_mono
import Theorems.Thm_DiscreteConvex_MixedMatrices_mixed_matrix_rank_max_formula

set_option autoImplicit false

namespace DiscreteConvex.MixedMatrices

/-- Core of `card_le_rank_of_indep_transversal`: the columns `Q_c` (`c ∈ Jq`) restricted to the rows
outside `S = ψ(Je)` are linearly independent, because together with the unit vectors `e_{ψ c}`
(`c ∈ Je`) they are the independent family `v`. -/
lemma pk_card_le_subRank {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C] (Q : Matrix R C K) (J Jq Je : Finset C)
    (v : C → R → F) (hind : LinearIndepOn F v (J : Set C)) (hJ : J = Jq ∪ Je)
    (hdisj : Disjoint Jq Je) (ψ : C → R) (hψinj : Set.InjOn ψ (Je : Set C))
    (hq : ∀ c ∈ Jq, v c = fun r : R => algebraMap K F (Q r c))
    (he : ∀ c ∈ Je, v c = (Pi.single (ψ c) (1 : F) : R → F)) :
    Jq.card ≤ MatrixSubRank Q (Je.image ψ)ᶜ Jq := by
  classical
  rw [← matrixSubRank_map_algebraMap (F := F) Q (Je.image ψ)ᶜ Jq]
  unfold MatrixSubRank
  rw [Matrix.rank_eq_finrank_span_cols]
  have hLI : LinearIndependent F (Matrix.col ((Q.map (algebraMap K F)).submatrix
      ((↑) : ↥(Je.image ψ)ᶜ → R) ((↑) : ↥Jq → C))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c
    set S : Finset R := Je.image ψ with hS
    -- extend `g` to all of `C`
    let g' : C → F := fun c => if h : c ∈ Jq then g ⟨c, h⟩ else 0
    let u : R → F := ∑ c ∈ Jq, g' c • (fun r : R => algebraMap K F (Q r c))
    have hu0 : ∀ r, r ∉ S → u r = 0 := by
      intro r hr
      have h := congrFun hg ⟨r, Finset.mem_compl.2 hr⟩
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, Matrix.submatrix_apply,
        Matrix.map_apply, smul_eq_mul, Pi.zero_apply] at h
      have e : u r = ∑ i : ↥Jq, g i * algebraMap K F (Q r i) := by
        simp only [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [← Finset.sum_coe_sort Jq]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [g']
      rw [e]; exact h
    have hu : u = ∑ s ∈ S, u s • (Pi.single s (1 : F) : R → F) := by
      funext r
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero]
      rw [Finset.sum_ite_eq]
      by_cases hr : r ∈ S
      · simp [hr]
      · simp [hr, hu0 r hr]
    have hu' : u = ∑ c ∈ Je, u (ψ c) • v c := by
      calc u = ∑ s ∈ S, u s • (Pi.single s (1 : F) : R → F) := hu
        _ = ∑ c ∈ Je, u (ψ c) • (Pi.single (ψ c) (1 : F) : R → F) := by
          rw [hS, Finset.sum_image hψinj]
        _ = ∑ c ∈ Je, u (ψ c) • v c :=
          Finset.sum_congr rfl (fun c hc => by rw [he c hc])
    let G : C → F := fun c => if c ∈ Jq then g' c else - u (ψ c)
    have hsum : ∑ c ∈ J, G c • v c = 0 := by
      rw [hJ, Finset.sum_union hdisj]
      have h1 : ∑ c ∈ Jq, G c • v c = u := by
        refine Finset.sum_congr rfl (fun c hc => ?_) |>.trans rfl
        simp only [G, if_pos hc, hq c hc]
      have h2 : ∑ c ∈ Je, G c • v c = - u := by
        have : ∀ c ∈ Je, G c • v c = -(u (ψ c) • v c) := by
          intro c hc
          have hcq : c ∉ Jq := fun h => Finset.disjoint_left.1 hdisj h hc
          simp [G, hcq]
        rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib, ← hu']
      rw [h1, h2, add_neg_cancel]
    have hGc := (linearIndepOn_finset_iff.1 hind) G hsum c.1 (by rw [hJ]; exact Finset.mem_union_left _ c.2)
    simpa [G, g', c.2] using hGc
  rw [finrank_span_eq_card hLI]
  simp

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices

theorem solution {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T)
    (J : Finset C) (v : C → R → F)
    (hv : ∀ c ∈ J, v c ∈ ({fun r : R => algebraMap K F (Q r c)} ∪
      (fun s : R => (Pi.single s (1 : F) : R → F)) '' {s : R | T s c ≠ 0}))
    (hind : LinearIndepOn F v (J : Set C)) :
    J.card ≤ A.rank := by
  classical
  have hinj : Set.InjOn v (J : Set C) := hind.injOn
  have hcls : ∀ c ∈ J, v c = (fun r : R => algebraMap K F (Q r c)) ∨
      ∃ s, T s c ≠ 0 ∧ v c = (Pi.single s (1 : F) : R → F) := by
    intro c hc
    rcases hv c hc with h | ⟨s, hs, hsv⟩
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, hsv.symm⟩
  by_cases hR : Nonempty R
  · have hex : ∀ c, ∃ s : R, c ∈ J → v c ≠ (fun r : R => algebraMap K F (Q r c)) →
        (T s c ≠ 0 ∧ v c = (Pi.single s (1 : F) : R → F)) := by
      intro c
      by_cases h : c ∈ J ∧ v c ≠ (fun r : R => algebraMap K F (Q r c))
      · rcases hcls c h.1 with h' | ⟨s, hs⟩
        · exact absurd h' h.2
        · exact ⟨s, fun _ _ => hs⟩
      · exact ⟨hR.some, fun hc hne => absurd ⟨hc, hne⟩ h⟩
    choose ψ hψ using hex
    set Jq : Finset C := J.filter (fun c => v c = fun r : R => algebraMap K F (Q r c)) with hJq
    set Je : Finset C := J.filter (fun c => ¬ v c = fun r : R => algebraMap K F (Q r c)) with hJe
    have hJ : J = Jq ∪ Je := (Finset.filter_union_filter_not_eq _ _).symm
    have hdisj : Disjoint Jq Je := Finset.disjoint_filter_filter_not J J _
    have hqJ : ∀ c ∈ Jq, v c = fun r : R => algebraMap K F (Q r c) := fun c hc =>
      (Finset.mem_filter.1 hc).2
    have heJ : ∀ c ∈ Je, T (ψ c) c ≠ 0 ∧ v c = (Pi.single (ψ c) (1 : F) : R → F) := by
      intro c hc
      have := Finset.mem_filter.1 hc
      exact hψ c this.1 this.2
    have hψinj : Set.InjOn ψ (Je : Set C) := by
      intro c hc c' hc' h
      have hc1 := (heJ c hc).2
      have hc2 := (heJ c' hc').2
      have hcJ : c ∈ J := (Finset.mem_filter.1 hc).1
      have hcJ' : c' ∈ J := (Finset.mem_filter.1 hc').1
      apply hinj hcJ hcJ'
      rw [hc1, hc2, h]
    -- (a) the Q-part
    have hA1 : Jq.card ≤ MatrixSubRank Q (Je.image ψ)ᶜ Jq :=
      pk_card_le_subRank Q J Jq Je v hind hJ hdisj ψ hψinj hqJ (fun c hc => (heJ c hc).2)
    -- (b) the T-part
    have hB := matrixSubRank_eq_card_of_nonzero_transversal T hA.2 Je ψ hψinj
      (fun c hc => (heJ c hc).1)
    have hB' : MatrixSubRank T (Je.image ψ) Je ≤ MatrixSubRank T (Je.image ψ) Jqᶜ :=
      matrixSubRank_mono T (Finset.Subset.refl _) (by
        intro c hc
        exact Finset.mem_compl.2 (fun h => Finset.disjoint_left.1 hdisj h hc))
    -- (c) Theorem 12.7
    have h127 := mixed_matrix_rank_max_formula A Q T hA
    have hle : MatrixSubRank Q (Je.image ψ)ᶜ Jq + MatrixSubRank T (Je.image ψ)ᶜᶜ Jqᶜ ≤ A.rank := by
      rw [h127]
      refine le_trans ?_ (Finset.le_sup (f := fun I => (Finset.univ : Finset (Finset C)).sup
        (fun J => MatrixSubRank Q I J + MatrixSubRank T Iᶜ Jᶜ)) (Finset.mem_univ (Je.image ψ)ᶜ))
      exact Finset.le_sup (f := fun J => MatrixSubRank Q (Je.image ψ)ᶜ J +
        MatrixSubRank T (Je.image ψ)ᶜᶜ Jᶜ) (Finset.mem_univ Jq)
    rw [compl_compl] at hle
    have hcard : J.card = Jq.card + Je.card := by
      rw [hJq, hJe]; exact (Finset.card_filter_add_card_filter_not _).symm
    omega
  · -- `R` empty: every vector is `0`, so `J = ∅`
    rcases J.eq_empty_or_nonempty with h | ⟨c, hc⟩
    · simp [h]
    · exfalso
      refine hind.ne_zero (Finset.mem_coe.2 hc) ?_
      funext r
      exact (hR ⟨r⟩).elim

#print axioms solution
