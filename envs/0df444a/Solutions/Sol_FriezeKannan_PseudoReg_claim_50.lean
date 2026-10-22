-- Prove2me | solution 1 for FriezeKannan.PseudoReg.claim_50
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:36:34.769407+00:00
-- url     : https://prove2.me/submissions/198513f1-ddbc-46fe-a755-36154755af6f

import Mathlib
import Definitions.Def_FriezeKannan_PseudoReg_Setting



namespace FriezeKannan.PseudoReg

section aux
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma g92_sum_part (Q : Finpartition (Finset.univ : Finset V)) (S : Finset V)
    (f : Finset V → ℝ) :
    ∑ i ∈ S, f (Q.part i) = ∑ U ∈ Q.parts, ((S ∩ U).card : ℝ) * f U := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := Q.parts) (g := Q.part)
    (fun i _ => by simp)]
  refine Finset.sum_congr rfl fun U hU => ?_
  have h1 : S.filter (fun i => Q.part i = U) = S ∩ U := by
    ext i
    simp [Finset.mem_filter, Finset.mem_inter, Q.part_eq_iff_mem hU]
  calc ∑ i ∈ S.filter (fun i => Q.part i = U), f (Q.part i)
      = ∑ i ∈ S.filter (fun i => Q.part i = U), f U :=
        Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2])
    _ = _ := by rw [Finset.sum_const, h1]; simp

lemma g92_sum_part2 (Q : Finpartition (Finset.univ : Finset V)) (S T : Finset V)
    (F : Finset V → Finset V → ℝ) :
    ∑ i ∈ S, ∑ j ∈ T, F (Q.part i) (Q.part j) =
      ∑ U ∈ Q.parts, ∑ W ∈ Q.parts, ((S ∩ U).card : ℝ) * ((T ∩ W).card : ℝ) * F U W := by
  rw [g92_sum_part Q S (fun U => ∑ j ∈ T, F U (Q.part j))]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [g92_sum_part Q T (fun W => F U W), Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

lemma g92_lin_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (g x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) (c : ℝ)
    (h : ∀ I ⊆ s, |∑ i ∈ I, g i| ≤ c) : |∑ i ∈ s, x i * g i| ≤ c := by
  have up : ∑ i ∈ s, x i * g i ≤ ∑ i ∈ s.filter (fun i => 0 < g i), g i := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun i hi => ?_
    have := hx0 i hi
    have := hx1 i hi
    by_cases hg : 0 < g i
    · simp only [hg, if_true]; nlinarith
    · simp only [hg, if_false]; nlinarith [not_lt.1 hg]
  have lo : ∑ i ∈ s.filter (fun i => g i < 0), g i ≤ ∑ i ∈ s, x i * g i := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun i hi => ?_
    have := hx0 i hi
    have := hx1 i hi
    by_cases hg : g i < 0
    · simp only [hg, if_true]; nlinarith
    · simp only [hg, if_false]; nlinarith [not_lt.1 hg]
  have h1 := abs_le.1 (h _ (Finset.filter_subset (fun i => 0 < g i) s))
  have h2 := abs_le.1 (h _ (Finset.filter_subset (fun i => g i < 0) s))
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma g92_bilin_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (β : ι → ι → ℝ)
    (x y : ι → ℝ) (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1)
    (hy0 : ∀ i ∈ s, 0 ≤ y i) (hy1 : ∀ i ∈ s, y i ≤ 1) (c : ℝ)
    (h : ∀ I ⊆ s, ∀ J ⊆ s, |∑ i ∈ I, ∑ j ∈ J, β i j| ≤ c) :
    |∑ i ∈ s, ∑ j ∈ s, x i * y j * β i j| ≤ c := by
  have stepA : ∀ I ⊆ s, |∑ i ∈ I, ∑ j ∈ s, y j * β i j| ≤ c := by
    intro I hI
    have : ∑ i ∈ I, ∑ j ∈ s, y j * β i j = ∑ j ∈ s, y j * (∑ i ∈ I, β i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    rw [this]
    refine g92_lin_bound s (fun j => ∑ i ∈ I, β i j) y hy0 hy1 c ?_
    intro J hJ
    rw [Finset.sum_comm]
    exact h I hI J hJ
  have : ∑ i ∈ s, ∑ j ∈ s, x i * y j * β i j = ∑ i ∈ s, x i * (∑ j ∈ s, y j * β i j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  refine g92_lin_bound s (fun i => ∑ j ∈ s, y j * β i j) x hx0 hx1 c ?_
  intro I hI
  exact stepA I hI

lemma g92_blockSum_biUnion' (Q : Finpartition (Finset.univ : Finset V)) (B : Matrix V V ℝ)
    (I J : Finset (Finset V)) (hI : I ⊆ Q.parts) (hJ : J ⊆ Q.parts) :
    blockSum B (I.biUnion id) (J.biUnion id) = ∑ U ∈ I, ∑ W ∈ J, blockSum B U W := by
  have h1 : blockSum B (I.biUnion id) (J.biUnion id)
      = ∑ U ∈ I, ∑ i ∈ U, ∑ j ∈ J.biUnion id, B i j := by
    unfold blockSum
    rw [Finset.sum_biUnion (Q.disjoint.subset (Finset.coe_subset.2 hI))]
    rfl
  rw [h1]
  refine Finset.sum_congr rfl fun U _ => ?_
  have h2 : ∀ i, ∑ j ∈ J.biUnion id, B i j = ∑ W ∈ J, ∑ j ∈ W, B i j := by
    intro i
    rw [Finset.sum_biUnion (Q.disjoint.subset (Finset.coe_subset.2 hJ))]
    rfl
  simp only [h2]
  rw [Finset.sum_comm]
  rfl

lemma g92_avg_sum (Q : Finpartition (Finset.univ : Finset V)) (B : Matrix V V ℝ)
    (S T : Finset V) :
    blockSum (blockAvg Q B) S T =
      ∑ U ∈ Q.parts, ∑ W ∈ Q.parts, ((S ∩ U).card : ℝ) * ((T ∩ W).card : ℝ) *
        (blockSum B U W / ((U.card : ℝ) * (W.card : ℝ))) := by
  unfold blockSum
  have := g92_sum_part2 Q S T (fun U W => (∑ i ∈ U, ∑ j ∈ W, B i j) / ((U.card : ℝ) * (W.card : ℝ)))
  rw [← this]
  rfl

lemma g92_avg_bound (Q : Finpartition (Finset.univ : Finset V)) (B : Matrix V V ℝ) (c : ℝ)
    (hc : ∀ S T : Finset V, |blockSum B S T| ≤ c) (S T : Finset V) :
    |blockSum (blockAvg Q B) S T| ≤ c := by
  rw [g92_avg_sum]
  have hpos : ∀ U ∈ Q.parts, (0 : ℝ) < U.card := fun U hU =>
    Nat.cast_pos.2 (Finset.card_pos.2 (Q.nonempty_of_mem_parts hU))
  have hle : ∀ (S : Finset V) U, ((S ∩ U).card : ℝ) ≤ U.card := fun S U =>
    Nat.cast_le.2 (Finset.card_le_card Finset.inter_subset_right)
  have key := g92_bilin_bound Q.parts (fun U W => blockSum B U W)
    (fun U => ((S ∩ U).card : ℝ) / U.card) (fun W => ((T ∩ W).card : ℝ) / W.card)
    (fun U hU => by have := hpos U hU; positivity)
    (fun U hU => by rw [div_le_one (hpos U hU)]; exact hle S U)
    (fun U hU => by have := hpos U hU; positivity)
    (fun U hU => by rw [div_le_one (hpos U hU)]; exact hle T U) c
    (fun I hI J hJ => by
      rw [← g92_blockSum_biUnion' Q B I J hI hJ]; exact hc _ _)
  have e : ∑ U ∈ Q.parts, ∑ W ∈ Q.parts, ((S ∩ U).card : ℝ) * ((T ∩ W).card : ℝ) *
        (blockSum B U W / ((U.card : ℝ) * (W.card : ℝ))) =
      ∑ U ∈ Q.parts, ∑ W ∈ Q.parts, ((S ∩ U).card : ℝ) / U.card * (((T ∩ W).card : ℝ) / W.card)
        * blockSum B U W := by
    refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun W _ => ?_
    ring
  rw [e]; exact key

lemma g92_blockAvg_sub (Q : Finpartition (Finset.univ : Finset V)) (A M : Matrix V V ℝ) :
    blockAvg Q (A - M) = blockAvg Q A - blockAvg Q M := by
  ext p q
  simp only [blockAvg, blockSum, Matrix.sub_apply, Finset.sum_sub_distrib, sub_div]

lemma g92_blockAvg_compat (P Q : Finpartition (Finset.univ : Finset V)) (hQP : Q ≤ P)
    (M : Matrix V V ℝ) (hM : Compatible P M) : blockAvg Q M = M := by
  ext p q
  have key : ∀ p' q', Q.part p = Q.part p' → Q.part q = Q.part q' → M p' q' = M p q := by
    intro p' q' hp hq
    have hP : ∀ a b : V, Q.part a = Q.part b → P.part a = P.part b := by
      intro a b hab
      obtain ⟨v, hv, hsub⟩ := hQP (Q.part_mem.2 (Finset.mem_univ a))
      have ha : a ∈ v := hsub (Q.mem_part (Finset.mem_univ a))
      have hb : b ∈ v := hsub (hab ▸ Q.mem_part (Finset.mem_univ b))
      rw [P.part_eq_of_mem hv ha, P.part_eq_of_mem hv hb]
    exact (hM p p' q q' (hP _ _ hp) (hP _ _ hq)).symm
  have hs : blockSum M (Q.part p) (Q.part q) =
      ((Q.part p).card : ℝ) * ((Q.part q).card : ℝ) * M p q := by
    unfold blockSum
    have : ∀ i ∈ Q.part p, ∑ j ∈ Q.part q, M i j = ((Q.part q).card : ℝ) * M p q := by
      intro i hi
      have hi' : Q.part p = Q.part i := (Q.part_eq_of_mem (Q.part_mem.2 (Finset.mem_univ p)) hi).symm
      rw [Finset.sum_congr rfl (g := fun _ => M p q)]
      · simp
      · intro j hj
        have hj' : Q.part q = Q.part j :=
          (Q.part_eq_of_mem (Q.part_mem.2 (Finset.mem_univ q)) hj).symm
        exact key i j hi' hj'
    rw [Finset.sum_congr rfl this]
    simp; ring
  have hp0 : ((Q.part p).card : ℝ) ≠ 0 := by
    have := Q.part_nonempty.2 (Finset.mem_univ p)
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 this).ne'
  have hq0 : ((Q.part q).card : ℝ) ≠ 0 := by
    have := Q.part_nonempty.2 (Finset.mem_univ q)
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 this).ne'
  show blockSum M (Q.part p) (Q.part q) / _ = M p q
  rw [hs]
  field_simp

end aux

theorem g92_lemma_7a {V : Type*} [Fintype V] [DecidableEq V]
    (A M : Matrix V V ℝ) (P Q : Finpartition (Finset.univ : Finset V)) (hQP : Q ≤ P)
    (hM : Compatible P M) (c : ℝ)
    (hc : ∀ S T : Finset V, |blockSum (A - M) S T| ≤ c) :
    ∀ S T : Finset V, |blockSum (A - blockAvg Q A) S T| ≤ 2 * c := by
  intro S T
  have h1 : A - blockAvg Q A = (A - M) - blockAvg Q (A - M) := by
    rw [g92_blockAvg_sub, g92_blockAvg_compat P Q hQP M hM]
    abel
  have h2 : blockSum (A - blockAvg Q A) S T =
      blockSum (A - M) S T - blockSum (blockAvg Q (A - M)) S T := by
    rw [h1]
    simp only [blockSum, Matrix.sub_apply, Finset.sum_sub_distrib]
  rw [h2]
  calc _ ≤ |blockSum (A - M) S T| + |blockSum (blockAvg Q (A - M)) S T| := abs_sub _ _
    _ ≤ c + c := add_le_add (hc S T) (g92_avg_bound Q (A - M) c hc S T)
    _ = 2 * c := by ring

theorem g92_cutSum_compatible {V : Type*} [Fintype V] [DecidableEq V]
    (s : ℕ) (Rs Cs : Fin s → Finset V) (d : Fin s → ℝ) :
    Compatible (atomPartition Rs Cs) (cutSum Rs Cs d) := by
  have atom : ∀ p p' : V, (atomPartition Rs Cs).part p = (atomPartition Rs Cs).part p' →
      ∀ F ∈ (Finset.univ.image Rs ∪ Finset.univ.image Cs), (p ∈ F ↔ p' ∈ F) := by
    intro p p' hpp F hF
    have hmem := (atomPartition Rs Cs).part_mem.2 (Finset.mem_univ p)
    obtain ⟨_, Qs, hQ, hEq⟩ := Finpartition.mem_atomise.1 hmem
    have hp : p ∈ (atomPartition Rs Cs).part p := (atomPartition Rs Cs).mem_part (Finset.mem_univ p)
    have hp' : p' ∈ (atomPartition Rs Cs).part p := by
      rw [hpp]; exact (atomPartition Rs Cs).mem_part (Finset.mem_univ p')
    have hp1 := (Finset.ext_iff.1 hEq p).2 hp
    have hp2 := (Finset.ext_iff.1 hEq p').2 hp'
    simp only [Finset.mem_filter] at hp1 hp2
    rw [← hp1.2 F hF, ← hp2.2 F hF]
  intro p p' q q' hp hq
  simp only [cutSum, Matrix.sum_apply, cutMatrix]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 := atom p p' hp (Rs t) (by simp)
  have h2 := atom q q' hq (Cs t) (by simp)
  simp only [h1, h2]

theorem g92_eq_47 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : Finpartition (Finset.univ : Finset V)) (S T : Finset V) :
    blockSum (G.adjMatrix ℝ) S T = ((G.interedges S T).card : ℝ) ∧
    blockSum (blockAvg Q (G.adjMatrix ℝ)) S T =
      ∑ Vi ∈ Q.parts, ∑ Vj ∈ Q.parts,
        (G.edgeDensity Vi Vj : ℝ) * ((S ∩ Vi).card : ℝ) * ((T ∩ Vj).card : ℝ) ∧
    blockSum (G.adjMatrix ℝ) S T - blockSum (blockAvg Q (G.adjMatrix ℝ)) S T =
      delta G Q S T := by
  have h1 : ∀ S T : Finset V, blockSum (G.adjMatrix ℝ) S T = ((G.interedges S T).card : ℝ) := by
    intro S T
    unfold blockSum
    rw [SimpleGraph.interedges_def, Finset.card_filter, Finset.sum_product]
    push_cast
    simp [SimpleGraph.adjMatrix_apply]
  have h2 : blockSum (blockAvg Q (G.adjMatrix ℝ)) S T =
      ∑ Vi ∈ Q.parts, ∑ Vj ∈ Q.parts,
        (G.edgeDensity Vi Vj : ℝ) * ((S ∩ Vi).card : ℝ) * ((T ∩ Vj).card : ℝ) := by
    rw [g92_avg_sum]
    refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun W _ => ?_
    rw [h1, SimpleGraph.edgeDensity_def]
    push_cast
    ring
  refine ⟨h1 S T, h2, ?_⟩
  rw [h2, h1]
  rfl

theorem g92_claim_50 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (s : ℕ) (Rs Cs : Fin s → Finset V) (d : Fin s → ℝ)
    (hD : ∀ S T : Finset V,
      |blockSum (G.adjMatrix ℝ - cutSum Rs Cs d) S T| ≤ ε * (Fintype.card V : ℝ) ^ 2) :
    IsPseudoRegular G (atomPartition Rs Cs) (2 * ε) := by
  intro S T _
  have h := g92_lemma_7a (G.adjMatrix ℝ) (cutSum Rs Cs d) (atomPartition Rs Cs)
    (atomPartition Rs Cs) le_rfl (g92_cutSum_compatible s Rs Cs d) _ hD S T
  have h3 := (g92_eq_47 G (atomPartition Rs Cs) S T).2.2
  have h4 : blockSum (G.adjMatrix ℝ - blockAvg (atomPartition Rs Cs) (G.adjMatrix ℝ)) S T
      = delta G (atomPartition Rs Cs) S T := by
    rw [← h3]
    simp only [blockSum, Matrix.sub_apply, Finset.sum_sub_distrib]
  rw [h4] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end FriezeKannan.PseudoReg

open FriezeKannan.PseudoReg


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (s : ℕ) (Rs Cs : Fin s → Finset V) (d : Fin s → ℝ)
    (hD : ∀ S T : Finset V,
      |blockSum (G.adjMatrix ℝ - cutSum Rs Cs d) S T| ≤ ε * (Fintype.card V : ℝ) ^ 2) :
    IsPseudoRegular G (atomPartition Rs Cs) (2 * ε) := by
  exact g92_claim_50 G ε s Rs Cs d hD
