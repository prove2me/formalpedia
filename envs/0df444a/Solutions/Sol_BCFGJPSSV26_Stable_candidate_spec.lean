-- Prove2me | solution 1 for BCFGJPSSV26.Stable.candidate_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:04:05.421267+00:00
-- url     : https://prove2.me/submissions/cd74d61f-77c0-46bb-9253-08ad9860cad7

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coloring
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Definitions.Def_BuhaiPapers_Background_Tuples
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Submod
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_Submod
public import Theorems.Thm_BCFGJPSSV26_Stable_gfun_isSubmod
public import Theorems.Thm_BCFGJPSSV26_Stable_seqGreedy_bound

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26

namespace Raw

open Stable

end Raw

namespace Stable

section Helpers

open Finset

section Greedy

variable (g : List ℕ → ℚ) (parts : List (List ℕ)) (Vs : List (List ℕ))

end Greedy

/-- **The exact sequential greedy** picks one element of each part and satisfies the guarantee
of `BCFGJPSSV26.Stable.seqGreedy_bound`, for `g` computing a function `G` with `G ∅ - G`
monotone and submodular. -/
private theorem seqGreedyQ_spec {I : Instance} (hm : 1 ≤ I.m) {g : List ℕ → ℚ}
    {G : Finset (Fin I.m) → ℝ}
    (hg : ∀ l : List ℕ, (∀ i ∈ l, i < I.m) → (g l : ℝ) = G (I.centers l))
    (hmono : IsMonoF fun Y ↦ G ∅ - G Y) (hsub : IsSubmod fun Y ↦ G ∅ - G Y)
    {parts : List (List ℕ)} (hp : ∀ j < parts.length, parts.getD j [] ≠ [])
    (hpm : ∀ j < parts.length, ∀ i ∈ parts.getD j [], i < I.m)
    {N B : ℕ} (hN : 1 ≤ N) (hB : N ^ parts.length ≤ B) :
    (seqGreedyQ g parts N B).length = parts.length ∧
    (∀ j < parts.length, (seqGreedyQ g parts N B).getD j 0 ∈ parts.getD j []) ∧
    ∀ o : Fin parts.length → Fin I.m, (∀ j : Fin parts.length, (o j).1 ∈ parts.getD j []) →
      (1 - ((N : ℝ) / (N + 1)) ^ N) * (G ∅ - G (univ.image o)) ≤
        G ∅ - G (I.centers (seqGreedyQ g parts N B)) := by
  classical
  obtain ⟨hLlen, hLj, hent⟩ := greedyR_spec g parts (Tuples.tuples B N parts.length) hp N
  set Vs := Tuples.tuples B N parts.length with hVs
  set L := greedyR g parts Vs N with hL
  have hseq : seqGreedyQ g parts N B = pickQ L (argminBy (fun V ↦ g (pickQ L V)) Vs []) := rfl
  have hVsne : Vs ≠ [] :=
    List.ne_nil_of_mem (Tuples.ofFn_mem_tuples hB fun _ ↦ (⟨0, hN⟩ : Fin N))
  obtain ⟨hVminmem, hVminle⟩ := argminBy_spec (fun V ↦ g (pickQ L V)) hVsne []
  obtain ⟨hVminlen, hVminlt⟩ := Tuples.mem_tuples_le hVminmem
  set Vmin := argminBy (fun V ↦ g (pickQ L V)) Vs [] with hVmin
  -- all entries are facilities
  have hLm : ∀ j', ∀ a ∈ L.getD j' [], a < I.m := by
    intro j' a ha
    by_cases hj' : j' < parts.length
    · obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 ha
      have ht' : t < N := by rw [← hLj j' hj']; exact ht
      have := (hent j' hj' t ht').1
      rw [List.getD_eq_getElem _ _ ht] at this
      exact hpm j' hj' _ this
    · rw [List.getD_eq_default _ _ (by rw [hLlen]; omega)] at ha
      simp at ha
  have hm0 : 0 < I.m := by omega
  rw [hseq]
  refine ⟨by simp [pickQ, hLlen], fun j hj ↦ ?_, fun o ho ↦ ?_⟩
  · have hjL : j < (pickQ L Vmin).length := by simp [pickQ, hLlen, hj]
    rw [List.getD_eq_getElem _ _ hjL]
    simp only [pickQ, List.getElem_map, List.getElem_range]
    have hVj : Vmin.getD j 0 < N := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hVminlt _ (List.getElem_mem _)
    exact (hent j hj _ hVj).1
  -- the greedy rule on functions
  obtain ⟨Lst', hLst'⟩ : ∃ Lst' : Fin parts.length → Fin N → Fin I.m,
      ∀ j t, ((Lst' j t : Fin I.m) : ℕ) = (L.getD j []).getD t 0 :=
    ⟨fun j t ↦ ⟨_, getD_lt_of (hLm j) hm0 t⟩, fun _ _ ↦ rfl⟩
  have hgain : ∀ (j : Fin parts.length) (t : Fin N) (e : Fin I.m),
      ∑ v : Fin parts.length → Fin N,
        (G (greedyQ Lst' j t v) - G (insert e (greedyQ Lst' j t v))) =
        (gainQ g L j t Vs e : ℝ) := by
    intro j t e
    rw [gainQ, Rat.cast_list_sum, List.map_map, sum_tuples hB]
    refine sum_congr rfl fun v _ ↦ ?_
    have hQm := greedyQL_lt hLm hm0 j t (List.ofFn fun j ↦ (v j : ℕ))
    have hQm' : ∀ i ∈ (e : ℕ) :: greedyQL L j t (List.ofFn fun j ↦ (v j : ℕ)), i < I.m := by
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact e.2
      · exact hQm i hi
    rw [← centers_greedyQL hLlen Lst' hLst' j t v]
    simp only [Function.comp_apply, Rat.cast_sub]
    rw [hg _ hQm, hg _ hQm', centers_cons e.2]
  have hIS : IsSeqGreedy (fun Y ↦ G ∅ - G Y) (fun j ↦ I.centers (parts.getD j [])) Lst' := by
    intro j t
    refine ⟨?_, fun e he ↦ ?_⟩
    · simp only [Instance.mem_centers, hLst']
      exact (hent j j.2 t t.2).1
    · have h3 := (hent j j.2 t t.2).2 e.1 (Instance.mem_centers.1 he)
      rw [← hLst'] at h3
      simp only [sub_sub_sub_cancel_left]
      rw [hgain j t e, hgain j t (Lst' j t)]
      exact_mod_cast h3
  have hbound := seqGreedy_bound (f := fun Y ↦ G ∅ - G Y) hmono hsub (by simp) (by omega) hIS o
    (fun j ↦ by simpa only [Instance.mem_centers] using ho j)
  have hpick : ∀ v : Fin parts.length → Fin N, G ∅ - G (univ.image fun j ↦ Lst' j (v j)) ≤
      G ∅ - G (I.centers (pickQ L Vmin)) := by
    intro v
    rw [← centers_pickQ hLlen Lst' hLst' v, ← hg _ (pickQ_lt hLm hm0 _),
      ← hg _ (pickQ_lt hLm hm0 _)]
    have h1 := hVminle _ (Tuples.ofFn_mem_tuples hB v)
    have h2 : (g (pickQ L Vmin) : ℝ) ≤ g (pickQ L (List.ofFn fun j ↦ (v j : ℕ))) := by
      exact_mod_cast h1
    linarith
  have hsum : ∑ v : Fin parts.length → Fin N, (G ∅ - G (univ.image fun j ↦ Lst' j (v j))) ≤
      (G ∅ - G (I.centers (pickQ L Vmin))) * (N : ℝ) ^ parts.length := by
    calc _ ≤ ∑ v : Fin parts.length → Fin N, (G ∅ - G (I.centers (pickQ L Vmin))) :=
          sum_le_sum fun v _ ↦ hpick v
      _ = _ := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  have hNpos : (0 : ℝ) < (N : ℝ) ^ parts.length := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  exact le_of_mul_le_mul_right (hbound.trans hsum) hNpos

variable {I : Instance}

/-- **The specification of the candidate**, unfolded. -/
private theorem candidate_spec_aux (hv : I.Valid) {N B : ℕ} (hN : 1 ≤ N) {LS' : List ℕ}
    (hnd : LS'.Nodup) (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ} (hΛ : (toRaw I).ValidDums Λ)
    {col : List Bool} {p' : ℕ} (hB : N ^ (Λ.length + p') ≤ B)
    (hzr : (LS'.length + (Λ.length + p')) - I.k ≤ (redOf LS' col).length)
    (hballs : ∀ l ∈ Λ, (toRaw I).ballQ l ≠ []) :
    let red := redOf LS' col
    let blue := blueOf LS' col
    let z := (LS'.length + (Λ.length + p')) - I.k
    let Y := seqGreedyQ ((toRaw I).gQ LS' Λ red blue z)
      (Λ.map (toRaw I).ballQ ++ List.replicate p' (List.range I.m)) N B
    let Zl := (red.mergeSort fun c c' ↦
      decide ((toRaw I).hclQ LS' Λ blue c Y ≤ (toRaw I).hclQ LS' Λ blue c' Y)).take z
    let T := ((LS'.filter fun c ↦ decide (c ∉ Zl)) ++ Y).dedup
    T.Nodup ∧ (∀ i ∈ T, i < I.m) ∧ T.length ≤ I.k ∧
      ∃ Y' Zh : Finset (Fin I.m), I.centers T = (I.centers LS' \ Zh) ∪ Y' ∧
        (∀ l ∈ toDums I Λ, ∃ i ∈ Y', i ∈ l.ball) ∧ Zh ⊆ I.centers red ∧
        Zh.card = z ∧
        ∑ c ∈ Zh, hcl I (I.centers LS') (toDums I Λ) (I.centers blue) c Y' =
          g₂ I (I.centers LS') (toDums I Λ) (I.centers red) (I.centers blue) z Y' ∧
        GreedyGuarantee I N (gfun I (I.centers LS') (toDums I Λ) (I.centers red)
          (I.centers blue) z) (toDums I Λ) p' Y' := by
  intro red blue z Y Zl T
  classical
  have hm1 : 1 ≤ I.m := hv.one_le_m
  have hΛ' : ∀ l ∈ Λ, l.1 < I.n + I.m := hΛ
  -- red and blue
  have hredsub : red.Sublist LS' := redOf_sublist LS' col
  have hrednd : red.Nodup := hnd.sublist hredsub
  have hredLS : ∀ c ∈ red, c ∈ LS' := fun c hc ↦ hredsub.subset hc
  have hredm : ∀ c ∈ red, c < I.m := fun c hc ↦ hm c (hredLS c hc)
  have hbluem : ∀ c ∈ blue, c < I.m := fun c hc ↦ hm c ((blueOf_sublist LS' col).subset hc)
  have hzr' : z ≤ red.length := hzr
  -- the parts
  have hplen : (partsOf I Λ p').length = Λ.length + p' := length_partsOf I Λ p'
  have hballm : ∀ l, ∀ i ∈ (toRaw I).ballQ l, i < I.m :=
    fun l i hi ↦ List.mem_range.1 (List.mem_of_mem_filter hi)
  have hp : ∀ j < (partsOf I Λ p').length, (partsOf I Λ p').getD j [] ≠ [] := by
    intro j hj
    rw [hplen] at hj
    by_cases h : j < Λ.length
    · rw [getD_partsOf_lt h]
      exact hballs _ (List.getElem_mem _)
    · rw [getD_partsOf_ge (by omega) hj]
      exact List.ne_nil_of_mem (List.mem_range.2 (by omega : 0 < I.m))
  have hpm : ∀ j < (partsOf I Λ p').length, ∀ i ∈ (partsOf I Λ p').getD j [], i < I.m := by
    intro j hj i hi
    rw [hplen] at hj
    by_cases h : j < Λ.length
    · rw [getD_partsOf_lt h] at hi
      exact hballm _ i hi
    · rw [getD_partsOf_ge (by omega) hj] at hi
      exact List.mem_range.1 hi
  -- the greedy
  set G := gfun I (I.centers LS') (toDums I Λ) (I.centers red) (I.centers blue) z with hG
  have hgG : ∀ l : List ℕ, (∀ i ∈ l, i < I.m) →
      ((toRaw I).gQ LS' Λ red blue z l : ℝ) = G (I.centers l) :=
    fun l hl ↦ gQ_toRaw hm hΛ hredLS hrednd hbluem hzr' hl
  obtain ⟨hYlen, hYmem, hYG⟩ : Y.length = (partsOf I Λ p').length ∧
      (∀ j < (partsOf I Λ p').length, Y.getD j 0 ∈ (partsOf I Λ p').getD j []) ∧
      ∀ o : Fin (partsOf I Λ p').length → Fin I.m,
        (∀ j : Fin (partsOf I Λ p').length, (o j).1 ∈ (partsOf I Λ p').getD j []) →
        (1 - ((N : ℝ) / (N + 1)) ^ N) * (G ∅ - G (univ.image o)) ≤ G ∅ - G (I.centers Y) :=
    seqGreedyQ_spec hm1 hgG (gfun_isMonoF hv _ _ _ _ _) (gfun_isSubmod hv _ _ _ _ _) hp hpm hN
      (by rw [hplen]; exact hB)
  have hYm : ∀ i ∈ Y, i < I.m := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hi
    have hjp : j < (partsOf I Λ p').length := hYlen ▸ hj
    have := hYmem j hjp
    rw [List.getD_eq_getElem _ _ hj] at this
    exact hpm j hjp _ this
  -- the centers to close
  have hZperm := List.mergeSort_perm red (fun c c' ↦
    decide ((toRaw I).hclQ LS' Λ blue c Y ≤ (toRaw I).hclQ LS' Λ blue c' Y))
  have hZlsub : ∀ c ∈ Zl, c ∈ red := fun c hc ↦ hZperm.subset (List.mem_of_mem_take hc)
  have hZlnd : Zl.Nodup := (hZperm.nodup_iff.2 hrednd).sublist (List.take_sublist _ _)
  have hZllen : Zl.length = z := by
    change (List.take z _).length = z
    rw [List.length_take, hZperm.length_eq]
    omega
  have hZlm : ∀ c ∈ Zl, c < I.m := fun c hc ↦ hredm c (hZlsub c hc)
  -- the candidate
  have hTm : ∀ i ∈ T, i < I.m := by
    intro i hi
    simp only [T, List.mem_dedup, List.mem_append, List.mem_filter] at hi
    rcases hi with hi | hi
    · exact hm i hi.1
    · exact hYm i hi
  have hTc : I.centers T = (I.centers LS' \ I.centers Zl) ∪ I.centers Y := by
    ext i
    simp only [T, Instance.mem_centers, List.mem_dedup, List.mem_append, List.mem_filter,
      mem_union, mem_sdiff, decide_eq_true_eq]
  have hTlen : T.length ≤ I.k := by
    have h1 : T.length = (I.centers T).card :=
      (Instance.card_centers (List.nodup_dedup _) hTm).symm
    have h2 : (I.centers T).card ≤ (I.centers LS' \ I.centers Zl).card + (I.centers Y).card := by
      rw [hTc]
      exact card_union_le _ _
    have h3 : (I.centers LS' \ I.centers Zl).card = LS'.length - z := by
      rw [card_sdiff_of_subset (Instance.centers_mono fun c hc ↦ hredLS c (hZlsub c hc)),
        Instance.card_centers hnd hm, Instance.card_centers hZlnd hZlm, hZllen]
    have h4 : (I.centers Y).card ≤ Λ.length + p' :=
      (Instance.card_centers_le Y).trans (by rw [hYlen, hplen])
    have h5 : z ≤ LS'.length := hzr'.trans hredsub.length_le
    have hz : z = (LS'.length + (Λ.length + p')) - I.k := rfl
    omega
  -- the balls
  have hYball : ∀ l ∈ toDums I Λ, ∃ i ∈ I.centers Y, i ∈ l.ball := by
    intro l hl
    rw [toDums_eq_pmap hΛ', List.mem_pmap] at hl
    obtain ⟨a, haΛ, rfl⟩ := hl
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 haΛ
    have hjp : j < (partsOf I Λ p').length := by rw [hplen]; omega
    have hmem := hYmem j hjp
    rw [getD_partsOf_lt hj] at hmem
    have hjY : j < Y.length := by rw [hYlen]; exact hjp
    rw [List.getD_eq_getElem _ _ hjY] at hmem
    exact ⟨⟨Y[j], hYm _ (List.getElem_mem _)⟩, Instance.mem_centers.2 (List.getElem_mem _),
      (Raw.mem_ballQ (hΛ' _ haΛ)).1 hmem⟩
  -- the sum of the `z` smallest
  have hkey : ∀ c ∈ I.centers red,
      hcl I (I.centers LS') (toDums I Λ) (I.centers blue) c (I.centers Y) =
        ((toRaw I).hclQ LS' Λ blue c Y : ℝ) :=
    fun c hc ↦ (hclQ_toRaw hm hΛ hbluem hYm (hredLS _ (Instance.mem_centers.1 hc))).symm
  have hZs : ∑ c ∈ I.centers Zl, hcl I (I.centers LS') (toDums I Λ) (I.centers blue) c
      (I.centers Y) = g₂ I (I.centers LS') (toDums I Λ) (I.centers red) (I.centers blue) z
      (I.centers Y) := by
    unfold g₂
    rw [sum_congr rfl fun c hc ↦ hkey c (Instance.centers_mono hZlsub hc),
      sumSmallest_congr hkey]
    exact sum_take_mergeSort hrednd hredm (fun c ↦ (toRaw I).hclQ LS' Λ blue c Y) hzr'
  -- the greedy guarantee
  have hGG : GreedyGuarantee I N G (toDums I Λ) p' (I.centers Y) := by
    unfold GreedyGuarantee
    intro o ho E hE
    have hlenD : (toDums I Λ).length = Λ.length := length_toDums' hΛ'
    have hjE : ∀ j : Fin (partsOf I Λ p').length, ¬ j.1 < Λ.length →
        j.1 - Λ.length < E.card := by
      intro j hj
      have := j.2
      omega
    let o' : Fin (partsOf I Λ p').length → Fin I.m := fun j ↦
      if h : j.1 < Λ.length then o ⟨j.1, by rw [hlenD]; exact h⟩
      else (E.equivFin.symm ⟨j.1 - Λ.length, hjE j h⟩ : Fin I.m)
    have ho' : ∀ j : Fin (partsOf I Λ p').length, (o' j).1 ∈ (partsOf I Λ p').getD j [] := by
      intro j
      by_cases h : j.1 < Λ.length
      · have h1 : o' j = o ⟨j.1, by rw [hlenD]; exact h⟩ := dif_pos h
        rw [h1, getD_partsOf_lt h]
        have := ho ⟨j.1, by rw [hlenD]; exact h⟩
        rw [List.get_eq_getElem, getElem_toDums hΛ' h] at this
        exact (Raw.mem_ballQ (hΛ' _ (List.getElem_mem _))).2 this
      · have : j.1 < Λ.length + p' := by have := j.2; omega
        rw [getD_partsOf_ge (by omega) this]
        exact List.mem_range.2 (o' j).2
    have himg : univ.image o' = univ.image o ∪ E := by
      ext i
      simp only [mem_image, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨j, rfl⟩
        by_cases h : j.1 < Λ.length
        · have h1 : o' j = o ⟨j.1, by rw [hlenD]; exact h⟩ := dif_pos h
          exact .inl ⟨_, h1.symm⟩
        · right
          have h1 : o' j = (E.equivFin.symm ⟨j.1 - Λ.length, hjE j h⟩ : Fin I.m) :=
            dif_neg h
          rw [h1]
          exact (E.equivFin.symm _).2
      · rintro (⟨i₀, rfl⟩ | hi)
        · have h : i₀.1 < Λ.length := by have := i₀.2; omega
          refine ⟨⟨i₀.1, by rw [hplen]; omega⟩, ?_⟩
          exact dif_pos h
        · have hb := (E.equivFin ⟨i, hi⟩).2
          have h : ¬ (Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ) < Λ.length) := by omega
          refine ⟨⟨Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ), by rw [hplen]; omega⟩, ?_⟩
          have h1 : o' ⟨Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ), by rw [hplen]; omega⟩ =
              (E.equivFin.symm ⟨Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ) - Λ.length,
                hjE ⟨_, by rw [hplen]; omega⟩ h⟩ : Fin I.m) := dif_neg h
          rw [h1]
          have h2 : (⟨Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ) - Λ.length,
              hjE ⟨_, by rw [hplen]; omega⟩ h⟩ : Fin E.card) = E.equivFin ⟨i, hi⟩ :=
            Fin.ext (by simp)
          rw [h2, Equiv.symm_apply_apply]
    have := hYG o' ho'
    rw [himg] at this
    exact this
  exact ⟨List.nodup_dedup _, hTm, hTlen, I.centers Y, I.centers Zl, hTc, hYball,
    Instance.centers_mono hZlsub, by rw [Instance.card_centers hZlnd hZlm, hZllen], hZs, hGG⟩

end Helpers

variable {I : Instance}

open Classical in
/-- **The specification of a computed candidate.** -/
theorem candidate_spec (hv : I.Valid) {N s B : ℕ} (hN : 1 ≤ N) {LS' : List ℕ}
    (hnd : LS'.Nodup) (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ} (hΛ : (toRaw I).ValidDums Λ)
    {col : List Bool} (hcol : col.length = LS'.length) {p' : ℕ} (hB : N ^ (Λ.length + p') ≤ B)
    {T : List ℕ} (hT : candidate N (toRaw I) s B LS' Λ col p' = some T) :
    T.Nodup ∧ (∀ i ∈ T, i < I.m) ∧ T.length ≤ I.k ∧
      ∃ Y Zh : Finset (Fin I.m), I.centers T = (I.centers LS' \ Zh) ∪ Y ∧
        (∀ l ∈ toDums I Λ, ∃ i ∈ Y, i ∈ l.ball) ∧ Zh ⊆ I.centers (redOf LS' col) ∧
        Zh.card = (LS'.length + (Λ.length + p')) - I.k ∧
        ∑ c ∈ Zh, hcl I (I.centers LS') (toDums I Λ) (I.centers (blueOf LS' col)) c Y =
          g₂ I (I.centers LS') (toDums I Λ) (I.centers (redOf LS' col))
            (I.centers (blueOf LS' col)) ((LS'.length + (Λ.length + p')) - I.k) Y ∧
        GreedyGuarantee I N (gfun I (I.centers LS') (toDums I Λ) (I.centers (redOf LS' col))
          (I.centers (blueOf LS' col)) ((LS'.length + (Λ.length + p')) - I.k))
          (toDums I Λ) p' Y := by
  have _ := hcol
  have hT' := hT
  dsimp only [candidate] at hT'
  have hk : (toRaw I).k = I.k := rfl
  by_cases hskip : s < Λ.length + p' ∨
      (redOf LS' col).length < LS'.length + (Λ.length + p') - (toRaw I).k ∨
        (Λ.any fun l ↦ ((toRaw I).ballQ l).isEmpty) = true
  · rw [if_pos hskip] at hT'
    exact absurd hT' (by simp)
  rw [if_neg hskip] at hT'
  have hzr : (LS'.length + (Λ.length + p')) - I.k ≤ (redOf LS' col).length := by
    simp only [not_or, not_lt] at hskip
    have := hskip.2.1
    omega
  have hballs : ∀ l ∈ Λ, (toRaw I).ballQ l ≠ [] := by
    intro l hl he
    simp only [not_or] at hskip
    exact hskip.2.2 (List.any_eq_true.2 ⟨l, hl, by simp [he]⟩)
  obtain rfl := (Option.some.inj hT').symm
  exact candidate_spec_aux hv hN hnd hm hΛ hB hzr hballs

end Stable

end BCFGJPSSV26

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.candidate_spec := @BCFGJPSSV26.Stable.candidate_spec
