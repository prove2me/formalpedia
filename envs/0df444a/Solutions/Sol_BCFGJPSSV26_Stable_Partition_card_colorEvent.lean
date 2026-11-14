-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Partition.card_colorEvent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:21.228655+00:00
-- url     : https://prove2.me/submissions/87aaf8c1-d4aa-4311-9329-30269ac92115

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coloring
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_Coloring

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

open Classical in
/-- **The color event is likely.** -/
theorem Partition.card_colorEvent {X : Ctx} (H : Hyp X) {Λ₁ : List (Dummy X.I)}
    {w₁ : ClientWitness X Λ₁} {LS' : List ℕ} {Λ₂ : List (Dummy X.I)}
    {w₂ : ClusterWitness w₁ (X.I.centers LS') Λ₂} (Q : Partition w₂) (hnd : LS'.Nodup)
    (hm : ∀ i ∈ LS', i < X.I.m) (hk : LS'.length ≤ X.I.k) :
    (1 / 4 : ℝ) ^ X.s * ((2 : ℝ) ^ X.b) ^ X.I.k ≤
      (univ.filter fun u : Fin X.I.k → Fin (2 ^ X.b) ↦
        Q.ColorEvent (X.I.centers (redOf LS' (colors X.b LS' (toCh u))))
          (X.I.centers (blueOf LS' (colors X.b LS' (toCh u))))).card := by
  have hb : 1 ≤ X.b := by
    have := X.P.N_pos
    simp only [Ctx.b, Par.bits]
    omega
  have hZL : Q.Zstar ⊆ X.I.centers LS' := Q.Zstar_sub.trans sdiff_subset
  have hpos : ∀ c ∈ X.I.centers LS', ∃ p, ∃ hp : p < LS'.length, LS'[p] = c.1 :=
    fun c hc ↦ List.getElem_of_mem (Instance.mem_centers.1 hc)
  -- the centers to be blue
  let B : Finset (Fin X.I.m) := if h : (X.I.centers LS' \ Q.Zstar).Nonempty then
    Q.Zstar.image fun c ↦ X.I.near (X.I.centers LS' \ Q.Zstar) h (.inr c) else ∅
  have hBL : B ⊆ X.I.centers LS' \ Q.Zstar := by
    intro d hd
    simp only [B] at hd
    split_ifs at hd with h
    · obtain ⟨c, -, rfl⟩ := mem_image.1 hd
      exact Instance.near_mem h _
    · simp at hd
  have hBcard : B.card ≤ Q.Zstar.card := by
    simp only [B]
    split_ifs
    · exact card_image_le
    · simp
  -- the allowed chunks at each position
  let T : Finset (Fin (2 ^ X.b)) := univ.filter fun v ↦ cbit X.b v = true
  let F : Finset (Fin (2 ^ X.b)) := univ.filter fun v ↦ cbit X.b v = false
  let A : Fin X.I.k → Finset (Fin (2 ^ X.b)) := fun e ↦
    if ∃ c ∈ Q.Zstar, LS'[e.1]? = some c.1 then T
    else if ∃ c ∈ B, LS'[e.1]? = some c.1 then F else univ
  have hsub : Fintype.piFinset A ⊆ univ.filter fun u : Fin X.I.k → Fin (2 ^ X.b) ↦
      Q.ColorEvent (X.I.centers (redOf LS' (colors X.b LS' (toCh u))))
        (X.I.centers (blueOf LS' (colors X.b LS' (toCh u)))) := by
    intro u hu
    rw [Fintype.mem_piFinset] at hu
    rw [mem_filter]
    refine ⟨mem_univ _, fun c hc ↦ ?_, fun c hc h ↦ ?_⟩
    · obtain ⟨p, hp, hpc⟩ := hpos c (hZL hc)
      have hpk : p < X.I.k := by omega
      have hA : A ⟨p, hpk⟩ = T := by
        refine ite_eq_left_iff.2 fun hn ↦ absurd ⟨c, hc, ?_⟩ hn
        exact (List.getElem?_eq_getElem hp).trans (congrArg some hpc)
      have hbit := hu ⟨p, hpk⟩
      rw [hA] at hbit
      rw [Instance.mem_centers, ← hpc]
      refine mem_redOf_colors hp ?_
      rw [toCh_of_lt u hpk]
      exact (mem_filter.1 hbit).2
    · have hdB : X.I.near (X.I.centers LS' \ Q.Zstar) h (.inr c) ∈ B := by
        simp only [B, h, ↓reduceDIte]
        exact mem_image_of_mem _ hc
      have hdL := mem_sdiff.1 (hBL hdB)
      obtain ⟨p, hp, hpd⟩ := hpos _ hdL.1
      have hpk : p < X.I.k := by omega
      have hnZ : ¬ ∃ c ∈ Q.Zstar, LS'[p]? = some c.1 := by
        rintro ⟨c', hc', h'⟩
        rw [List.getElem?_eq_getElem hp, Option.some.injEq, hpd] at h'
        exact hdL.2 (Fin.ext h' ▸ hc')
      have hA : A ⟨p, hpk⟩ = F := by
        simp only [A]
        rw [if_neg hnZ]
        refine ite_eq_left_iff.2 fun hn ↦ absurd ⟨_, hdB, ?_⟩ hn
        exact (List.getElem?_eq_getElem hp).trans (congrArg some hpd)
      have hbit := hu ⟨p, hpk⟩
      rw [hA] at hbit
      rw [Instance.mem_centers, ← hpd]
      refine mem_blueOf_colors hp ?_
      rw [toCh_of_lt u hpk]
      exact (mem_filter.1 hbit).2
  -- the number of constrained positions
  let cnt : Fin X.I.k → ℕ := fun e ↦
    if ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1 then 1 else 0
  have hK : (2 : ℝ) ^ X.b = 2 * 2 ^ (X.b - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcT : (T.card : ℝ) = 2 ^ (X.b - 1) := by exact_mod_cast card_cbit hb true
  have hcF : (F.card : ℝ) = 2 ^ (X.b - 1) := by exact_mod_cast card_cbit hb false
  have hA : ∀ e, (2 : ℝ) ^ X.b * (1 / 2) ^ cnt e ≤ (A e).card := by
    intro e
    simp only [A, cnt]
    by_cases h1 : ∃ c ∈ Q.Zstar, LS'[e.1]? = some c.1
    · have h1' : ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1 :=
        let ⟨c, hc, h⟩ := h1
        ⟨c, mem_union_left _ hc, h⟩
      rw [if_pos h1, if_pos h1', hcT, hK, pow_one]
      linarith
    · by_cases h2 : ∃ c ∈ B, LS'[e.1]? = some c.1
      · have h2' : ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1 :=
          let ⟨c, hc, h⟩ := h2
          ⟨c, mem_union_right _ hc, h⟩
        rw [if_neg h1, if_pos h2, if_pos h2', hcF, hK, pow_one]
        linarith
      · have h3 : ¬ ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1 := by
          rintro ⟨c, hc, h⟩
          rcases mem_union.1 hc with hc | hc
          · exact h1 ⟨c, hc, h⟩
          · exact h2 ⟨c, hc, h⟩
        rw [if_neg h1, if_neg h2, if_neg h3, pow_zero, mul_one, card_univ,
          Fintype.card_fin]
        push_cast
        rfl
  have hC : ∑ e, cnt e =
      (univ.filter fun e : Fin X.I.k ↦ ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1).card := by
    simp only [cnt]
    rw [sum_boole, Nat.cast_id]
  have hZs : Q.Zstar.card ≤ X.s := by
    have h1 := Q.Zstar_card
    have h2 := Q.card_OLam_add_OP_le H
    have h3 := Instance.card_centers hnd hm
    rw [List.length_append] at h2
    omega
  have hCle : (univ.filter fun e : Fin X.I.k ↦
      ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1).card ≤ 2 * X.s := by
    have h1 : (univ.filter fun e : Fin X.I.k ↦ ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1).card ≤
        ((Q.Zstar ∪ B).map Fin.valEmbedding).card := by
      refine card_le_card_of_injOn (fun e ↦ (LS'[e.1]?).getD 0) (fun e he ↦ ?_)
        (fun e he e' he' h ↦ ?_)
      · obtain ⟨c, hc, h⟩ := (mem_filter.1 he).2
        simp only [h, Option.getD_some]
        exact mem_map_of_mem _ hc
      · obtain ⟨c, -, hc⟩ := (mem_filter.1 he).2
        obtain ⟨c', -, hc'⟩ := (mem_filter.1 he').2
        simp only [hc, hc', Option.getD_some] at h
        rw [h] at hc
        obtain ⟨h1, h1'⟩ := List.getElem?_eq_some_iff.1 hc
        obtain ⟨h2, h2'⟩ := List.getElem?_eq_some_iff.1 hc'
        exact Fin.ext (hnd.getElem_inj_iff.1 (h1'.trans h2'.symm))
    rw [card_map] at h1
    have h2 := card_union_le Q.Zstar B
    omega
  have hfinal : (1 / 4 : ℝ) ^ X.s * ((2 : ℝ) ^ X.b) ^ X.I.k ≤ ∏ e, ((A e).card : ℝ) := by
    calc (1 / 4 : ℝ) ^ X.s * ((2 : ℝ) ^ X.b) ^ X.I.k ≤
          ((2 : ℝ) ^ X.b) ^ X.I.k * (1 / 2) ^ (∑ e, cnt e) := by
          rw [mul_comm]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hC]
          calc (1 / 4 : ℝ) ^ X.s = (1 / 2) ^ (2 * X.s) := by
                rw [pow_mul]
                norm_num
            _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hCle
      _ = ∏ e, (2 : ℝ) ^ X.b * (1 / 2) ^ (cnt e) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum]
      _ ≤ _ := prod_le_prod (fun e _ ↦ by positivity) (fun e _ ↦ hA e)
  calc _ ≤ ∏ e, ((A e).card : ℝ) := hfinal
    _ = (Fintype.piFinset A).card := by
        rw [Fintype.card_piFinset]
        push_cast
        rfl
    _ ≤ _ := by exact_mod_cast card_le_card hsub

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Partition.card_colorEvent := @BCFGJPSSV26.Stable.Partition.card_colorEvent
