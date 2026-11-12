-- Prove2me | solution 1 for FairShares.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:24:08.314201+00:00
-- url     : https://prove2.me/submissions/6caa6f22-2732-47fa-a501-40c7911bb606

import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_LittleCharity_MMS_Setting
import Theorems.Thm_FairShares_lemma_15

namespace Aux_FairShares_lemma_16
open FairShares

private lemma list_ofFn_drop_succ {m : ℕ} {α : Type*} (f : Fin m → α) (d : ℕ) (hd : d < m) :
    (List.ofFn f).drop d = f ⟨d, hd⟩ :: (List.ofFn f).drop (d + 1) := by
  have hlen : d < (List.ofFn f).length := by simp [hd]
  rw [← List.getElem_cons_drop hlen]
  simp

private lemma exists_heavy_in_R {m : ℕ} {d : ℕ} (hd : d < m)
    (π : Fin m ≃ Fin m) (R : Finset (Fin m)) (hcard : d + R.card = m) :
    ∃ t₀ : Fin m, t₀.1 ≤ d ∧ π t₀ ∈ R := by
  let I : Finset (Fin m) :=
    (Finset.univ.filter (fun t : Fin m => t.1 ≤ d)).map π.toEmbedding
  have hI_card : I.card = d + 1 := by
    simp only [I, Finset.card_map]
    rw [← Finset.card_range (d + 1)]
    refine Finset.card_bij (fun (t : Fin m) _ => t.1) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact Finset.mem_range.mpr (by omega)
    · intro t₁ _ t₂ _ heq
      exact Fin.ext heq
    · intro k hk
      have hkm : k < m := Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) hd
      refine ⟨⟨k, hkm⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hk' := Finset.mem_range.mp hk
      omega
  have hRc_card : Rᶜ.card = d := by
    have htot := Finset.card_add_card_compl R
    rw [Fintype.card_fin] at htot
    omega
  have hnot_sub : ¬ I ⊆ Rᶜ := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  rcases Finset.not_subset.mp hnot_sub with ⟨e, heI, heR⟩
  rw [Finset.mem_compl, not_not] at heR
  rcases Finset.mem_map.mp heI with ⟨t₀, ht₀, rfl⟩
  exact ⟨t₀, (Finset.mem_filter.mp ht₀).2, heR⟩

private lemma gameVal_ge_tail {m n : ℕ} (w : Fin m → ℝ)
    (v : Finset (Fin m) → ℝ) (hv : ∀ S, v S = ∑ j ∈ S, w j)
    (π : Fin m ≃ Fin m) (hπ : ∀ i j : Fin m, i ≤ j → w (π j) ≤ w (π i))
    (ω : Fin m → Fin n) (k : Fin n) :
    ∀ (r : ℕ) (hr : r ≤ m) (R H : Finset (Fin m)),
      R.card = r → Disjoint R H →
      v H + (∑ t ∈ Finset.univ.filter (fun t : Fin m => m - r ≤ t.1 ∧ ω t = k), w (π t)) ≤
        gameVal v k ((List.ofFn ω).drop (m - r)) R H
  | 0, _, R, H, hR0, _ => by
    have hdrop : (List.ofFn ω).drop (m - 0) = [] := by simp
    have hemp : Finset.univ.filter (fun t : Fin m => m - 0 ≤ t.1 ∧ ω t = k) = ∅ := by
      ext ⟨t, ht⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [hdrop, hemp, Finset.sum_empty, add_zero, gameVal]
  | r + 1, hr, R, H, hRcard, hdisj => by
    set d := m - (r + 1)
    have hd : d < m := by omega
    have hd_succ : d + 1 = m - r := by omega
    have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
    rw [list_ofFn_drop_succ ω d hd, gameVal]
    simp only [hRne, ↓reduceDIte]
    split_ifs with hpk
    · have hsum_split :
          (∑ t ∈ Finset.univ.filter (fun t : Fin m => d ≤ t.1 ∧ ω t = k), w (π t)) =
            w (π ⟨d, hd⟩) +
              ∑ t ∈ Finset.univ.filter (fun t : Fin m => m - r ≤ t.1 ∧ ω t = k), w (π t) := by
        have hset : Finset.univ.filter (fun t : Fin m => d ≤ t.1 ∧ ω t = k) =
            insert (⟨d, hd⟩ : Fin m)
              (Finset.univ.filter (fun t : Fin m => m - r ≤ t.1 ∧ ω t = k)) := by
          ext ⟨t, ht⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Fin.ext_iff]
          constructor
          · rintro ⟨hdt, hω⟩
            rcases eq_or_lt_of_le hdt with rfl | hlt
            · exact Or.inl rfl
            · exact Or.inr ⟨by omega, hω⟩
          · rintro (rfl | ⟨hdt, hω⟩)
            · exact ⟨le_rfl, congrArg Fin.val hpk⟩
            · exact ⟨by omega, hω⟩
        have hnotmem : (⟨d, hd⟩ : Fin m) ∉
            Finset.univ.filter (fun t : Fin m => m - r ≤ t.1 ∧ ω t = k) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        rw [hset, Finset.sum_insert hnotmem]
      rcases exists_heavy_in_R hd π R (by omega) with ⟨t₀, ht₀, heR⟩
      set e := π t₀
      have hwe : w (π ⟨d, hd⟩) ≤ w e := hπ t₀ ⟨d, hd⟩ ht₀
      have heH : e ∉ H := Finset.disjoint_left.mp hdisj heR
      have hv_ins : v (insert e H) = v H + w e := by
        rw [hv, hv, Finset.sum_insert heH, add_comm]
      have hdisj' : Disjoint (R.erase e) (insert e H) := by
        rw [Finset.disjoint_insert_right]
        exact ⟨Finset.notMem_erase e R, hdisj.mono_left (Finset.erase_subset e R)⟩
      have ih := gameVal_ge_tail w v hv π hπ ω k r (by omega) (R.erase e) (insert e H)
        (by rw [Finset.card_erase_of_mem heR]; omega) hdisj'
      rw [← hd_succ] at *
      refine le_trans ?_ (Finset.le_sup' (fun x => gameVal v k ((List.ofFn ω).drop (d + 1))
        (R.erase x) (insert x H)) heR)
      rw [hsum_split]
      linarith
    · have hset : Finset.univ.filter (fun t : Fin m => d ≤ t.1 ∧ ω t = k) =
          Finset.univ.filter (fun t : Fin m => m - r ≤ t.1 ∧ ω t = k) := by
        ext ⟨t, ht⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hdt, hω⟩
          have hne : t ≠ d := by
            rintro rfl
            exact hpk hω
          exact ⟨by omega, hω⟩
        · rintro ⟨hdt, hω⟩
          exact ⟨by omega, hω⟩
      rw [hset]
      refine Finset.le_inf' hRne _ fun e heR => ?_
      have ih := gameVal_ge_tail w v hv π hπ ω k r (by omega) (R.erase e) H
        (by rw [Finset.card_erase_of_mem heR]; omega) (hdisj.mono_left (Finset.erase_subset e R))
      simpa [hd_succ] using ih

end Aux_FairShares_lemma_16

open FairShares Aux_FairShares_lemma_16

theorem solution {m n : ℕ} (hn : 1 ≤ n) (v : Finset (Fin m) → ℝ) (hv : IsAdditive v) :
    ∃ ω : Fin m → Fin n, pickShare ω v = LittleCharity.MMS.mms v n Finset.univ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rcases hv with ⟨w, _, hw⟩
  have hmms_eq : LittleCharity.MMS.mms v n Finset.univ =
      ⨆ f : Fin m → Fin n, ⨅ j : Fin n, v (Finset.univ.filter (fun g => f g = j)) := by
    unfold LittleCharity.MMS.mms
    congr 1
  -- Nonempty finite supremum in mms is attained at some partition fStar
  obtain ⟨fStar, hfStar⟩ : ∃ fStar : Fin m → Fin n,
      (⨅ j : Fin n, v (Finset.univ.filter (fun g => fStar g = j))) =
        LittleCharity.MMS.mms v n Finset.univ := by
    rw [hmms_eq]
    exact exists_eq_ciSup_of_finite
  -- Sort items in nonincreasing order of w using Tuple.sort on (-w)
  let π : Fin m ≃ Fin m := Tuple.sort (fun i : Fin m => -w i)
  have hπ : ∀ i j : Fin m, i ≤ j → w (π j) ≤ w (π i) := by
    intro i j hij
    have hmono := Tuple.monotone_sort (fun x : Fin m => -w x) hij
    dsimp [π] at *
    linarith
  let ω : Fin m → Fin n := fun t => fStar (π t)
  refine ⟨ω, le_antisymm ?_ ?_⟩
  · -- Upper bound from lemma_15 applied to the constant valuation profile
    have hfeas := FairShares.lemma_15 hn ω Set.univ
    rcases hfeas (fun _ => v) (fun _ => Set.mem_univ _) with ⟨A, hA⟩
    rw [hmms_eq]
    refine le_trans (le_ciInf fun j => hA j) ?_
    unfold bundle
    exact le_ciSup (f := fun f : Fin m → Fin n =>
      ⨅ j : Fin n, v (Finset.univ.filter (fun g => f g = j))) (Finite.bddAbove_range _) A
  · -- Lower bound: for every agent k, pickValue ω v k ≥ v {g | fStar g = k}
    rw [← hfStar]
    unfold pickShare
    refine le_ciInf fun k => ?_
    refine le_trans (ciInf_le (Finite.bddBelow_range _) k) ?_
    have htail := gameVal_ge_tail w v hw π hπ ω k m le_rfl Finset.univ ∅
      (Fintype.card_fin m) (Finset.disjoint_empty_right _)
    have hv0 : v ∅ = 0 := by rw [hw, Finset.sum_empty]
    have hsum_eq :
        (∑ t ∈ Finset.univ.filter (fun t : Fin m => m - m ≤ t.1 ∧ ω t = k), w (π t)) =
          v (Finset.univ.filter (fun g : Fin m => fStar g = k)) := by
      rw [hw]
      simp only [tsub_self, zero_le, true_and, ω]
      refine Finset.sum_bij (fun t _ => π t) ?_ ?_ ?_ ?_
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        exact ht
      · intro t₁ _ t₂ _ heq
        exact π.injective heq
      · intro g hg
        refine ⟨π.symm g, ?_, π.apply_symm_apply g⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
        simpa using hg
      · intro _ _; rfl
    unfold pickValue
    rw [hv0, zero_add, hsum_eq] at htail
    simpa [tsub_self] using htail
