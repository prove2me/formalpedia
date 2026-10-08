-- Prove2me | solution 1 for ClarkeWright64.Savings.tableII_iff_fleetFeasible
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:46:52.268651+00:00
-- url     : https://prove2.me/submissions/370aa142-eaac-4286-b792-e3e1d9af445b

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance

open ClarkeWright64.Savings
open scoped BigOperators

private theorem partition_card {n : ℕ} (κ : Multiset (ℝ × Fin (n+1))) (i : Fin (n+1)) :
    (κ.filter (fun p => i < p.2)).card =
      ∑ k ∈ Finset.Ioi i, (κ.filter (fun p => p.2 = k)).card := by
  classical
  induction κ using Multiset.induction_on with
  | empty => simp
  | cons p κ ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, apply_ite,
      Multiset.card_singleton, Multiset.card_zero, Finset.sum_add_distrib]
    simp [ih, Finset.sum_ite_eq', Finset.sum_ite, add_comm]

private theorem necessary {M n : ℕ} (I : Instance M n) (hC : StrictMono I.C)
    (loads : Multiset ℝ) (h : I.FleetFeasible loads) : I.TableIIOK loads := by
  classical
  obtain ⟨κ,hκ,hcap,hcount⟩ := h
  intro i
  rw [← hκ, Multiset.filter_map, Multiset.card_map]
  have hle : (κ.filter (fun p => I.C i < p.1)).card ≤
      (κ.filter (fun p => i < p.2)).card := by
    apply Multiset.card_le_card
    apply Multiset.le_filter.mpr
    refine ⟨Multiset.filter_le _ _, ?_⟩
    intro p hp
    obtain ⟨hp,hl⟩ := Multiset.mem_filter.mp hp
    by_contra hnot
    have hc := hC.monotone (le_of_not_gt hnot)
    have := hcap p hp
    linarith
  calc
    ((κ.filter (fun p => I.C i < p.1)).card : ℕ∞)
      ≤ ((κ.filter (fun p => i < p.2)).card : ℕ∞) := by exact_mod_cast hle
    _ = ∑ k ∈ Finset.Ioi i, ((κ.filter (fun p => p.2 = k)).card : ℕ∞) := by
      rw [partition_card, Nat.cast_sum]
    _ ≤ ∑ k ∈ Finset.Ioi i, I.x k := Finset.sum_le_sum (fun k hk => hcount k)

private theorem available {M n : ℕ} (I : Instance M n) (hx : I.x 0 = ⊤)
    (loads : Multiset ℝ) (hok : I.TableIIOK loads) (l : ℝ) (hl : l ∈ loads) :
    ∃ j : Fin (n+1), l ≤ I.C j ∧ 0 < I.x j := by
  classical
  by_contra h
  have hnone : ∀ j, l ≤ I.C j → I.x j = 0 := by
    intro j hj
    have hh : ¬ 0 < I.x j := by intro hp; exact h ⟨j,hj,hp⟩
    exact le_antisymm (le_of_not_gt hh) bot_le
  have h0 : I.C 0 < l := by
    by_contra hh
    have := hnone 0 (le_of_not_gt hh)
    rw [hx] at this
    exact ENat.top_ne_zero this
  let s : Finset (Fin (n+1)) := Finset.univ.filter (fun j => I.C j < l)
  have hs : s.Nonempty := ⟨0, by simp [s,h0]⟩
  let i := s.max' hs
  have hi : I.C i < l := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hsum : ∑ k ∈ Finset.Ioi i, I.x k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply hnone
    by_contra hkl
    have hks : k ∈ s := by simp [s,lt_of_not_ge hkl]
    have hki := Finset.le_max' s k hks
    exact (not_le_of_gt (Finset.mem_Ioi.mp hk)) hki
  have hc := hok i
  rw [hsum] at hc
  have hcard : 0 < (loads.filter (fun v => I.C i < v)).card :=
    Multiset.card_pos.mpr (by
      intro hz
      have hm := Multiset.mem_filter.mpr ⟨hl,hi⟩
      rw [hz] at hm
      simpa using hm)
  have hpos : (0 : ℕ∞) < ((loads.filter (fun v => I.C i < v)).card : ℕ∞) := by exact_mod_cast hcard
  exact (not_le_of_gt hpos) hc

private theorem sufficient {M n : ℕ} (loads : Multiset ℝ) :
    ∀ (I : Instance M n), StrictMono I.C → I.x 0 = ⊤ →
      I.TableIIOK loads → I.FleetFeasible loads := by
  classical
  induction loads using Multiset.strongInductionOn with
  | ih loads ih =>
    intro I hC hx hok
    by_cases he : loads = 0
    · subst loads
      exact ⟨0, by simp, by simp, by simp⟩
    have hn : loads.toFinset.Nonempty := by
      obtain ⟨l,hl⟩ := Multiset.exists_mem_of_ne_zero he
      exact ⟨l,Multiset.mem_toFinset.mpr hl⟩
    let l := loads.toFinset.max' hn
    have hl : l ∈ loads := Multiset.mem_toFinset.mp (Finset.max'_mem _ hn)
    let rest := loads.erase l
    have hr : l ::ₘ rest = loads := Multiset.cons_erase hl
    have hmax : ∀ z ∈ rest, z ≤ l := by
      intro z hz
      exact Finset.le_max' _ _ (Multiset.mem_toFinset.mpr (Multiset.mem_of_mem_erase hz))
    obtain ⟨j,hjl,hjx⟩ := available I hx loads hok l hl
    let J : Instance M n := { I with x := fun k => if k=j then I.x k - 1 else I.x k }
    have hJ0 : J.x 0 = ⊤ := by
      dsimp [J]; split_ifs <;> simp [hx]
    have hJok : J.TableIIOK rest := by
      intro i
      change ((rest.filter (fun z => I.C i < z)).card : ℕ∞) ≤ _
      by_cases hli : I.C i < l
      · have hcount := hok i
        rw [← hr, Multiset.filter_cons_of_pos _ hli, Multiset.card_cons, Nat.cast_add, Nat.cast_one] at hcount
        by_cases hji : i < j
        · have hsum : (∑ k ∈ Finset.Ioi i, J.x k) + 1 = ∑ k ∈ Finset.Ioi i, I.x k := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_Ioi.mpr hji),
                ← Finset.sum_erase_add _ _ (Finset.mem_Ioi.mpr hji)]
            have hs : ∑ k ∈ (Finset.Ioi i).erase j, J.x k = ∑ k ∈ (Finset.Ioi i).erase j, I.x k := by
              apply Finset.sum_congr rfl
              intro k hk; simp [J, (Finset.mem_erase.mp hk).1]
            rw [hs]
            dsimp [J]
            rw [if_pos rfl, add_assoc, tsub_add_cancel_of_le ((Order.one_le_iff_ne_zero).mpr (ne_of_gt hjx))]
          rw [← hsum] at hcount
          apply ENat.addLECancellable_natCast 1
          simpa only [add_comm, ENat.natCast_one] using hcount
        · have hs : ∑ k ∈ Finset.Ioi i, J.x k = ∑ k ∈ Finset.Ioi i, I.x k := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkj : k ≠ j := by intro hh; subst k; exact hji (Finset.mem_Ioi.mp hk)
            simp [J,hkj]
          rw [hs]
          exact le_trans (le_add_of_nonneg_right bot_le) hcount
      · have hz : rest.filter (fun z => I.C i < z) = 0 := by
          apply Multiset.filter_eq_nil.mpr
          intro z hz
          exact not_lt_of_ge (le_trans (hmax z hz) (le_of_not_gt hli))
        change ((rest.filter (fun z => I.C i < z)).card : ℕ∞) ≤ _
        rw [hz]; simp
    have hrest : rest < loads := by
      rw [← hr]
      exact Multiset.lt_cons_self _ _
    obtain ⟨κ,hκ,hcap,hcount⟩ := ih rest hrest J hC hJ0 hJok
    refine ⟨(l,j) ::ₘ κ, ?_, ?_, ?_⟩
    · simp only [Multiset.map_cons,hκ]; exact hr
    · intro p hp
      rcases Multiset.mem_cons.mp hp with rfl | hp
      · exact hjl
      · exact hcap p hp
    · intro k
      by_cases hk : j=k
      · subst k
        rw [Multiset.filter_cons]
        simp only [Prod.snd, if_pos rfl, Multiset.card_add, Multiset.card_singleton,
          Nat.cast_add, Nat.cast_one]
        have hc : ((κ.filter (fun p => p.2=j)).card : ℕ∞) ≤ I.x j - 1 := by
          simpa only [J,if_pos rfl,if_true] using hcount j
        have hh := add_le_add_right hc (1 : ℕ∞)
        rw [add_comm (1 : ℕ∞) (I.x j - 1),
          tsub_add_cancel_of_le ((Order.one_le_iff_ne_zero).mpr (ne_of_gt hjx))] at hh
        simpa only [if_true,Multiset.card_singleton,ENat.natCast_one] using hh
      · rw [Multiset.filter_cons]
        simp only [Prod.snd, if_neg hk, Multiset.zero_add]
        simpa [J,Ne.symm hk] using hcount k

theorem solution {M n : ℕ} (I : Instance M n) (hC : StrictMono I.C)
    (hx : I.x 0 = ⊤) (loads : Multiset ℝ) :
    I.TableIIOK loads ↔ I.FleetFeasible loads :=
  ⟨sufficient loads I hC hx, necessary I hC loads⟩

#print axioms solution
