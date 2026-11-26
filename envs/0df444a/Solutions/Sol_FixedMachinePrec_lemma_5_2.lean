-- Prove2me | solution 1 for FixedMachinePrec.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:24:12.283526+00:00
-- url     : https://prove2.me/submissions/1b816a77-d7e2-49c7-9b8a-6a4ef61dedae

import Theorems.Thm_FixedMachinePrec_lemma_5_1
import Theorems.Thm_FixedMachinePrec_serialSchedule_meets_job_count
import Theorems.Thm_FixedMachinePrec_fill_slot_schedule_with_dummies
import Theorems.Thm_FixedMachinePrec_extract_padded_deadline

open FixedMachinePrec

private theorem slot_capacity {G : Instance} {m T : ℕ} {τ : Fin G.n → ℕ}
    (h : IsSlotSchedule G m T τ) : G.n ≤ T * m := by
  have hmap : ((Finset.univ : Finset (Fin G.n)) : Set (Fin G.n)).MapsTo τ (Finset.Icc 1 T) :=
    fun x _ => Finset.mem_Icc.mpr (h.1 x)
  have e := Finset.card_eq_sum_card_fiberwise hmap
  calc
    G.n = ∑ t ∈ Finset.Icc 1 T, (Finset.univ.filter fun x => τ x = t).card := by simpa using e
    _ ≤ ∑ _t ∈ Finset.Icc 1 T, m := Finset.sum_le_sum fun t _ => h.2.1 t
    _ = T * m := by simp [Nat.card_Icc]

theorem solution (m : ℕ) (hm : 1 ≤ m) (G : Instance) (hG : G.Acyclic) (hn : 0 < G.n) :
    (∀ T : ℕ, T < ceilDiv G.n m → ¬ DeadlineFeasible G m T) ∧
    (∀ T : ℕ, G.n ≤ T → DeadlineFeasible G m T) ∧
    (∀ T : ℕ, ceilDiv G.n m ≤ T → T < G.n →
      (DeadlineFeasible G m T ↔
        ∃ S : List (Finset (Fin (m * T))),
          IsFullSchedule (paddedPrec G (m * T)) m Finset.univ S ∧ S.length = T) ∧
      m * T ≤ m * G.n) := by
  have slots (T : ℕ) (h : DeadlineFeasible G m T) : ∃ τ, IsSlotSchedule G m T τ := by
    obtain ⟨σ, hσ, ht⟩ := h
    obtain ⟨u, τ, hv, hu⟩ := lemma_5_1 m hm G hG σ hσ
    have hut : u ≤ T := by exact_mod_cast hu.trans ht
    exact ⟨τ, fun x => ⟨(hv.1 x).1, ((hv.1 x).2).trans hut⟩, hv.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro T hT hf
    obtain ⟨τ,hτ⟩ := slots T hf
    have hcap := slot_capacity hτ
    have hbad := (Nat.le_div_iff_mul_le hm).mp (show T+1 ≤ (G.n+m-1)/m from hT)
    rw [Nat.add_mul, Nat.one_mul] at hbad
    omega
  · intro T ht
    obtain ⟨σ, _, hσ, hc⟩ := serialSchedule_meets_job_count m hm G hG
    exact ⟨σ, hσ, hc.trans (by exact_mod_cast ht)⟩
  · intro T hlow hhigh
    refine ⟨⟨?_, ?_⟩, Nat.mul_le_mul_left _ hhigh.le⟩
    · intro hf
      obtain ⟨τ,hτ⟩ := slots T hf
      exact fill_slot_schedule_with_dummies G m T τ hτ
    · rintro ⟨S,hS,hlen⟩
      have hquot : (G.n+m-1)/m < T+1 := Nat.lt_succ_of_le hlow
      have h := (Nat.div_lt_iff_lt_mul hm).mp hquot
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm T m] at h
      obtain ⟨σ, _, hσ, hc⟩ := extract_padded_deadline G m T (by omega) S hS hlen
      exact ⟨σ, hσ, hc⟩
