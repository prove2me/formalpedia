-- Prove2me | solution 1 for ConstrainedQueueing.Nonstationary.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:35:55.44159+00:00
-- url     : https://prove2.me/submissions/111f6c4d-aff4-4986-b958-3cd589652e4e

import Mathlib
import Definitions.Def_ConstrainedQueueing_Nonstationary_Model
open ConstrainedQueueing.Nonstationary
open ConstrainedQueueing.MaxThroughput (actVec)

private theorem erase_mem {L N : ℕ} (net : Network L N) (hC1 : C1 net)
    (c : Fin N → ℝ) (hc : c ∈ coS net) (i : Fin N) :
    Function.update c i 0 ∈ coS net := by
  classical
  let f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
    { toFun := fun v => Function.update v i 0
      map_add' := by intro v w; ext k; by_cases h : k = i <;> simp [h]
      map_smul' := by intro a v; ext k; by_cases h : k = i <;> simp [h] }
  have him : f '' (actVec '' net.S) ⊆ actVec '' net.S := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s.erase i, hC1 s hs _ (Finset.erase_subset _ _), ?_⟩
    ext k
    by_cases h : k = i
    · subst k; simp [f, actVec]
    · simp [f, actVec, h]
  have hf : f c ∈ f '' coS net := ⟨c, hc, rfl⟩
  rw [coS, f.image_convexHull] at hf
  exact (convexHull_mono him) hf

private theorem update_mem {L N : ℕ} (net : Network L N) (hC1 : C1 net)
    (c : Fin N → ℝ) (hc : c ∈ coS net) (i : Fin N) (a : ℝ)
    (ha : 0 ≤ a) (hac : a ≤ c i) :
    Function.update c i a ∈ coS net := by
  classical
  by_cases hz : c i = 0
  · have he : a = 0 := by linarith
    rw [he]
    exact erase_mem net hC1 c hc i
  have hci : 0 < c i := lt_of_le_of_ne (ha.trans hac) (Ne.symm hz)
  have ht0 : 0 ≤ a / c i := div_nonneg ha hci.le
  have ht1 : a / c i ≤ 1 := (div_le_one hci).mpr hac
  have hc' := (convex_convexHull ℝ (actVec '' net.S)) (erase_mem net hC1 c hc i) hc
    (sub_nonneg.mpr ht1) ht0 (by ring : (1 - a / c i) + a / c i = 1)
  have he : (1 - a / c i) • Function.update c i 0 + (a / c i) • c =
      Function.update c i a := by
    ext k
    by_cases hk : k = i
    · subst k; simp [div_mul_cancel₀ a hz]
    · simp [hk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  rw [he] at hc'
  exact hc'

theorem solution {L N : ℕ} (net : Network L N) (hC1 : C1 net) :
    ∀ c ∈ coS net, ∀ a : Fin N → ℝ, 0 ≤ a → a ≤ c → a ∈ coS net := by
  classical
  intro c hc a ha hac
  have hupdate : ∀ s : Finset (Fin N),
      (fun i => if i ∈ s then a i else c i) ∈ coS net := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hc
    | @insert i s hi ih =>
      have hci : (if i ∈ s then a i else c i) = c i := if_neg hi
      have hm := update_mem net hC1 _ ih i (a i) (ha i) (by rw [hci]; exact hac i)
      convert hm using 1
      ext k
      by_cases hk : k = i
      · subst k; simp
      · simp [hk]
  simpa using hupdate Finset.univ

#print axioms solution


