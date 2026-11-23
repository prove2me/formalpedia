-- Prove2me | solution 1 for FasterWCTFPTAS.Main.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:34:22.853831+00:00
-- url     : https://prove2.me/submissions/c099dbb6-bb9c-4807-8d63-83caaaa0a3cf

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_DP
import Theorems.Thm_FasterWCTFPTAS_Main_observation_4_5

set_option autoImplicit false

open FasterWCTFPTAS.Main
open Finset

namespace Lemma46Aux

def remJobs (n i : ℕ) : Finset (Fin n) :=
  univ.filter (fun j : Fin n => i ≤ j.val)

lemma disj_first_rem (n i : ℕ) : Disjoint (firstJobs n i) (remJobs n i) := by
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  have h1 := (mem_filter.mp hj1).2
  have h2 := (mem_filter.mp hj2).2
  omega

lemma union_first_rem (n i : ℕ) : firstJobs n i ∪ remJobs n i = univ := by
  ext j
  simp only [mem_union, firstJobs, remJobs, mem_filter, mem_univ, true_and, iff_true]
  omega

lemma load_last_eq {m' n : ℕ} (p : Fin n → ℝ) (i : ℕ) (τ : Fin n → Fin (m' + 1)) :
    ∑ l ∈ (firstJobs n i).filter (fun l => τ l = Fin.last m'), p l =
      T p i - ∑ c : Fin m', piVec (m' + 1) p i τ c := by
  have hpart :
      T p i = ∑ l : Fin (m' + 1), ∑ j ∈ (firstJobs n i).filter (fun j => τ j = l), p j := by
    unfold T firstJobs
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) p
  rw [Fin.sum_univ_castSucc] at hpart
  have hcoord : ∀ c : Fin m',
      ∑ j ∈ (firstJobs n i).filter (fun j => τ j = Fin.castSucc c), p j =
        piVec (m' + 1) p i τ c := fun _ => rfl
  simp_rw [hcoord] at hpart
  linarith

noncomputable def wRem {m n : ℕ} (w : Fin n → ℝ) (i : ℕ) (σ' : Fin n → Fin m) (l : Fin m) : ℝ :=
  ∑ j ∈ (remJobs n i).filter (fun j => σ' j = l), w j

lemma wRem_diff_abs_le {m' n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (i : ℕ)
    (σ' : Fin n → Fin (m' + 1)) (c : Fin m') :
    |wRem w i σ' (Fin.castSucc c) - wRem w i σ' (Fin.last m')| ≤ Wgt w i := by
  have ha_nonneg : 0 ≤ wRem w i σ' (Fin.castSucc c) :=
    Finset.sum_nonneg fun j _ => hw j
  have hb_nonneg : 0 ≤ wRem w i σ' (Fin.last m') :=
    Finset.sum_nonneg fun j _ => hw j
  have hdisj : Disjoint
      ((remJobs n i).filter (fun j => σ' j = Fin.castSucc c))
      ((remJobs n i).filter (fun j => σ' j = Fin.last m')) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := (mem_filter.mp hj1).2
    have h2 := (mem_filter.mp hj2).2
    have hne : Fin.castSucc c ≠ Fin.last m' := Fin.castSucc_ne_last c
    exact hne (h1.symm.trans h2)
  have hsub :
      ((remJobs n i).filter (fun j => σ' j = Fin.castSucc c)) ∪
        ((remJobs n i).filter (fun j => σ' j = Fin.last m')) ⊆ remJobs n i :=
    Finset.union_subset (filter_subset _ _) (filter_subset _ _)
  have hsum_le :
      wRem w i σ' (Fin.castSucc c) + wRem w i σ' (Fin.last m') ≤ Wgt w i := by
    unfold wRem
    rw [← Finset.sum_union hdisj]
    change _ ≤ ∑ j ∈ remJobs n i, w j
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hw j
  rw [abs_le]
  constructor <;> linarith

lemma cost_combine_decomp {m' n : ℕ} (p w : Fin n → ℝ) (i : ℕ)
    (τ σ' : Fin n → Fin (m' + 1)) :
    costIdxOn p w univ (combine i τ σ') =
      dotm (piVec (m' + 1) p i τ) (fun c => wRem w i σ' (Fin.castSucc c) - wRem w i σ' (Fin.last m')) +
      theta (m' + 1) p w i τ +
      costIdxOn p w (remJobs n i) σ' +
      T p i * wRem w i σ' (Fin.last m') := by
  have hsplit_univ :
      costIdxOn p w univ (combine i τ σ') =
        (∑ j ∈ firstJobs n i,
          w j * ∑ l ∈ univ.filter (fun l => combine i τ σ' l = combine i τ σ' j ∧ l ≤ j), p l) +
        (∑ j ∈ remJobs n i,
          w j * ∑ l ∈ univ.filter (fun l => combine i τ σ' l = combine i τ σ' j ∧ l ≤ j), p l) := by
    unfold costIdxOn
    rw [← Finset.sum_union (disj_first_rem n i), union_first_rem]
  have hfirst :
      ∑ j ∈ firstJobs n i,
          w j * ∑ l ∈ univ.filter (fun l => combine i τ σ' l = combine i τ σ' j ∧ l ≤ j), p l =
        theta (m' + 1) p w i τ := by
    unfold theta costIdxOn
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    have hj_lt : j.val < i := (mem_filter.mp hj).2
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [mem_univ, true_and]
    constructor
    · rintro ⟨hs, hle⟩
      have hl_lt : l.val < i := Nat.lt_of_le_of_lt hle hj_lt
      have hl_mem : l ∈ firstJobs n i := mem_filter.mpr ⟨mem_univ l, hl_lt⟩
      have hs' : τ l = τ j := by
        simpa [combine, hj_lt, hl_lt] using hs
      exact ⟨hl_mem, hs', hle⟩
    · rintro ⟨hl_mem, hs, hle⟩
      have hl_lt : l.val < i := (mem_filter.mp hl_mem).2
      have hs' : combine i τ σ' l = combine i τ σ' j := by
        simp [combine, hj_lt, hl_lt, hs]
      exact ⟨hs', hle⟩
  have hrem_each : ∀ j ∈ remJobs n i,
      ∑ l ∈ univ.filter (fun l => combine i τ σ' l = combine i τ σ' j ∧ l ≤ j), p l =
        (∑ l ∈ (firstJobs n i).filter (fun l => τ l = σ' j), p l) +
        (∑ l ∈ (remJobs n i).filter (fun l => σ' l = σ' j ∧ l ≤ j), p l) := by
    intro j hj
    have hj_ge : i ≤ j.val := (mem_filter.mp hj).2
    have hj_not_lt : ¬ j.val < i := by omega
    have hsplit :
        univ.filter (fun l => combine i τ σ' l = combine i τ σ' j ∧ l ≤ j) =
          ((firstJobs n i).filter (fun l => τ l = σ' j)) ∪
          ((remJobs n i).filter (fun l => σ' l = σ' j ∧ l ≤ j)) := by
      ext l
      rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      simp only [mem_univ, true_and]
      by_cases hl_lt : l.val < i
      · have hl_mem1 : l ∈ firstJobs n i := mem_filter.mpr ⟨mem_univ l, hl_lt⟩
        have hl_not_mem2 : l ∉ remJobs n i := by
          simp [remJobs]; omega
        have hle : l ≤ j := le_of_lt (Nat.lt_of_lt_of_le hl_lt hj_ge)
        simp [combine, hj_not_lt, hl_lt, hl_mem1, hl_not_mem2, hle]
      · have hl_not_mem1 : l ∉ firstJobs n i := by
          simp [firstJobs, hl_lt]
        have hl_mem2 : l ∈ remJobs n i := by
          simp [remJobs]; omega
        simp [combine, hj_not_lt, hl_lt, hl_not_mem1, hl_mem2]
    have hdisj' : Disjoint
        ((firstJobs n i).filter (fun l => τ l = σ' j))
        ((remJobs n i).filter (fun l => σ' l = σ' j ∧ l ≤ j)) :=
      Disjoint.mono (filter_subset _ _) (filter_subset _ _) (disj_first_rem n i)
    rw [hsplit, Finset.sum_union hdisj']
  have hrem :
      ∑ j ∈ remJobs n i,
          w j * ∑ l ∈ univ.filter (fun l => combine i τ σ' l = combine i τ σ' j ∧ l ≤ j), p l =
        (∑ j ∈ remJobs n i, w j * ∑ l ∈ (firstJobs n i).filter (fun l => τ l = σ' j), p l) +
        costIdxOn p w (remJobs n i) σ' := by
    unfold costIdxOn
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hrem_each j hj, mul_add]
  let load : Fin (m' + 1) → ℝ := fun m0 => ∑ l ∈ (firstJobs n i).filter (fun l => τ l = m0), p l
  have hcross :
      ∑ j ∈ remJobs n i, w j * load (σ' j) =
        ∑ m0 : Fin (m' + 1), wRem w i σ' m0 * load m0 := by
    have hfib := Finset.sum_fiberwise_of_maps_to (s := remJobs n i) (t := univ)
      (g := σ') (fun _ _ => mem_univ _) (fun j => w j * load (σ' j))
    rw [← hfib]
    refine Finset.sum_congr rfl fun m0 _ => ?_
    unfold wRem
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [(mem_filter.mp hj).2]
  have hcross2 :
      ∑ m0 : Fin (m' + 1), wRem w i σ' m0 * load m0 =
        dotm (piVec (m' + 1) p i τ)
          (fun c => wRem w i σ' (Fin.castSucc c) - wRem w i σ' (Fin.last m')) +
        T p i * wRem w i σ' (Fin.last m') := by
    rw [Fin.sum_univ_castSucc]
    have hc_load : ∀ c : Fin m', load (Fin.castSucc c) = piVec (m' + 1) p i τ c := fun _ => rfl
    have hlast_load : load (Fin.last m') = T p i - ∑ c : Fin m', piVec (m' + 1) p i τ c :=
      load_last_eq p i τ
    simp_rw [hc_load, hlast_load]
    unfold dotm
    change (∑ c : Fin m', wRem w i σ' c.castSucc * piVec (m' + 1) p i τ c) +
        wRem w i σ' (Fin.last m') * (T p i - ∑ c : Fin m', piVec (m' + 1) p i τ c) =
      (∑ c : Fin m', piVec (m' + 1) p i τ c *
        (wRem w i σ' c.castSucc - wRem w i σ' (Fin.last m'))) +
      T p i * wRem w i σ' (Fin.last m')
    have hsub_sum :
        ∑ c : Fin m', piVec (m' + 1) p i τ c *
            (wRem w i σ' c.castSucc - wRem w i σ' (Fin.last m')) =
          (∑ c : Fin m', wRem w i σ' c.castSucc * piVec (m' + 1) p i τ c) -
          wRem w i σ' (Fin.last m') * ∑ c : Fin m', piVec (m' + 1) p i τ c := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hsub_sum]
    ring
  rw [hsplit_univ, hfirst, hrem]
  change theta (m' + 1) p w i τ +
      ((∑ j ∈ remJobs n i, w j * load (σ' j)) + costIdxOn p w (remJobs n i) σ') = _
  rw [hcross, hcross2]
  ring

lemma T_mono {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) {a b : ℕ} (hab : a ≤ b) :
    T p a ≤ T p b := by
  unfold T
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => le_of_lt (hp j)
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  omega

lemma Ti_Wgt_add_Ui_le_Un {n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (i : ℕ) :
    T p i * Wgt w i + U p w i ≤ U p w n := by
  have huniv : U p w n = ∑ j : Fin n, w j * T p (j.val + 1) := by
    unfold U
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp
  rw [huniv, ← union_first_rem n i, Finset.sum_union (disj_first_rem n i)]
  have _hUi : U p w i = ∑ j ∈ firstJobs n i, w j * T p (j.val + 1) := rfl
  have hWgt : T p i * Wgt w i ≤ ∑ j ∈ remJobs n i, w j * T p (j.val + 1) := by
    unfold Wgt remJobs
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj_ge : i ≤ j.val := (mem_filter.mp hj).2
    have hT : T p i ≤ T p (j.val + 1) := T_mono p hp (by omega)
    have hmul := mul_le_mul_of_nonneg_left hT (hw j)
    linarith
  linarith

end Lemma46Aux

theorem solution {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) (i : ℕ) (_hi1 : 1 ≤ i) (_hin : i ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (_hδ1 : δ < 1)
    (D Dt : Set (Pt m)) (hD : D ⊆ DP m p w i)
    (hrel : IsRelaxedRep (δ / m) (T p i) (U p w i) (Wgt w i) Dt D) :
    IsRepSet m p w i δ Dt D := by
  have hobs45 : U p w n / (m : ℝ) ≤ OPT m p w :=
    FasterWCTFPTAS.Main.observation_4_5 hm p w hp hw hsort
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨hrel.1, fun σ' σ hσD => ?_⟩
  let x : Fin m' → ℝ :=
    fun c => Lemma46Aux.wRem w i σ' (Fin.castSucc c) - Lemma46Aux.wRem w i σ' (Fin.last m')
  have hx : ∀ c : Fin m', |x c| ≤ Wgt w i :=
    fun c => Lemma46Aux.wRem_diff_abs_le w hw i σ' c
  obtain ⟨e, heDt, he_le⟩ := hrel.2 x hx (pairOf (m' + 1) p w i σ) hσD
  have heDP : e ∈ DP (m' + 1) p w i := hD (hrel.1 heDt)
  obtain ⟨σt, rfl⟩ := heDP
  refine ⟨σt, heDt, ?_⟩
  have hTU : T p i * Wgt w i + U p w i ≤ U p w n := Lemma46Aux.Ti_Wgt_add_Ui_le_Un p w hp hw i
  have hU_opt : U p w n ≤ ((m' + 1 : ℕ) : ℝ) * OPT (m' + 1) p w := by
    have h := (div_le_iff₀ hm_pos).mp hobs45
    linarith
  have herr :
      (δ / ((m' + 1 : ℕ) : ℝ)) * (T p i * Wgt w i + U p w i) ≤ δ * OPT (m' + 1) p w := by
    have h1 : T p i * Wgt w i + U p w i ≤ ((m' + 1 : ℕ) : ℝ) * OPT (m' + 1) p w :=
      le_trans hTU hU_opt
    have hdiv_pos : 0 ≤ δ / ((m' + 1 : ℕ) : ℝ) := div_nonneg (le_of_lt hδ0) (le_of_lt hm_pos)
    calc
      (δ / ((m' + 1 : ℕ) : ℝ)) * (T p i * Wgt w i + U p w i)
          ≤ (δ / ((m' + 1 : ℕ) : ℝ)) * (((m' + 1 : ℕ) : ℝ) * OPT (m' + 1) p w) :=
            mul_le_mul_of_nonneg_left h1 hdiv_pos
      _ = δ * OPT (m' + 1) p w := by
            field_simp [ne_of_gt hm_pos]
  have he_le' :
      dotm (piVec (m' + 1) p i σt) x + theta (m' + 1) p w i σt ≤
        dotm (piVec (m' + 1) p i σ) x + theta (m' + 1) p w i σ +
          (δ / ((m' + 1 : ℕ) : ℝ)) * (T p i * Wgt w i + U p w i) := he_le
  have h1 := Lemma46Aux.cost_combine_decomp p w i σt σ'
  have h2 := Lemma46Aux.cost_combine_decomp p w i σ σ'
  change costIdxOn p w univ (combine i σt σ') =
      dotm (piVec (m' + 1) p i σt) x + theta (m' + 1) p w i σt +
        costIdxOn p w (Lemma46Aux.remJobs n i) σ' +
        T p i * Lemma46Aux.wRem w i σ' (Fin.last m') at h1
  change costIdxOn p w univ (combine i σ σ') =
      dotm (piVec (m' + 1) p i σ) x + theta (m' + 1) p w i σ +
        costIdxOn p w (Lemma46Aux.remJobs n i) σ' +
        T p i * Lemma46Aux.wRem w i σ' (Fin.last m') at h2
  linarith
