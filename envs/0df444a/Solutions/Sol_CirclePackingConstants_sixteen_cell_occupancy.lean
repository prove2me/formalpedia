-- Prove2me | solution 1 for CirclePackingConstants.sixteen_cell_occupancy
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-06T15:06:51.459985+00:00
-- url     : https://prove2.me/submissions/63e220e1-c06d-40fd-a940-4465cf714be2

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_SixteenOcc
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch1
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch2
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch3
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch4
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch5
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch6
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch7
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch8
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch9
import Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch10
import Theorems.Thm_CirclePackingConstants_sixteen_cover_group1
import Theorems.Thm_CirclePackingConstants_sixteen_cover_group2
import Theorems.Thm_CirclePackingConstants_sixteen_cover_group3
import Theorems.Thm_CirclePackingConstants_sixteen_cover_group4
import Theorems.Thm_CirclePackingConstants_sixteen_cover_group5
import Theorems.Thm_CirclePackingConstants_sixteen_cover_group6
import Theorems.Thm_CirclePackingConstants_sixteen_cover_group7
import Theorems.Thm_CirclePackingConstants_sixteen_cover_group8

open CirclePackingConstants CirclePackingConstants.Sixteen

namespace OccAsm

noncomputable def cxf (x : ℝ) : ℕ := min 3 ⌊4 * x⌋₊

theorem cxf_spec (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (cxf x : ℝ) / 4 ≤ x ∧ x ≤ ((cxf x : ℝ) + 1) / 4 ∧ cxf x ≤ 3 := by
  unfold cxf
  have hm1 : (⌊4 * x⌋₊ : ℝ) ≤ 4 * x := Nat.floor_le (by linarith)
  have hm2 : 4 * x < (⌊4 * x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  by_cases hm : ⌊4 * x⌋₊ ≤ 3
  · rw [min_eq_right hm]
    refine ⟨by linarith, by linarith, hm⟩
  · have hm' : 3 < ⌊4 * x⌋₊ := by omega
    rw [min_eq_left hm'.le]
    have hge : (4 : ℝ) ≤ ⌊4 * x⌋₊ := by exact_mod_cast hm'
    refine ⟨by push_cast; linarith, by push_cast; linarith, le_refl _⟩


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem lib_len : sixteenLib.length = 590 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem lib_589 : sixteenLib[589]? = some [(0, 0, 3)] := by decide +kernel

/-- cell label of a point -/
noncomputable def clf (p : Fin 16 → Point) (k : Fin 16) : ℕ × ℕ := (cxf (p k).1, cxf (p k).2)

def ci (cl : Fin 16 → ℕ × ℕ) (k : Fin 16) : ℕ := 4 * (cl k).1 + (cl k).2

def cnt (cl : Fin 16 → ℕ × ℕ) (c : ℕ) : ℕ :=
  if c < 16 then (Finset.univ.filter (fun k : Fin 16 => ci cl k = c)).card else 0

theorem cnt_eq (cl : Fin 16 → ℕ × ℕ) (hle : ∀ k, (cl k).1 ≤ 3 ∧ (cl k).2 ≤ 3) (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) :
    (Finset.univ.filter (fun k : Fin 16 => cl k = (a, b))).card = cnt cl (4 * a + b) := by
  unfold cnt
  rw [if_pos (by omega)]
  congr 1
  apply Finset.filter_congr
  intro k _
  have := hle k
  unfold ci
  constructor
  · intro h; rw [h]
  · intro h
    have h1 : (cl k).1 = a := by omega
    have h2 : (cl k).2 = b := by omega
    exact Prod.ext h1 h2

theorem cnt_sum (cl : Fin 16 → ℕ × ℕ) (hle : ∀ k, (cl k).1 ≤ 3 ∧ (cl k).2 ≤ 3) :
    ∑ c ∈ Finset.range 16, cnt cl c = 16 := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin 16))) (t := Finset.range 16)
    (f := ci cl) (fun k _ => by
      have := hle k; unfold ci; exact Finset.mem_range.2 (by omega))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  refine Eq.trans ?_ h.symm
  apply Finset.sum_congr rfl
  intro c hc
  unfold cnt
  rw [if_pos (Finset.mem_range.1 hc)]


theorem inGrid_facts {z : ℤ × ℤ} (h : inGrid z = true) : 0 ≤ z.1 ∧ z.1 ≤ 3 ∧ 0 ≤ z.2 ∧ z.2 ≤ 3 := by
  unfold inGrid at h
  simpa using h

theorem cell_card (cl : Fin 16 → ℕ × ℕ) (hle : ∀ k, (cl k).1 ≤ 3 ∧ (cl k).2 ≤ 3) (z : ℤ × ℤ)
    (hz : inGrid z = true) :
    cnt cl (cellIdx z) = (Finset.univ.filter (fun k : Fin 16 => cl k = (z.1.toNat, z.2.toNat))).card := by
  obtain ⟨h1, h2, h3, h4⟩ := inGrid_facts hz
  have e : cellIdx z = 4 * z.1.toNat + z.2.toNat := by
    unfold cellIdx; omega
  rw [e, cnt_eq cl hle z.1.toNat z.2.toNat (by omega) (by omega)]

theorem noninj (p : Fin 16 → Point) (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1)
    (hd : ∀ i j, i ≠ j → (1 : ℝ) / 9 < sqDist (p i) (p j)) (hni : ¬ Function.Injective (clf p)) : False := by
  classical
  have hspec : ∀ k, (clf p k).1 ≤ 3 ∧ (clf p k).2 ≤ 3 ∧
      ((clf p k).1 : ℝ) / 4 ≤ (p k).1 ∧ (p k).1 ≤ (((clf p k).1 : ℝ) + 1) / 4 ∧
      ((clf p k).2 : ℝ) / 4 ≤ (p k).2 ∧ (p k).2 ≤ (((clf p k).2 : ℝ) + 1) / 4 := by
    intro k
    obtain ⟨a1, a2, a3, a4⟩ := hp k
    obtain ⟨b1, b2, b3⟩ := cxf_spec (p k).1 a1 a2
    obtain ⟨c1, c2, c3⟩ := cxf_spec (p k).2 a3 a4
    exact ⟨b3, c3, b1, b2, c1, c2⟩
  have hle : ∀ k, (clf p k).1 ≤ 3 ∧ (clf p k).2 ≤ 3 := fun k => ⟨(hspec k).1, (hspec k).2.1⟩
  have hcell : ∀ k, ((clf p k).1 : ℝ) / 4 ≤ (p k).1 ∧ (p k).1 ≤ (((clf p k).1 : ℝ) + 1) / 4 ∧
      ((clf p k).2 : ℝ) / 4 ≤ (p k).2 ∧ (p k).2 ≤ (((clf p k).2 : ℝ) + 1) / 4 :=
    fun k => ⟨(hspec k).2.2.1, (hspec k).2.2.2.1, (hspec k).2.2.2.2.1, (hspec k).2.2.2.2.2⟩
  -- a pattern of the library cannot be placed
  have key : ∀ (e : ℕ) (ent : List (ℕ × ℕ × ℕ)) (s tx ty : ℕ), sixteenLib[e]? = some ent →
      (∀ t ∈ ent, inGrid (place s tx ty (t.1, t.2.1)) = true ∧
        t.2.2 ≤ (Finset.univ.filter (fun k : Fin 16 => clf p k = ((place s tx ty (t.1, t.2.1)).1.toNat,
          (place s tx ty (t.1, t.2.1)).2.toNat))).card) → False := by
    intro e ent s tx ty hent hm
    have he : e < 590 := by
      have := (List.getElem?_eq_some_iff.1 hent).1
      rw [lib_len] at this; exact this
    by_cases h0 : e < 134
    · exact sixteen_nogood_batch1 e (by omega) h0 ent hent p (clf p) hcell hd s tx ty hm
    ·
      by_cases h1 : e < 197
      · exact sixteen_nogood_batch2 e (by omega) h1 ent hent p (clf p) hcell hd s tx ty hm
      ·
        by_cases h2 : e < 255
        · exact sixteen_nogood_batch3 e (by omega) h2 ent hent p (clf p) hcell hd s tx ty hm
        ·
          by_cases h3 : e < 367
          · exact sixteen_nogood_batch4 e (by omega) h3 ent hent p (clf p) hcell hd s tx ty hm
          ·
            by_cases h4 : e < 403
            · exact sixteen_nogood_batch5 e (by omega) h4 ent hent p (clf p) hcell hd s tx ty hm
            ·
              by_cases h5 : e < 439
              · exact sixteen_nogood_batch6 e (by omega) h5 ent hent p (clf p) hcell hd s tx ty hm
              ·
                by_cases h6 : e < 470
                · exact sixteen_nogood_batch7 e (by omega) h6 ent hent p (clf p) hcell hd s tx ty hm
                ·
                  by_cases h7 : e < 486
                  · exact sixteen_nogood_batch8 e (by omega) h7 ent hent p (clf p) hcell hd s tx ty hm
                  ·
                    by_cases h8 : e < 540
                    · exact sixteen_nogood_batch9 e (by omega) h8 ent hent p (clf p) hcell hd s tx ty hm
                    ·
                      exact sixteen_nogood_batch10 e (by omega) he ent hent p (clf p) hcell hd s tx ty hm
  have key2 : ∀ (e s tx ty : ℕ), Matches sixteenLib (cnt (clf p)) e s tx ty → False := by
    intro e s tx ty ⟨ent, hent, hall⟩
    refine key e ent s tx ty hent (fun t ht => ?_)
    obtain ⟨hg, hc⟩ := hall t ht
    refine ⟨hg, ?_⟩
    rw [← cell_card (clf p) hle _ hg]
    exact hc
  -- triple occupancy
  by_cases h3 : ∃ c < 16, 3 ≤ cnt (clf p) c
  · obtain ⟨c, hc16, hc3⟩ := h3
    apply key 589 [(0, 0, 3)] 0 (c / 4 + 3) (c % 4 + 3) lib_589
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    have hz : inGrid (place 0 (c / 4 + 3) (c % 4 + 3) (0, 0)) = true := by
      unfold inGrid place; simp; omega
    refine ⟨hz, ?_⟩
    rw [← cell_card (clf p) hle _ hz]
    have e : cellIdx (place 0 (c / 4 + 3) (c % 4 + 3) (0, 0)) = c := by
      unfold cellIdx place; simp; omega
    rw [e]; exact hc3
  · push Not at h3
    have hn2 : ∀ i, cnt (clf p) i ≤ 2 := by
      intro i
      by_cases hi : i < 16
      · have := h3 i hi; omega
      · unfold cnt; rw [if_neg hi]; omega
    have hsum := cnt_sum (clf p) hle
    have hne : ∃ i < 16, cnt (clf p) i ≠ 1 := by
      unfold Function.Injective at hni
      push Not at hni
      obtain ⟨i, j, hij, hne⟩ := hni
      refine ⟨4 * (clf p i).1 + (clf p i).2, by have := hle i; omega, ?_⟩
      have hh := hle i
      have hcnt : cnt (clf p) (4 * (clf p i).1 + (clf p i).2) =
          (Finset.univ.filter (fun k : Fin 16 => clf p k = (clf p i))).card := by
        rw [← cnt_eq (clf p) hle _ _ hh.1 hh.2]
      rw [hcnt]
      have h2 : 2 ≤ (Finset.univ.filter (fun k : Fin 16 => clf p k = (clf p i))).card := by
        have hsub : ({i, j} : Finset (Fin 16)) ⊆ Finset.univ.filter (fun k : Fin 16 => clf p k = (clf p i)) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hx with rfl | rfl
          · rfl
          · exact hij.symm
        have := Finset.card_le_card hsub
        rw [Finset.card_pair hne] at this
        exact this
      omega
    -- covering: case on the counts of cells 0 and 1
    have hcov : ∃ e s tx ty, Matches sixteenLib (cnt (clf p)) e s tx ty := by
      rcases (by have := hn2 0; omega : cnt (clf p) 0 = 0 ∨ cnt (clf p) 0 = 1 ∨ cnt (clf p) 0 = 2) with a | a | a <;>
      rcases (by have := hn2 1; omega : cnt (clf p) 1 = 0 ∨ cnt (clf p) 1 = 1 ∨ cnt (clf p) 1 = 2) with b | b | b
      · exact sixteen_cover_group1 _ hn2 hsum hne (by exact ⟨a, b⟩)
      · exact sixteen_cover_group2 _ hn2 hsum hne (by exact ⟨a, b⟩)
      · exact sixteen_cover_group3 _ hn2 hsum hne (Or.inl ⟨a, b⟩)
      · exact sixteen_cover_group4 _ hn2 hsum hne (by exact ⟨a, b⟩)
      · exact sixteen_cover_group5 _ hn2 hsum hne (by exact ⟨a, b⟩)
      · exact sixteen_cover_group6 _ hn2 hsum hne (by exact ⟨a, b⟩)
      · exact sixteen_cover_group7 _ hn2 hsum hne (by exact ⟨a, b⟩)
      · exact sixteen_cover_group8 _ hn2 hsum hne (by exact ⟨a, b⟩)
      · exact sixteen_cover_group3 _ hn2 hsum hne (Or.inr (⟨a, b⟩))
    obtain ⟨e, s, tx, ty, hM⟩ := hcov
    exact key2 e s tx ty hM

end OccAsm

theorem solution (p : Fin 16 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1)
    (hd : ∀ i j, i ≠ j → (1 : ℝ) / 9 < sqDist (p i) (p j)) :
    ∃ σ : Fin 16 → Fin 4 × Fin 4, Function.Bijective σ ∧ ∀ k,
      ((σ k).1.val : ℝ) / 4 ≤ (p k).1 ∧ (p k).1 ≤ (((σ k).1.val : ℝ) + 1) / 4 ∧
      ((σ k).2.val : ℝ) / 4 ≤ (p k).2 ∧ (p k).2 ≤ (((σ k).2.val : ℝ) + 1) / 4 := by
  classical
  by_cases hinj : Function.Injective (OccAsm.clf p)
  · have hspec : ∀ k, (OccAsm.clf p k).1 ≤ 3 ∧ (OccAsm.clf p k).2 ≤ 3 ∧
        ((OccAsm.clf p k).1 : ℝ) / 4 ≤ (p k).1 ∧ (p k).1 ≤ (((OccAsm.clf p k).1 : ℝ) + 1) / 4 ∧
        ((OccAsm.clf p k).2 : ℝ) / 4 ≤ (p k).2 ∧ (p k).2 ≤ (((OccAsm.clf p k).2 : ℝ) + 1) / 4 := by
      intro k
      obtain ⟨a1, a2, a3, a4⟩ := hp k
      obtain ⟨b1, b2, b3⟩ := OccAsm.cxf_spec (p k).1 a1 a2
      obtain ⟨c1, c2, c3⟩ := OccAsm.cxf_spec (p k).2 a3 a4
      exact ⟨b3, c3, b1, b2, c1, c2⟩
    let σ : Fin 16 → Fin 4 × Fin 4 := fun k =>
      (⟨(OccAsm.clf p k).1, by have := (hspec k).1; omega⟩, ⟨(OccAsm.clf p k).2, by have := (hspec k).2.1; omega⟩)
    have hσ : Function.Injective σ := by
      intro i j h
      apply hinj
      have h1 := congrArg (fun x => x.1.val) h
      have h2 := congrArg (fun x => x.2.val) h
      simp only [σ] at h1 h2
      exact Prod.ext h1 h2
    refine ⟨σ, ?_, ?_⟩
    · rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hσ, by simp⟩
    · intro k
      exact ⟨(hspec k).2.2.1, (hspec k).2.2.2.1, (hspec k).2.2.2.2.1, (hspec k).2.2.2.2.2⟩
  · exact (OccAsm.noninj p hp hd hinj).elim
