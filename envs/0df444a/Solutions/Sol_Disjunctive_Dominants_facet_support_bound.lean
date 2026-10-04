-- Prove2me | solution 1 for Disjunctive.Dominants.facet_support_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:16:00.887248+00:00
-- url     : https://prove2.me/submissions/882c8199-16d8-4dd6-bf97-1ba64e5729db

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

open Disjunctive.Dominants

theorem solution : ¬ (∀ {n : ℕ} (P : Set (Fin n → ℝ)) (pi : Fin n → ℝ) (beta : ℝ)
    (hfacet : IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = beta})),
    ((Finset.univ.filter (fun j => pi j ≠ 0)).card : ℤ) ≤ PolyDim P + 1) := by
  classical
  intro h
  set p1 : Fin 4 → ℝ := ![1, 0, -1, 0] with hp1
  set p2 : Fin 4 → ℝ := ![0, 1, 0, -1] with hp2
  set P : Set (Fin 4 → ℝ) := {p1, p2, -p1, -p2} with hP
  set e : Fin 4 → Fin 4 → ℝ := fun i => Pi.single i 1 with he
  -- description of the dominant
  have hdom : ∀ y, y ∈ Dominant P ↔ 0 ≤ y ∧ ∃ j, 1 ≤ y j := by
    intro y
    constructor
    · rintro ⟨hy0, x, hx, hxy⟩
      refine ⟨hy0, ?_⟩
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨0, by simpa [hp1] using hxy 0⟩
      · exact ⟨1, by simpa [hp2] using hxy 1⟩
      · exact ⟨2, by simpa [hp1] using hxy 2⟩
      · exact ⟨3, by simpa [hp2] using hxy 3⟩
    · rintro ⟨hy0, j, hj⟩
      refine ⟨hy0, ?_⟩
      have h0 := fun i => hy0 i
      simp only [Pi.zero_apply] at h0
      fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hj
      · refine ⟨p1, by simp [hP], fun i => ?_⟩
        fin_cases i <;> simp [hp1] <;> linarith [h0 0, h0 1, h0 2, h0 3]
      · refine ⟨p2, by simp [hP], fun i => ?_⟩
        fin_cases i <;> simp [hp2] <;> linarith [h0 0, h0 1, h0 2, h0 3]
      · refine ⟨-p1, by simp [hP], fun i => ?_⟩
        fin_cases i <;> simp [hp1] <;> linarith [h0 0, h0 1, h0 2, h0 3]
      · refine ⟨-p2, by simp [hP], fun i => ?_⟩
        fin_cases i <;> simp [hp2] <;> linarith [h0 0, h0 1, h0 2, h0 3]
  have hsum : ∀ y : Fin 4 → ℝ, dotProduct (fun _ => (1 : ℝ)) y = y 0 + y 1 + y 2 + y 3 := by
    intro y; simp [dotProduct, Fin.sum_univ_four]
  have hge : ∀ y, y ∈ Dominant P → 1 ≤ dotProduct (fun _ => (1 : ℝ)) y := by
    intro y hy
    obtain ⟨hy0, j, hj⟩ := (hdom y).mp hy
    have h0 := fun i => hy0 i
    simp only [Pi.zero_apply] at h0
    rw [hsum]
    fin_cases j <;> simp at hj <;> linarith [h0 0, h0 1, h0 2, h0 3]
  set F : Set (Fin 4 → ℝ) := {x ∈ Dominant P | dotProduct (fun _ => (1 : ℝ)) x = 1} with hF
  have hFe : F = Set.range e := by
    ext y
    constructor
    · rintro ⟨hy, hy1⟩
      obtain ⟨hy0, j, hj⟩ := (hdom y).mp hy
      have h0 := fun i => hy0 i
      simp only [Pi.zero_apply] at h0
      rw [hsum] at hy1
      refine ⟨j, ?_⟩
      funext i
      fin_cases j <;> fin_cases i <;> simp [he] at hj ⊢ <;>
        linarith [h0 0, h0 1, h0 2, h0 3]
    · rintro ⟨j, rfl⟩
      refine ⟨(hdom _).mpr ⟨fun i => ?_, j, by simp [he]⟩, ?_⟩
      · by_cases hij : i = j
        · subst hij; simp [he]
        · simp [he, Pi.single_apply, hij]
      · rw [hsum]
        fin_cases j <;> simp [he]
  -- dimensions
  have hFdim : PolyDim F = 3 := by
    have hne : F.Nonempty := by rw [hFe]; exact ⟨e 0, 0, rfl⟩
    rw [PolyDim, if_pos hne, hFe]
    have hli : LinearIndependent ℝ e := by
      have := (Pi.basisFun ℝ (Fin 4)).linearIndependent
      convert this using 1
      funext i
      simp [he]
    have := (hli.affineIndependent ℝ).finrank_vectorSpan (n := 3) (by simp)
    exact_mod_cast this
  have hQdim : PolyDim (Dominant P) = 4 := by
    have hone : (fun _ => (1 : ℝ)) ∈ Dominant P :=
      (hdom _).mpr ⟨fun _ => zero_le_one, 0, le_rfl⟩
    rw [PolyDim, if_pos ⟨_, hone⟩]
    have htop : vectorSpan ℝ (Dominant P) = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin 4)).span_eq, vectorSpan_def]
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      refine ⟨(fun _ => (1 : ℝ)) + e i, ?_, fun _ => 1, hone, ?_⟩
      · refine (hdom _).mpr ⟨fun k => ?_, 0, ?_⟩
        · by_cases hki : k = i
          · subst hki; simp [he]
          · simp [he, Pi.single_apply, hki]
        · by_cases h0i : (0 : Fin 4) = i
          · subst h0i; simp [he]
          · simp [he, Pi.single_apply, h0i]
      · simp [he]
    rw [htop, finrank_top, Module.finrank_fin_fun]
    rfl
  have hPdim : PolyDim P ≤ 2 := by
    have hne : P.Nonempty := ⟨p1, by simp [hP]⟩
    rw [PolyDim, if_pos hne]
    have hle : vectorSpan ℝ P ≤ Submodule.span ℝ (Set.range ![p1, p2]) := by
      rw [vectorSpan_def, Submodule.span_le]
      have hmem : ∀ x ∈ P, x ∈ Submodule.span ℝ (Set.range ![p1, p2]) := by
        have h1 : p1 ∈ Submodule.span ℝ (Set.range ![p1, p2]) :=
          Submodule.subset_span ⟨0, by simp⟩
        have h2 : p2 ∈ Submodule.span ℝ (Set.range ![p1, p2]) :=
          Submodule.subset_span ⟨1, by simp⟩
        rintro x (rfl | rfl | rfl | rfl)
        · exact h1
        · exact h2
        · exact Submodule.neg_mem _ h1
        · exact Submodule.neg_mem _ h2
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact Submodule.sub_mem _ (hmem x hx) (hmem y hy)
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_range_le_card (R := ℝ) ![p1, p2]
    simp only [Fintype.card_fin] at h2
    have : Module.finrank ℝ (vectorSpan ℝ P) ≤ 2 := le_trans h1 h2
    exact_mod_cast this
  have hfacet : IsFacet (Dominant P) F := by
    refine ⟨⟨fun x hx => hx.1, ?_⟩, ?_, ?_⟩
    · rintro x1 hx1 x2 hx2 x ⟨hx, hx1'⟩ ⟨a, b, ha, hb, hab, rfl⟩
      have g1 := hge x1 hx1
      have g2 := hge x2 hx2
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hx1'
      have e1 : dotProduct (fun _ => (1 : ℝ)) x1 = 1 := by nlinarith
      exact ⟨hx1, e1⟩
    · rw [hFe]; exact ⟨e 0, 0, rfl⟩
    · rw [hFdim, hQdim]; norm_num
  have := h P (fun _ => 1) 1 hfacet
  simp at this
  linarith

#print axioms solution
