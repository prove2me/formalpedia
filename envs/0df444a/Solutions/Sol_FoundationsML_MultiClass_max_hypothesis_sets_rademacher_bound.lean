-- Prove2me | solution 1 for FoundationsML.MultiClass.max_hypothesis_sets_rademacher_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T18:24:20.466233+00:00
-- url     : https://prove2.me/submissions/084a8c4e-3edf-47a6-961c-b58af8317602

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_EmpiricalRademacherComplexity
import Definitions.Def_FoundationsML_MultiClass_MaxFamily

section Helpersf69c

theorem cone_sup_le_f69c {α : Type} (G : Set α) (T : α → ℝ) (smul : ℝ → α → α)
    (hG : ∀ c : ℝ, 0 ≤ c → ∀ g ∈ G, smul c g ∈ G) (hT : ∀ c g, T (smul c g) = c * T g) :
    ⨆ g ∈ G, T g ≤ 0 := by
  by_cases hb : BddAbove (Set.range fun g => ⨆ (_ : g ∈ G), T g)
  · obtain ⟨B, hB⟩ := hb
    refine Real.iSup_le (fun g => ?_) le_rfl
    by_cases hg : g ∈ G
    · rw [ciSup_pos hg]
      by_contra hpos
      push Not at hpos
      have hc : 0 ≤ (|B| + 1) / T g := div_nonneg (by positivity) hpos.le
      have hmem := hG _ hc g hg
      have h1 := hB ⟨smul ((|B| + 1) / T g) g, rfl⟩
      simp only at h1
      rw [ciSup_pos hmem, hT, div_mul_cancel₀ _ hpos.ne'] at h1
      linarith [le_abs_self B]
    · simp [hg]
  · rw [Real.iSup_of_not_bddAbove hb]

theorem single_sup_le_f69c {α : Type} (w : α) (T : α → ℝ) :
    ⨆ g ∈ ({w} : Set α), T g ≤ max (T w) 0 := by
  refine Real.iSup_le (fun g => ?_) (le_max_right _ _)
  by_cases hg : g ∈ ({w} : Set α)
  · rw [ciSup_pos hg]
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact le_max_left _ _
  · simp [hg]

theorem lower_sup_f69c {α : Type} (G : Set α) (T : α → ℝ) (B : ℝ)
    (hB : ∀ g ∈ G, T g ≤ B) (g : α) (hg : g ∈ G) :
    T g ≤ ⨆ g ∈ G, T g := by
  have hbdd : BddAbove (Set.range fun g => ⨆ (_ : g ∈ G), T g) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨g', rfl⟩
    refine Real.iSup_le (fun hg' => ?_) (le_max_right _ _)
    exact (hB g' hg').trans (le_max_left _ _)
  refine le_trans ?_ (le_ciSup hbdd g)
  show T g ≤ ⨆ (_ : g ∈ G), T g
  rw [ciSup_pos hg]

theorem zero_le_sup_f69c {α : Type} (G : Set α) (T : α → ℝ) (g : α) (hg : g ∉ G) :
    0 ≤ ⨆ g ∈ G, T g := by
  by_cases hbdd : BddAbove (Set.range fun g => ⨆ (_ : g ∈ G), T g)
  · refine le_trans ?_ (le_ciSup hbdd g)
    show 0 ≤ ⨆ (_ : g ∈ G), T g
    simp [hg]
  · rw [Real.iSup_of_not_bddAbove hbdd]

theorem sup_fin_two_f69c (f : Fin 2 → ℝ) : ⨆ j, f j = max (f 0) (f 1) := by
  apply le_antisymm
  · refine ciSup_le (fun j => ?_)
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_ciSup (Finite.bddAbove_range f) 0) (le_ciSup (Finite.bddAbove_range f) 1)

theorem sum_bool2_f69c (f : (Fin 2 → Bool) → ℝ) :
    ∑ σ : Fin 2 → Bool, f σ = f ![true, true] + f ![true, false] + f ![false, true]
      + f ![false, false] := by
  rw [show (Finset.univ : Finset (Fin 2 → Bool)) =
      {![true, true], ![true, false], ![false, true], ![false, false]} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

end Helpersf69c

open FoundationsML.MultiClass in
theorem solution : ¬ (∀ {X ι : Type} [Fintype ι] [Nonempty ι] (F : ι → Set (X → ℝ)) (m : ℕ)
    (S : Fin m → X),
    EmpiricalRademacherComplexity (MaxFamily F) S ≤
      ∑ j, EmpiricalRademacherComplexity (F j) S) := by
  intro h
  set w : Fin 2 → ℝ := ![-1, 1] with hw
  set F : Fin 2 → Set (Fin 2 → ℝ) := ![{g | ∀ x, g x ≤ 0}, {w}] with hF
  have H := h F 2 id
  set T : (Fin 2 → Bool) → (Fin 2 → ℝ) → ℝ := fun σ g =>
    (1 / ((2 : ℕ) : ℝ)) * ∑ i : Fin 2, (if σ i then (1 : ℝ) else -1) * g (id i) with hT
  -- F 0 contributes nothing
  have h0 : EmpiricalRademacherComplexity (F 0) id ≤ 0 := by
    unfold EmpiricalRademacherComplexity
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun σ _ => ?_)
    refine cone_sup_le_f69c (F 0) (T σ) (fun c g => c • g) ?_ ?_
    · intro c hc g hg
      simp only [hF, Matrix.cons_val_zero, Set.mem_ofPred_eq] at hg ⊢
      intro x
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hc (hg x)
    · intro c g
      simp only [hT, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, id]
      ring
  have h1 : EmpiricalRademacherComplexity (F 1) id ≤ 1 / 4 := by
    unfold EmpiricalRademacherComplexity
    have hF1 : F 1 = {w} := by simp [hF]
    rw [hF1]
    have key : ∀ σ, ⨆ g ∈ ({w} : Set (Fin 2 → ℝ)), T σ g ≤ max (T σ w) 0 :=
      fun σ => single_sup_le_f69c w (T σ)
    calc (1 / (2 : ℝ) ^ 2) * ∑ σ : Fin 2 → Bool, ⨆ g ∈ ({w} : Set (Fin 2 → ℝ)), T σ g
        ≤ (1 / (2 : ℝ) ^ 2) * ∑ σ : Fin 2 → Bool, max (T σ w) 0 := by
          gcongr with σ
          exact key σ
      _ = 1 / 4 := by
          rw [sum_bool2_f69c]
          simp [hT, hw, Fin.sum_univ_two]
          norm_num
  have hM : 3 / 8 ≤ EmpiricalRademacherComplexity (MaxFamily F) id := by
    unfold EmpiricalRademacherComplexity
    have hbound : ∀ σ, ∀ g ∈ MaxFamily F, T σ g ≤ 1 := by
      intro σ g hg
      obtain ⟨hh, hhF, rfl⟩ := hg
      have hh0 : ∀ x, hh 0 x ≤ 0 := by simpa [hF] using hhF 0
      have hh1 : hh 1 = w := by simpa [hF] using hhF 1
      have gx : ∀ x, |⨆ j, hh j x| ≤ 1 := by
        intro x
        rw [sup_fin_two_f69c (fun j => hh j x), hh1]
        rw [abs_le]
        fin_cases x <;> simp [hw] <;> linarith [hh0 0, hh0 1]
      have e : ∀ (b : Bool) (v : ℝ), |v| ≤ 1 → (if b then (1:ℝ) else -1) * v ≤ 1 := by
        intro b v hv
        rw [abs_le] at hv
        cases b <;> simp <;> linarith [hv.1, hv.2]
      have e0 := e (σ 0) _ (gx 0)
      have e1 := e (σ 1) _ (gx 1)
      simp only [hT, Fin.sum_univ_two, id, Nat.cast_ofNat]
      linarith
    have l1 : 1 / 2 ≤ ⨆ g ∈ MaxFamily F, T ![true, true] g := by
      have hm : (fun x => ⨆ j, (![fun _ => (0:ℝ), w] : Fin 2 → Fin 2 → ℝ) j x) ∈ MaxFamily F :=
        ⟨_, fun j => by fin_cases j <;> simp [hF], rfl⟩
      refine le_trans ?_ (lower_sup_f69c _ _ 1 (hbound _) _ hm)
      simp [hT, Fin.sum_univ_two, sup_fin_two_f69c, hw]
    have l2 : 1 ≤ ⨆ g ∈ MaxFamily F, T ![false, true] g := by
      have hm : (fun x => ⨆ j, (![fun _ => (-1:ℝ), w] : Fin 2 → Fin 2 → ℝ) j x) ∈ MaxFamily F :=
        ⟨_, fun j => by fin_cases j <;> simp [hF], rfl⟩
      refine le_trans ?_ (lower_sup_f69c _ _ 1 (hbound _) _ hm)
      simp [hT, Fin.sum_univ_two, sup_fin_two_f69c, hw]
      norm_num
    have hn : (fun _ => (5:ℝ)) ∉ MaxFamily F := by
      rintro ⟨hh, hhF, heq⟩
      have hh0 : ∀ x, hh 0 x ≤ 0 := by simpa [hF] using hhF 0
      have hh1 : hh 1 = w := by simpa [hF] using hhF 1
      have := congrFun heq 0
      rw [sup_fin_two_f69c (fun j => hh j 0), hh1] at this
      have hle : max (hh 0 0) (w 0) ≤ 0 := max_le (hh0 0) (by simp [hw])
      linarith
    have l3 : 0 ≤ ⨆ g ∈ MaxFamily F, T ![true, false] g :=
      zero_le_sup_f69c _ _ _ hn
    have l4 : 0 ≤ ⨆ g ∈ MaxFamily F, T ![false, false] g :=
      zero_le_sup_f69c _ _ _ hn
    change 3 / 8 ≤ (1 / (2:ℝ) ^ 2) * ∑ σ : Fin 2 → Bool, ⨆ g ∈ MaxFamily F, T σ g
    rw [sum_bool2_f69c (fun σ => ⨆ g ∈ MaxFamily F, T σ g)]
    linarith
  have := H
  rw [Fin.sum_univ_two] at this
  linarith
