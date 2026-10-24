-- Prove2me | solution 1 for Disjunctive.Polymatroids.pi_projection_characterization_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T15:02:26.900478+00:00
-- url     : https://prove2.me/submissions/75b1cf19-5eb6-444f-b6f6-a6dcece9fe1b

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace PM90
open Disjunctive.Polymatroids Finset

def U {n : ℕ} (τ : Fin n → Fin n) (j : Fin n) : Finset (Fin n) := univ.filter (fun i => τ j ≤ τ i)

def greedy {n : ℕ} (r : Finset (Fin n) → ℝ) (τ : Fin n → Fin n) (j : Fin n) : ℝ :=
  r (U τ j) - r ((U τ j).erase j)

lemma mem_U {n : ℕ} (τ : Fin n → Fin n) (i j : Fin n) : i ∈ U τ j ↔ τ j ≤ τ i := by
  simp [U]

lemma greedy_mem {n : ℕ} (r : Finset (Fin n) → ℝ) (hr : IsPolymatroidRankFunction r)
    (τ : Fin n → Fin n) : greedy r τ ∈ PolymatroidP r := by
  obtain ⟨h0, hmono, hsub⟩ := hr
  refine ⟨fun j => ?_, fun A => ?_⟩
  · simp only [Pi.zero_apply, greedy]; linarith [hmono _ _ (erase_subset j (U τ j))]
  · induction A using Finset.strongInduction with
    | H A ih =>
      rcases A.eq_empty_or_nonempty with rfl | hne
      · simp [SumOver, h0]
      · obtain ⟨j, hjA, hjmin⟩ := A.exists_min_image τ hne
        have hAU : A ⊆ U τ j := fun i hi => (mem_U τ i j).2 (hjmin i hi)
        have h1 : A ∪ (U τ j).erase j = U τ j := by
          ext i; simp only [mem_union, mem_erase]; constructor
          · rintro (h | ⟨_, h⟩)
            · exact hAU h
            · exact h
          · intro h
            by_cases hij : i = j
            · left; rw [hij]; exact hjA
            · right; exact ⟨hij, h⟩
        have h2 : A ∩ (U τ j).erase j = A.erase j := by
          ext i; simp only [mem_inter, mem_erase]; constructor
          · rintro ⟨h, hne, _⟩; exact ⟨hne, h⟩
          · rintro ⟨hne, h⟩; exact ⟨h, hne, hAU h⟩
        have hs := hsub A ((U τ j).erase j)
        rw [h1, h2] at hs
        have hih := ih (A.erase j) (erase_ssubset hjA)
        have hsplit : SumOver (greedy r τ) A = greedy r τ j + SumOver (greedy r τ) (A.erase j) := by
          unfold SumOver; rw [add_sum_erase _ _ hjA]
        rw [hsplit]; unfold greedy at *; linarith

lemma greedy_tight {n : ℕ} (r : Finset (Fin n) → ℝ) (h0 : r ∅ = 0)
    (τ : Fin n → Fin n) (hτ : Function.Injective τ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, ∀ i', τ i ≤ τ i' → i' ∈ A) : SumOver (greedy r τ) A = r A := by
  induction A using Finset.strongInduction with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with rfl | hne
    · simp [SumOver, h0]
    · obtain ⟨j, hjA, hjmin⟩ := A.exists_min_image τ hne
      have hAU : A = U τ j := by
        ext i; rw [mem_U]; exact ⟨hjmin i, hA j hjA i⟩
      have hup : ∀ i ∈ A.erase j, ∀ i', τ i ≤ τ i' → i' ∈ A.erase j := by
        intro i hi i' hii'
        rw [mem_erase] at hi ⊢
        refine ⟨fun h => ?_, hA i hi.2 i' hii'⟩
        subst h
        exact hi.1 (hτ (le_antisymm (hjmin i hi.2) hii').symm)
      have hih := ih (A.erase j) (erase_ssubset hjA) hup
      have hsplit : SumOver (greedy r τ) A = greedy r τ j + SumOver (greedy r τ) (A.erase j) := by
        unfold SumOver; rw [add_sum_erase _ _ hjA]
      rw [hsplit, hih]; unfold greedy; rw [← hAU]; ring


lemma chain_sum {n : ℕ} (τ : Fin n → Fin n) (c : Fin n → ℝ) (f : Finset (Fin n) → ℝ) :
    ∑ A, (∑ j, if U τ j = A then c j else 0) * f A = ∑ j, c j * f (U τ j) := by
  simp_rw [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

lemma sup_dir {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) :
    PiProjSystem r1 r2 ⊆ PiSet r1 r2 := by
  rintro π ⟨u, hu, hπ, hcov, h1, h2⟩
  refine ⟨hπ, fun x hx => ?_⟩
  have key : ∀ r : Finset (Fin n) → ℝ, x ∈ PolymatroidP r → (∑ A, u A * r A) ≤ 1 →
      dotProduct π x ≤ 1 := by
    intro r ⟨hx0, hxr⟩ hr
    have e1 : dotProduct π x ≤ ∑ j, (∑ A ∈ univ.filter (fun A => j ∈ A), u A) * x j := by
      unfold dotProduct
      exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcov j) (hx0 j)
    have e2 : ∑ j, (∑ A ∈ univ.filter (fun A => j ∈ A), u A) * x j = ∑ A, u A * SumOver x A := by
      simp_rw [sum_filter, sum_mul, SumOver, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun A _ => ?_
      simp_rw [ite_mul, zero_mul]
      rw [← sum_filter]
      simp
    have e3 : ∑ A, u A * SumOver x A ≤ ∑ A, u A * r A :=
      sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hxr A) (hu A)
    linarith
  rcases hx with hx | hx
  · exact key r1 hx h1
  · exact key r2 hx h2


/-- prefix values: `P 0 = 0`, `P (k+1) = π (σ k)`. -/
def Pv {n : ℕ} (π : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if h : k < n then π (σ ⟨k, h⟩) else 0

lemma telescope {n : ℕ} (π : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (∑ j, if σ.symm j ≤ σ.symm i then Pv π σ ((σ.symm j : ℕ) + 1) - Pv π σ (σ.symm j) else 0)
      = π i := by
  rw [Equiv.sum_comp σ.symm (fun k : Fin n =>
    if k ≤ σ.symm i then Pv π σ ((k : ℕ) + 1) - Pv π σ k else 0)]
  set m := σ.symm i with hm
  simp_rw [← Fin.val_fin_le]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    if k ≤ (m : ℕ) then Pv π σ (k + 1) - Pv π σ k else 0) n] 
  · rw [← sum_filter]
    have : (range n).filter (fun k => k ≤ (m : ℕ)) = range ((m : ℕ) + 1) := by
      ext k; simp only [mem_filter, mem_range]; constructor
      · rintro ⟨_, h⟩; omega
      · intro h; exact ⟨by omega, by omega⟩
    rw [this, sum_range_sub]
    simp [Pv, hm]


lemma sub_dir {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsPolymatroidRankFunction r1) (hr2 : IsPolymatroidRankFunction r2) :
    PiSet r1 r2 ⊆ PiProjSystem r1 r2 := by
  rintro π ⟨hπ, hdot⟩
  set σ := Tuple.sort π with hσ
  have hmono : Monotone (π ∘ σ) := Tuple.monotone_sort π
  set τ : Fin n → Fin n := ⇑σ.symm with hτdef
  have hτ : Function.Injective τ := σ.symm.injective
  set c : Fin n → ℝ := fun j => Pv π σ ((τ j : ℕ) + 1) - Pv π σ (τ j) with hc
  have hc0 : ∀ j, 0 ≤ c j := by
    intro j
    simp only [hc]
    obtain ⟨k, hk⟩ := τ j
    cases k with
    | zero => simp [Pv, hk]; exact hπ _
    | succ k =>
      have h1 : k < n := by omega
      simp only [Pv, hk, h1, dif_pos]
      have := hmono (show (⟨k, h1⟩ : Fin n) ≤ ⟨k + 1, hk⟩ from by simp [Fin.le_def])
      simp only [Function.comp] at this
      linarith
  have htel : ∀ i, (∑ j, if τ j ≤ τ i then c j else 0) = π i := fun i => telescope π σ i
  set u : Finset (Fin n) → ℝ := fun A => ∑ j, if U τ j = A then c j else 0 with hu
  have hbound : ∀ r, IsPolymatroidRankFunction r → (∑ A, u A * r A) = dotProduct π (greedy r τ) := by
    intro r hr
    rw [hu, chain_sum]
    have e1 : ∀ j, r (U τ j) = ∑ i, if τ j ≤ τ i then greedy r τ i else 0 := by
      intro j
      rw [← greedy_tight r hr.1 τ hτ (U τ j) ?_]
      · unfold SumOver U; rw [sum_filter]
      · intro i hi i' hii'
        rw [mem_U] at hi ⊢; exact le_trans hi hii'
    simp_rw [e1, mul_sum]
    rw [sum_comm]
    unfold dotProduct
    refine sum_congr rfl fun i _ => ?_
    rw [← htel i, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  refine ⟨u, fun A => sum_nonneg fun j _ => ?_, hπ, fun i => ?_, ?_, ?_⟩
  · split_ifs
    · exact hc0 j
    · exact le_refl _
  · have := chain_sum τ c (fun A => if i ∈ A then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at this
    rw [sum_filter, ← hu] at *
    rw [this]
    rw [← htel i]
    refine le_of_eq (sum_congr rfl fun j _ => ?_)
    simp only [mem_U]
  · rw [hbound r1 hr1]; exact hdot _ (Or.inl (greedy_mem r1 hr1 τ))
  · rw [hbound r2 hr2]; exact hdot _ (Or.inr (greedy_mem r2 hr2 τ))

end PM90

open Disjunctive.Polymatroids in
theorem solution {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsPolymatroidRankFunction r1) (hr2 : IsPolymatroidRankFunction r2) :
    PiSet r1 r2 = PiProjSystem r1 r2 :=
  Set.Subset.antisymm (PM90.sub_dir r1 r2 hr1 hr2) (PM90.sup_dir r1 r2)
