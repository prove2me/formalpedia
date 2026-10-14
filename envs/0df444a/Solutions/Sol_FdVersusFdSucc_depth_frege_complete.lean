-- Prove2me | solution 1 for FdVersusFdSucc.depth_frege_complete
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T13:48:56.484168+00:00
-- url     : https://prove2.me/submissions/6a8f67f3-4d21-4685-a62b-ec048d87a96f

import Mathlib
import Definitions.Def_FdVersusFdSucc_defs

set_option autoImplicit false

open Filter

namespace FdVersusFdSucc.FrCompleteA
open FdVersusFdSucc Formula

/-- Classical decidable equality on formulas (only used for `List.erase` and `decide`). -/
noncomputable instance instDecEqFormula : DecidableEq Formula := Classical.decEq _

/-! ### Equation lemmas for `size` and `depth` -/

theorem size_and (As : List Formula) : (Formula.and As).size = (As.map Formula.size).sum + 1 := by
  simp [Formula.size]

theorem size_or (As : List Formula) : (Formula.or As).size = (As.map Formula.size).sum + 1 := by
  simp [Formula.size]

theorem depth_and (As : List Formula) :
    (Formula.and As).depth = (As.map Formula.depth).foldr max 0 + 1 := by
  simp [Formula.depth]

theorem depth_or (As : List Formula) :
    (Formula.or As).depth = (As.map Formula.depth).foldr max 0 + 1 := by
  simp [Formula.depth]

theorem le_foldr_max (l : List Formula) (A : Formula) (h : A ∈ l) :
    A.depth ≤ (l.map Formula.depth).foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons B l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem depth_lt_and {As : List Formula} {A : Formula} (h : A ∈ As) :
    A.depth < (Formula.and As).depth := by
  rw [depth_and]; exact Nat.lt_succ_of_le (le_foldr_max As A h)

theorem depth_lt_or {As : List Formula} {A : Formula} (h : A ∈ As) :
    A.depth < (Formula.or As).depth := by
  rw [depth_or]; exact Nat.lt_succ_of_le (le_foldr_max As A h)

theorem size_le_sum (l : List Formula) (A : Formula) (h : A ∈ l) :
    A.size ≤ (l.map Formula.size).sum := by
  induction l with
  | nil => simp at h
  | cons B l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact le_trans (ih h) (Nat.le_add_left _ _)

/-! ### Validity, derivability, and the structural properties of proofs -/

/-- A sequent is valid if under every assignment some member is true. -/
def Valid (Γ : Sequent) : Prop := ∀ v : ℕ → Bool, ∃ B ∈ Γ, B.eval v = true

/-- A sequent is derivable in `F_d` if it occurs as a line of some depth-`d` proof. -/
def Derivable (d : ℕ) (Γ : Sequent) : Prop := ∃ π, IsDepthProof d π ∧ Γ ∈ π

theorem step_mono {prev prev' : List Sequent} {Γ : Sequent} (h : Step prev Γ)
    (hs : prev ⊆ prev') : Step prev' Γ := by
  cases h with
  | ax Γ i hp hn => exact Step.ax Γ i hp hn
  | andI Γ As h => exact Step.andI Γ As (fun A hA => hs (h A hA))
  | orI Γ As A hA h => exact Step.orI Γ As A hA (hs h)
  | weaken Γ₀ _ h hsub => exact Step.weaken Γ₀ _ (hs h) hsub
  | cut Γ A h1 h2 => exact Step.cut Γ A (hs h1) (hs h2)

theorem isDepthProof_nil (d : ℕ) : IsDepthProof d [] :=
  ⟨fun i h => by simp at h, fun Γ h => by simp at h⟩

theorem isDepthProof_append {d : ℕ} {π₁ π₂ : List Sequent} (h₁ : IsDepthProof d π₁)
    (h₂ : IsDepthProof d π₂) : IsDepthProof d (π₁ ++ π₂) := by
  refine ⟨fun i hi => ?_, fun Γ hΓ A hA => ?_⟩
  · by_cases hlt : i < π₁.length
    · have e1 : (π₁ ++ π₂).take i = π₁.take i := by
        rw [List.take_append, Nat.sub_eq_zero_of_le hlt.le]; simp
      rw [e1, List.getElem_append_left hlt]
      exact h₁.1 i hlt
    · push Not at hlt
      have hj : i - π₁.length < π₂.length := by simp at hi; omega
      rw [List.getElem_append_right hlt]
      apply step_mono (h₂.1 _ hj)
      rw [List.take_append]
      exact List.subset_append_right _ _
  · rcases List.mem_append.mp hΓ with h | h
    · exact h₁.2 Γ h A hA
    · exact h₂.2 Γ h A hA

theorem isDepthProof_snoc {d : ℕ} {π : List Sequent} {Γ : Sequent} (h : IsDepthProof d π)
    (hs : Step π Γ) (hd : ∀ B ∈ Γ, B.depth ≤ d) : IsDepthProof d (π ++ [Γ]) := by
  refine ⟨fun i hi => ?_, fun Δ hΔ A hA => ?_⟩
  · by_cases hlt : i < π.length
    · have e1 : (π ++ [Γ]).take i = π.take i := by
        rw [List.take_append, Nat.sub_eq_zero_of_le hlt.le]; simp
      rw [e1, List.getElem_append_left hlt]
      exact h.1 i hlt
    · have hi' : i = π.length := by simp at hi; omega
      subst hi'
      have e1 : (π ++ [Γ]).take π.length = π := by simp
      rw [e1]
      simpa using hs
  · rcases List.mem_append.mp hΔ with h' | h'
    · exact h.2 Δ h' A hA
    · rw [List.mem_singleton] at h'
      subst h'
      exact hd A hA

theorem collect (d : ℕ) (S : List Sequent) (hS : ∀ Γ ∈ S, Derivable d Γ) :
    ∃ π, IsDepthProof d π ∧ S ⊆ π := by
  induction S with
  | nil => exact ⟨[], isDepthProof_nil d, List.nil_subset _⟩
  | cons Γ S ih =>
    obtain ⟨π₁, h₁, hΓ⟩ := hS Γ List.mem_cons_self
    obtain ⟨π₂, h₂, hsub⟩ := ih (fun Δ hΔ => hS Δ (List.mem_cons_of_mem _ hΔ))
    refine ⟨π₁ ++ π₂, isDepthProof_append h₁ h₂, ?_⟩
    intro Δ hΔ
    rcases List.mem_cons.mp hΔ with rfl | hΔ
    · exact List.mem_append_left _ hΓ
    · exact List.mem_append_right _ (hsub hΔ)

/-- A rule application whose premises are all derivable has a derivable conclusion. -/
theorem der_step {d : ℕ} (S : List Sequent) (Γ : Sequent) (hS : ∀ Δ ∈ S, Derivable d Δ)
    (hs : Step S Γ) (hd : ∀ B ∈ Γ, B.depth ≤ d) : Derivable d Γ := by
  obtain ⟨π, hπ, hsub⟩ := collect d S hS
  exact ⟨π ++ [Γ], isDepthProof_snoc hπ (step_mono hs hsub) hd,
    List.mem_append_right _ (List.mem_singleton_self _)⟩

theorem Derivable.depth_le {d : ℕ} {Γ : Sequent} (h : Derivable d Γ) :
    ∀ B ∈ Γ, B.depth ≤ d := by
  obtain ⟨π, hπ, hΓ⟩ := h
  exact hπ.2 Γ hΓ

theorem der_weaken {d : ℕ} {Γ Δ : Sequent} (h : Derivable d Γ) (hsub : Γ ⊆ Δ)
    (hd : ∀ B ∈ Δ, B.depth ≤ d) : Derivable d Δ :=
  der_step [Γ] Δ (fun Δ' hΔ' => by rw [List.mem_singleton] at hΔ'; subst hΔ'; exact h)
    (Step.weaken Γ Δ (List.mem_singleton_self _) hsub) hd

theorem der_orI {d : ℕ} {Γ : Sequent} {As : List Formula} {A : Formula} (hA : A ∈ As)
    (h : Derivable d (A :: Γ)) (hd : (Formula.or As).depth ≤ d) :
    Derivable d (Formula.or As :: Γ) :=
  der_step [A :: Γ] _ (fun Δ' hΔ' => by rw [List.mem_singleton] at hΔ'; subst hΔ'; exact h)
    (Step.orI Γ As A hA (List.mem_singleton_self _)) (by
      intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · exact hd
      · exact h.depth_le B (List.mem_cons_of_mem _ hB))

theorem der_andI {d : ℕ} {Γ : Sequent} {As : List Formula}
    (h : ∀ A ∈ As, Derivable d (A :: Γ)) (hd : ∀ B ∈ Formula.and As :: Γ, B.depth ≤ d) :
    Derivable d (Formula.and As :: Γ) :=
  der_step (As.map fun A => A :: Γ) _ (by
      intro Δ hΔ
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hΔ
      exact h A hA)
    (Step.andI Γ As (fun A hA => List.mem_map.mpr ⟨A, hA, rfl⟩)) hd

theorem der_ax {d : ℕ} {Γ : Sequent} (i : ℕ) (hp : pos i ∈ Γ) (hn : neg i ∈ Γ)
    (hd : ∀ B ∈ Γ, B.depth ≤ d) : Derivable d Γ :=
  der_step [] Γ (by simp) (Step.ax Γ i hp hn) hd

/-- If `⋁Bs ∈ Δ` and every member of `As` lies in `Bs`, then `As, Δ` derivable implies `Δ`
derivable (repeated `∨`-introduction followed by contraction). -/
theorem der_absorb {d : ℕ} (Bs : List Formula) (Δ : Sequent) (hor : Formula.or Bs ∈ Δ) :
    ∀ As : List Formula, (∀ A ∈ As, A ∈ Bs) → Derivable d (As ++ Δ) → Derivable d Δ := by
  intro As
  induction As with
  | nil => intro _ h; simpa using h
  | cons A As ih =>
    intro hsub h
    apply ih (fun A' hA' => hsub A' (List.mem_cons_of_mem _ hA'))
    have hdΔ := h.depth_le
    have h1 : Derivable d (Formula.or Bs :: (As ++ Δ)) :=
      der_orI (hsub A List.mem_cons_self) (by simpa using h)
        (hdΔ _ (List.mem_append_right _ hor))
    apply der_weaken h1
    · intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · exact List.mem_append_right _ hor
      · exact hB
    · intro B hB
      exact hdΔ B (List.mem_cons_of_mem _ hB)

/-! ### The measure and the main lemma -/

/-- Total size of a sequent. -/
def mu (Γ : Sequent) : ℕ := (Γ.map Formula.size).sum

theorem mu_erase {Γ : Sequent} {B : Formula} (h : B ∈ Γ) : mu Γ = B.size + mu (Γ.erase B) := by
  unfold mu
  have := (List.perm_cons_erase h).map Formula.size
  rw [this.sum_eq]
  simp

theorem mu_cons (A : Formula) (Γ : Sequent) : mu (A :: Γ) = A.size + mu Γ := by
  simp [mu]

theorem mu_append (As : List Formula) (Γ : Sequent) :
    mu (As ++ Γ) = (As.map Formula.size).sum + mu Γ := by
  simp [mu]

/-- Main lemma (cut-free completeness): every valid sequent of depth-`≤ d` formulas is
derivable in `F_d`. By strong induction on the total size of the sequent. -/
theorem main (d : ℕ) : ∀ (n : ℕ) (Γ : Sequent), mu Γ = n → Valid Γ →
    (∀ B ∈ Γ, B.depth ≤ d) → Derivable d Γ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ hn hv hd
  by_cases hand : ∃ As, Formula.and As ∈ Γ
  · obtain ⟨As, hAs⟩ := hand
    have hdA : (Formula.and As).depth ≤ d := hd _ hAs
    have hdΓ' : ∀ B ∈ Γ.erase (Formula.and As), B.depth ≤ d :=
      fun B hB => hd B (List.erase_subset hB)
    have hmu := mu_erase hAs
    have h1 : Derivable d (Formula.and As :: Γ.erase (Formula.and As)) := by
      apply der_andI
      · intro A hA
        refine ih _ ?_ (A :: Γ.erase (Formula.and As)) rfl ?_ ?_
        · rw [← hn, hmu, mu_cons, size_and]
          have := size_le_sum As A hA
          omega
        · intro v
          obtain ⟨B, hB, hBv⟩ := hv v
          by_cases hBe : B = Formula.and As
          · subst hBe
            refine ⟨A, List.mem_cons_self, ?_⟩
            simp only [Formula.eval, List.all_eq_true, List.mem_attach, true_implies,
              Subtype.forall] at hBv
            exact hBv A hA
          · exact ⟨B, List.mem_cons_of_mem _ ((List.mem_erase_of_ne hBe).mpr hB), hBv⟩
        · intro B hB
          rcases List.mem_cons.mp hB with rfl | hB
          · exact le_trans (depth_lt_and hA).le hdA
          · exact hdΓ' B hB
      · intro B hB
        rcases List.mem_cons.mp hB with rfl | hB
        · exact hdA
        · exact hdΓ' B hB
    apply der_weaken h1 _ hd
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hAs
    · exact List.erase_subset hB
  · push Not at hand
    by_cases hor : ∃ As, Formula.or As ∈ Γ
    · obtain ⟨As, hAs⟩ := hor
      have hdA : (Formula.or As).depth ≤ d := hd _ hAs
      have hdAs : ∀ A ∈ As, A.depth ≤ d := fun A hA => le_trans (depth_lt_or hA).le hdA
      have hmu := mu_erase hAs
      have h1 : Derivable d (As ++ Γ.erase (Formula.or As)) := by
        refine ih _ ?_ _ rfl ?_ ?_
        · rw [← hn, hmu, mu_append, size_or]
          omega
        · intro v
          obtain ⟨B, hB, hBv⟩ := hv v
          by_cases hBe : B = Formula.or As
          · subst hBe
            simp only [Formula.eval, List.any_eq_true, List.mem_attach, true_and,
              Subtype.exists] at hBv
            obtain ⟨A, hA, hAv⟩ := hBv
            exact ⟨A, List.mem_append_left _ hA, hAv⟩
          · exact ⟨B, List.mem_append_right _ ((List.mem_erase_of_ne hBe).mpr hB), hBv⟩
        · intro B hB
          rcases List.mem_append.mp hB with hB | hB
          · exact hdAs B hB
          · exact hd B (List.erase_subset hB)
      have h2 : Derivable d (As ++ Γ) := by
        apply der_weaken h1
        · intro B hB
          rcases List.mem_append.mp hB with hB | hB
          · exact List.mem_append_left _ hB
          · exact List.mem_append_right _ (List.erase_subset hB)
        · intro B hB
          rcases List.mem_append.mp hB with hB | hB
          · exact hdAs B hB
          · exact hd B hB
      exact der_absorb As Γ hAs As (fun A hA => hA) h2
    · push Not at hor
      by_cases hax : ∃ i, pos i ∈ Γ ∧ neg i ∈ Γ
      · obtain ⟨i, hp, hn'⟩ := hax
        exact der_ax i hp hn' hd
      · exfalso
        push Not at hax
        obtain ⟨B, hB, hBv⟩ := hv (fun i => decide (neg i ∈ Γ))
        cases B with
        | pos i =>
          simp only [Formula.eval, decide_eq_true_eq] at hBv
          exact hax i hB hBv
        | neg i =>
          simp only [Formula.eval, Bool.not_eq_true', decide_eq_false_iff_not] at hBv
          exact hBv hB
        | and As => exact hand As hB
        | or As => exact hor As hB

end FdVersusFdSucc.FrCompleteA

open FdVersusFdSucc in
theorem solution (d : ℕ) (A : Formula) (hd : A.depth ≤ d)
    (hA : A.IsTautology) : ∃ π : List Sequent, IsDepthProofOf d π A := by
  obtain ⟨π, hπ, hmem⟩ := FrCompleteA.main d _ [A] rfl
    (fun v => ⟨A, List.mem_singleton_self A, hA v⟩)
    (by
      intro B hB
      rw [List.mem_singleton] at hB
      subst hB
      exact hd)
  exact ⟨π, hπ, hmem⟩
