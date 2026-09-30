-- Prove2me | solution 1 for ComplexScheduling.interval_consistency_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:27:51.280179+00:00
-- url     : https://prove2.me/submissions/535476cc-e85e-4fbc-850b-6e7aa17ea020

import Mathlib
import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling

/-- Pairwise non-overlapping activities inside `[a, b]` have total length at most `b - a`. -/
lemma cs_pack {n : ℕ} (p S : Fin n → ℕ) :
    ∀ (k : ℕ) (J : Finset (Fin n)), J.card = k → ∀ a b : ℕ, J.Nonempty →
      (∀ j ∈ J, a ≤ S j ∧ S j + p j ≤ b) →
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i) →
      a + ∑ j ∈ J, p j ≤ b := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro J hJk a b hJne hwin hdis
    obtain ⟨m, hmJ, hmax⟩ := J.exists_max_image S hJne
    rcases (J.erase m).eq_empty_or_nonempty with hemp | hne'
    · have hJ : J = {m} := by
        ext x; constructor
        · intro hx
          by_contra hxm
          have : x ∈ J.erase m := Finset.mem_erase.mpr ⟨by simpa using hxm, hx⟩
          rw [hemp] at this; simp at this
        · intro hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact hmJ
      rw [hJ, Finset.sum_singleton]
      have := hwin m hmJ
      omega
    · have hcard : (J.erase m).card < k := by
        rw [Finset.card_erase_of_mem hmJ, ← hJk]
        exact Nat.sub_lt (Finset.card_pos.mpr hJne) Nat.one_pos
      have hsum : ∑ j ∈ J, p j = p m + ∑ j ∈ J.erase m, p j :=
        (Finset.add_sum_erase J p hmJ).symm
      have hdis' : ∀ i ∈ J.erase m, ∀ j ∈ J.erase m, i ≠ j →
          S i + p i ≤ S j ∨ S j + p j ≤ S i := fun i hi j hj hij =>
        hdis i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) hij
      rcases Nat.eq_zero_or_pos (p m) with hpm | hpm
      · have := ih _ hcard (J.erase m) rfl a b hne'
          (fun j hj => hwin j (Finset.mem_of_mem_erase hj)) hdis'
        rw [hsum, hpm]; omega
      · have hbefore : ∀ j ∈ J.erase m, S j + p j ≤ S m := by
          intro j hj
          have hjJ := Finset.mem_of_mem_erase hj
          have hjm : j ≠ m := Finset.ne_of_mem_erase hj
          have h1 := hmax j hjJ
          rcases hdis j hjJ m hmJ hjm with h | h
          · exact h
          · omega
        have := ih _ hcard (J.erase m) rfl a (S m) hne'
          (fun j hj => ⟨(hwin j (Finset.mem_of_mem_erase hj)).1, hbefore j hj⟩) hdis'
        have := hwin m hmJ
        rw [hsum]; omega

theorem cs_main {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I)
    (J J' J'' : Finset (Fin n)) (hJI : J ⊆ I) (hJ' : J' ⊂ J) (hJ'' : J'' ⊂ J)
    (hne : (J' ∪ J'').Nonempty)
    (hcond : ∀ ν ∈ J \ J', ∀ μ ∈ J \ J'', ν ≠ μ → dl μ < rel ν + totalProcessing p J)
    (S : Fin n → ℕ) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    (∃ i ∈ J', StartsFirstIn S J i) ∨ ∃ i ∈ J'', EndsLastIn p S J i := by
  classical
  -- non-overlap on `J`
  have hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i := by
    intro i hi j hj hij
    rcases hI.2 i (hJI hi) j (hJI hj) hij with h | h | h | h
    · exact hD _ h
    · exact (hD _ h).symm
    · exact Or.inl (hC _ h)
    · exact Or.inr (hC _ h)
  have hJne : J.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    rcases Finset.mem_union.mp hx with h | h
    · exact ⟨x, hJ'.1 h⟩
    · exact ⟨x, hJ''.1 h⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hF, hL⟩ := hcon
  -- the key claim
  have hclaim : ∀ ν ∈ J, ∀ μ ∈ J, (∀ j ∈ J, S ν ≤ S j) → (∀ j ∈ J, S j + p j ≤ S μ + p μ) →
      ν ≠ μ → False := by
    intro ν hν μ hμ hfirst hlast hνμ
    have hν' : ν ∈ J \ J' := Finset.mem_sdiff.mpr ⟨hν, fun h => hF ν h ⟨hν, hfirst⟩⟩
    have hμ' : μ ∈ J \ J'' := Finset.mem_sdiff.mpr ⟨hμ, fun h => hL μ h ⟨hμ, hlast⟩⟩
    have h1 := hcond ν hν' μ hμ' hνμ
    have h2 := cs_pack p S _ J rfl (S ν) (S μ + p μ) hJne
      (fun j hj => ⟨hfirst j hj, hlast j hj⟩) hdis
    have h3 := (hw ν).1
    have h4 := (hw μ).2
    unfold totalProcessing at h1
    omega
  obtain ⟨ν, hν, hνmin⟩ := J.exists_min_image S hJne
  obtain ⟨μ, hμ, hμmax⟩ := J.exists_max_image (fun i => S i + p i) hJne
  by_cases hνμ : ν = μ
  · subst hνμ
    -- some other activity exists
    have hother : ∃ j ∈ J, j ≠ ν := by
      by_contra hno
      push Not at hno
      have hJ : J = {ν} := by
        ext x; constructor
        · intro hx; rw [Finset.mem_singleton]; exact hno x hx
        · intro hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact hν
      rw [hJ] at hJ' hJ''
      have e1 : J' = ∅ := Finset.ssubset_singleton_iff.mp hJ'
      have e2 : J'' = ∅ := Finset.ssubset_singleton_iff.mp hJ''
      rw [e1, e2] at hne
      simp at hne
    obtain ⟨j, hj, hjν⟩ := hother
    rcases hdis ν hν j hj (Ne.symm hjν) with h | h
    · -- `j` also ends last
      have hjlast : ∀ k ∈ J, S k + p k ≤ S j + p j := by
        intro k hk
        have h1 : S k + p k ≤ S ν + p ν := hμmax k hk
        have h2 : S j + p j ≤ S ν + p ν := hμmax j hj
        omega
      exact hclaim ν hν j hj hνmin hjlast (Ne.symm hjν)
    · -- `j` also starts first
      have hjfirst : ∀ k ∈ J, S j ≤ S k := by
        intro k hk
        have := hνmin k hk
        have := hνmin j hj
        omega
      exact hclaim j hj ν hν hjfirst hμmax hjν
  · exact hclaim ν hν μ hμ hνmin hμmax hνμ

end ComplexScheduling

open ComplexScheduling

theorem solution {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I)
    (J J' J'' : Finset (Fin n)) (hJI : J ⊆ I) (hJ' : J' ⊂ J) (hJ'' : J'' ⊂ J)
    (hne : (J' ∪ J'').Nonempty)
    (hcond : ∀ ν ∈ J \ J', ∀ μ ∈ J \ J'', ν ≠ μ → dl μ < rel ν + totalProcessing p J)
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    (∃ i ∈ J', StartsFirstIn S J i) ∨ ∃ i ∈ J'', EndsLastIn p S J i := by
  exact cs_main p Rcap demand prec C D rel dl I hI J J' J'' hJI hJ' hJ'' hne hcond S hC hD hw
