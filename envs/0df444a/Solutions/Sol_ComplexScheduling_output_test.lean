-- Prove2me | solution 1 for ComplexScheduling.output_test
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:32:17.488021+00:00
-- url     : https://prove2.me/submissions/0f9a831b-a4e4-4f67-8898-b713f3110ea5

import Mathlib
import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling

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

lemma cs_disj {n : ℕ} (p S : Fin n → ℕ) (C D : Finset (Fin n × Fin n)) (I J : Finset (Fin n))
    (hI : IsDisjunctiveSet C D I) (hJI : J ⊆ I) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) :
    ∀ i ∈ J, ∀ j ∈ J, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i := by
  intro i hi j hj hij
  rcases hI.2 i (hJI hi) j (hJI hj) hij with h | h | h | h
  · exact hD _ h
  · exact (hD _ h).symm
  · exact Or.inl (hC _ h)
  · exact Or.inr (hC _ h)

theorem cs_output {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I)
    (Ω : Finset (Fin n)) (hΩ : Ω ⊆ I) (hne : Ω.Nonempty) (i : Fin n) (hi : i ∈ I) (hiΩ : i ∉ Ω)
    (hcond : ∀ μ ∈ Ω, ∀ ν ∈ insert i Ω, dl μ < rel ν + totalProcessing p (insert i Ω))
    (S : Fin n → ℕ) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    ∀ j ∈ Ω, S j + p j ≤ S i := by
  classical
  have hJI : insert i Ω ⊆ I := Finset.insert_subset hi hΩ
  have hdis := cs_disj p S C D I (insert i Ω) hI hJI hC hD
  have hJne : (insert i Ω).Nonempty := ⟨i, Finset.mem_insert_self i Ω⟩
  have hlt : ∀ j ∈ Ω, S j + p j < S i + p i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j0, hj0, hj0le⟩ := hcon
    obtain ⟨μ, hμ, hμmax⟩ := Ω.exists_max_image (fun i => S i + p i) hne
    have hμlast : ∀ j ∈ insert i Ω, S j + p j ≤ S μ + p μ := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hj0le.trans (hμmax j0 hj0)
      · exact hμmax j hj
    obtain ⟨ν, hν, hνmin⟩ := (insert i Ω).exists_min_image S hJne
    have h2 := cs_pack p S _ (insert i Ω) rfl (S ν) (S μ + p μ) hJne
      (fun j hj => ⟨hνmin j hj, hμlast j hj⟩) hdis
    have h1 := hcond μ hμ ν hν
    have h3 := (hw ν).1
    have h4 := (hw μ).2
    unfold totalProcessing at h1
    omega
  intro j hj
  have hji : j ≠ i := fun h => hiΩ (h ▸ hj)
  rcases hdis j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i Ω) hji with h | h
  · exact h
  · have := hlt j hj; omega

end ComplexScheduling

open ComplexScheduling

theorem solution {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I) (hp : ∀ i ∈ I, 0 < p i)
    (Ω : Finset (Fin n)) (hΩ : Ω ⊆ I) (hne : Ω.Nonempty) (i : Fin n) (hi : i ∈ I) (hiΩ : i ∉ Ω)
    (hcond : ∀ μ ∈ Ω, ∀ ν ∈ insert i Ω, dl μ < rel ν + totalProcessing p (insert i Ω))
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    ∀ j ∈ Ω, S j + p j ≤ S i := by
  exact cs_output p Rcap demand prec C D rel dl I hI Ω hΩ hne i hi hiΩ hcond S hC hD hw
