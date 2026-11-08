-- Prove2me | solution 1 for DRSubmodHull.lemma_4_8_P_mem_Zset
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:14:16.618195+00:00
-- url     : https://prove2.me/submissions/f8105288-c526-43b3-ace0-10995c4dcfc1

import Mathlib
import Definitions.Def_DRSubmodHull_Ppt

set_option autoImplicit false

open Classical

namespace DRSubmodHull.Aux_DR

open DRSubmodHull

variable {V : Type*}

theorem rtg_antisymm (A : V → V → Prop) (hac : ∀ i : V, ¬ Relation.TransGen A i i) {a b : V}
    (hab : Relation.ReflTransGen A a b) (hba : Relation.ReflTransGen A b a) : a = b := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with h | h
  · exact h.symm
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hba with h' | h'
    · exact h'
    · exact absurd (h.trans h') (hac a)

theorem u_mono (A : V → V → Prop) (u : V → ℝ) (hu : ∀ i j : V, A i j → u i ≤ u j) {a b : V}
    (h : Relation.ReflTransGen A a b) : u a ≤ u b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact ih.trans (hu _ _ hbc)

/-- the nearest-ancestor predicate -/
def nearest (A : V → V → Prop) (S : Finset V) (i x : V) : Prop :=
  x ∈ S ∧ Relation.ReflTransGen A x i ∧ ∀ k ∈ S, Relation.ReflTransGen A k i →
    Relation.ReflTransGen A k x

theorem tri_some_iff (A : V → V → Prop) (hac : ∀ i : V, ¬ Relation.TransGen A i i)
    (S : Finset V) (i x : V) : tri A S i = some x ↔ nearest A S i x := by
  unfold tri
  constructor
  · intro h
    split_ifs at h with hex
    · have := hex.choose_spec
      simp only [Option.some.injEq] at h
      rw [← h]
      exact this
  · intro hx
    have hex : ∃ j ∈ S, Relation.ReflTransGen A j i ∧
        ∀ k ∈ S, Relation.ReflTransGen A k i → Relation.ReflTransGen A k j := ⟨x, hx⟩
    rw [dif_pos hex]
    congr 1
    obtain ⟨hcS, hci, hcmax⟩ := hex.choose_spec
    obtain ⟨hxS, hxi, hxmax⟩ := hx
    exact rtg_antisymm A hac (hxmax _ hcS hci) (hcmax _ hxS hxi)

theorem tri_none_iff (A : V → V → Prop) (S : Finset V) (i : V) :
    tri A S i = none ↔ ¬ ∃ x, nearest A S i x := by
  unfold tri
  constructor
  · intro h
    split_ifs at h with hex
    · intro ⟨x, hx⟩; exact hex ⟨x, hx⟩
  · intro h
    rw [dif_neg]
    intro ⟨x, hx⟩; exact h ⟨x, hx⟩

end DRSubmodHull.Aux_DR

open DRSubmodHull DRSubmodHull.Aux_DR in
theorem solution {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (S : Finset V) :
    Ppt A N u S ∈ Zset A N u := by
  obtain ⟨⟨huniq, hac⟩, hNint, hupos, humono⟩ := hstd
  -- value of P in terms of tri
  have hPval : ∀ i, Ppt A N u S i = match tri A S i with
      | some ψ => if ψ ∈ Psi A N u ∧ child A ψ ∉ S then (Int.floor (u ψ) : ℝ) else u ψ
      | none => 0 := fun i => rfl
  -- general bounds: P i ≤ u ψ where ψ is the nearest ancestor
  have hbound : ∀ i, (tri A S i = none ∧ Ppt A N u S i = 0) ∨
      ∃ ψ, nearest A S i ψ ∧ (Ppt A N u S i = (Int.floor (u ψ) : ℝ) ∨ Ppt A N u S i = u ψ) ∧
        (Ppt A N u S i = u ψ ∨ (ψ ∈ Psi A N u ∧ child A ψ ∉ S)) := by
    intro i
    cases h : tri A S i with
    | none => left; refine ⟨rfl, ?_⟩; rw [hPval, h]
    | some ψ =>
      right
      refine ⟨ψ, (tri_some_iff A hac S i ψ).mp h, ?_⟩
      rw [hPval, h]
      simp only
      split_ifs with hc
      · exact ⟨Or.inl rfl, Or.inr hc⟩
      · exact ⟨Or.inr rfl, Or.inl rfl⟩
  -- the nearest ancestor of a vertex of N with non-integral weight is impossible unless it is in Psi
  have hPsi_of : ∀ ψ j, j ∈ N → Relation.ReflTransGen A ψ j → (¬ ∃ k : ℤ, u ψ = k) →
      ψ ∈ Psi A N u := fun ψ j hj hψj hnot => ⟨hnot, j, hj, hψj⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- integrality on N
    intro i hi
    rcases hbound i with ⟨_, h0⟩ | ⟨ψ, hψ, hval, hcase⟩
    · exact ⟨0, by rw [h0]; simp⟩
    · rcases hval with hf | hu
      · exact ⟨_, hf⟩
      · by_cases hint : ∃ k : ℤ, u ψ = k
        · obtain ⟨k, hk⟩ := hint
          exact ⟨k, by rw [hu, hk]⟩
        · exfalso
          have hψPsi := hPsi_of ψ i hi hψ.2.1 hint
          rcases hcase with hcase | ⟨_, hnotS⟩
          · -- child ψ ∈ S, contradiction with nearest
            have hchildS : child A ψ ∈ S := by
              by_contra hc
              have hPi : Ppt A N u S i = (Int.floor (u ψ) : ℝ) := by
                rw [hPval, (tri_some_iff A hac S i ψ).mpr hψ]
                simp only
                rw [if_pos ⟨hψPsi, hc⟩]
              rw [hPi] at hcase
              exact hint ⟨_, hcase.symm⟩
            obtain ⟨ρ, hρ, hρN, _⟩ := hP42 ψ hψPsi
            have hchild : child A ψ = ρ := by
              unfold child
              have hex : ∃ j, A ψ j := ⟨ρ, (hρ ρ).mpr rfl⟩
              rw [dif_pos hex]
              exact (hρ _).mp hex.choose_spec
            have hψi : ψ ≠ i := by
              intro h
              rw [h] at hint
              exact hint (hNint i hi)
            rcases Relation.ReflTransGen.cases_head hψ.2.1 with h | ⟨m, hm, hmi⟩
            · exact hψi h
            · have hmρ : m = ρ := (hρ m).mp hm
              have hρi : Relation.ReflTransGen A (child A ψ) i := by rw [hchild, ← hmρ]; exact hmi
              have hρψ := hψ.2.2 _ hchildS hρi
              rw [hchild] at hρψ
              have hAρ : A ψ ρ := (hρ ρ).mpr rfl
              exact hac ψ (Relation.TransGen.head' hAρ hρψ)
          · have hPi : Ppt A N u S i = (Int.floor (u ψ) : ℝ) := by
              rw [hPval, (tri_some_iff A hac S i ψ).mpr hψ]
              simp only
              rw [if_pos ⟨hψPsi, hnotS⟩]
            exact hint ⟨⌊u ψ⌋, hu.symm.trans hPi⟩
  · -- nonnegativity
    intro i
    show (0 : ℝ) ≤ Ppt A N u S i
    rcases hbound i with ⟨_, h0⟩ | ⟨ψ, _, hval, _⟩
    · rw [h0]
    · rcases hval with hf | hu
      · rw [hf]
        exact_mod_cast Int.floor_nonneg.mpr (hupos ψ).le
      · rw [hu]; exact (hupos ψ).le
  · -- upper bound
    intro i
    show Ppt A N u S i ≤ u i
    rcases hbound i with ⟨_, h0⟩ | ⟨ψ, hψ, hval, _⟩
    · rw [h0]; exact (hupos i).le
    · have hle := u_mono A u humono hψ.2.1
      rcases hval with hf | hu
      · rw [hf]; exact (Int.floor_le _).trans hle
      · rw [hu]; exact hle
  · -- arcs
    intro i j hij
    -- ancestors of j
    have hanc : ∀ k, Relation.ReflTransGen A k j → k = j ∨ Relation.ReflTransGen A k i := by
      intro k hk
      rcases Relation.ReflTransGen.cases_tail hk with h | ⟨m, hkm, hmj⟩
      · exact Or.inl h.symm
      · right
        have := huniq m i j hmj hij
        rw [← this]; exact hkm
    by_cases hjS : j ∈ S
    · -- the nearest ancestor of j is j
      have hnj : nearest A S j j := ⟨hjS, Relation.ReflTransGen.refl, fun k _ hk => hk⟩
      have hPj : Ppt A N u S j =
          if j ∈ Psi A N u ∧ child A j ∉ S then (Int.floor (u j) : ℝ) else u j := by
        rw [hPval, (tri_some_iff A hac S j j).mpr hnj]
      -- P i ≤ u i ≤ u j in general
      have hPi_le : Ppt A N u S i ≤ u i := by
        rcases hbound i with ⟨_, h0⟩ | ⟨ψ, hψ, hval, _⟩
        · rw [h0]; exact (hupos i).le
        · have hle := u_mono A u humono hψ.2.1
          rcases hval with hf | hu
          · rw [hf]; exact (Int.floor_le _).trans hle
          · rw [hu]; exact hle
      have hui : u i ≤ u j := humono i j hij
      rw [hPj]
      split_ifs with hc
      · -- need integrality of P i
        obtain ⟨hjPsi, _⟩ := hc
        have hPi_int : ∃ k : ℤ, Ppt A N u S i = k := by
          rcases hbound i with ⟨_, h0⟩ | ⟨ψ, hψ, hval, _⟩
          · exact ⟨0, by rw [h0]; simp⟩
          · rcases hval with hf | hu
            · exact ⟨_, hf⟩
            · by_cases hint : ∃ k : ℤ, u ψ = k
              · obtain ⟨k, hk⟩ := hint
                exact ⟨k, by rw [hu, hk]⟩
              · exfalso
                obtain ⟨_, jN, hjN, hjjN⟩ := id hjPsi
                have hψj : Relation.ReflTransGen A ψ j := hψ.2.1.tail hij
                have hψPsi := hPsi_of ψ jN hjN (hψj.trans hjjN) hint
                have := hA1.1 ψ hψPsi j hjPsi hψj
                subst this
                exact hac ψ (Relation.TransGen.tail' hψ.2.1 hij)
        obtain ⟨k, hk⟩ := hPi_int
        rw [hk]
        have : (k : ℝ) ≤ u j := by rw [← hk]; linarith
        exact_mod_cast Int.le_floor.mpr this
      · linarith
    · -- the nearest ancestors of i and j coincide
      have hnear : ∀ x, nearest A S j x ↔ nearest A S i x := by
        intro x
        unfold nearest
        have hkey : ∀ k ∈ S, Relation.ReflTransGen A k j ↔ Relation.ReflTransGen A k i := by
          intro k hk
          constructor
          · intro h
            rcases hanc k h with h' | h'
            · exact absurd (h' ▸ hk) hjS
            · exact h'
          · intro h; exact h.tail hij
        constructor
        · rintro ⟨hxS, hxj, hmax⟩
          exact ⟨hxS, (hkey x hxS).mp hxj, fun k hk hki => hmax k hk ((hkey k hk).mpr hki)⟩
        · rintro ⟨hxS, hxi, hmax⟩
          exact ⟨hxS, (hkey x hxS).mpr hxi, fun k hk hkj => hmax k hk ((hkey k hk).mp hkj)⟩
      have htri : tri A S j = tri A S i := by
        cases h : tri A S i with
        | none =>
          rw [tri_none_iff] at h ⊢
          intro ⟨x, hx⟩
          exact h ⟨x, (hnear x).mp hx⟩
        | some x =>
          rw [tri_some_iff A hac] at h ⊢
          exact (hnear x).mpr h
      rw [hPval j, hPval i, htri]
