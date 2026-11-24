-- Prove2me | solution 1 for ConstructiveArboricity.Exact.Supplement.rooted_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T16:15:20.778015+00:00
-- url     : https://prove2.me/submissions/a72ef607-1a8e-4a1f-a039-739bf0e69f1d

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Rooted
set_option autoImplicit false
open Classical
set_option linter.unusedSectionVars false

namespace RootedCore

variable {V A : Type} [Fintype V] [DecidableEq V] [Fintype A]

def hin (h : A → Option V) (S : Finset V) (a : A) : Prop := ∃ w ∈ S, h a = some w

noncomputable def cut (t : A → V) (h : A → Option V) (B : Finset A) (S : Finset V) : ℕ :=
  (B.filter fun a => t a ∈ S ∧ ¬ hin h S a).card

lemma hin_inter (h : A → Option V) (S T : Finset V) (a : A) :
    hin h (S ∩ T) a ↔ hin h S a ∧ hin h T a := by
  constructor
  · rintro ⟨w, hw, hh⟩
    rw [Finset.mem_inter] at hw
    exact ⟨⟨w, hw.1, hh⟩, ⟨w, hw.2, hh⟩⟩
  · rintro ⟨⟨w, hw, hh⟩, ⟨w', hw', hh'⟩⟩
    rw [hh] at hh'
    cases hh'
    exact ⟨w, Finset.mem_inter.2 ⟨hw, hw'⟩, hh⟩

lemma hin_union (h : A → Option V) (S T : Finset V) (a : A) :
    hin h (S ∪ T) a ↔ hin h S a ∨ hin h T a := by
  constructor
  · rintro ⟨w, hw, hh⟩
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · exact Or.inl ⟨w, hw, hh⟩
    · exact Or.inr ⟨w, hw, hh⟩
  · rintro (⟨w, hw, hh⟩ | ⟨w, hw, hh⟩)
    · exact ⟨w, Finset.mem_union_left _ hw, hh⟩
    · exact ⟨w, Finset.mem_union_right _ hw, hh⟩

lemma cut_submod (t : A → V) (h : A → Option V) (B : Finset A) (S T : Finset V) :
    cut t h B (S ∩ T) + cut t h B (S ∪ T) ≤ cut t h B S + cut t h B T := by
  unfold cut
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  simp only [Finset.mem_inter, Finset.mem_union, hin_inter, hin_union]
  by_cases a1 : t a ∈ S <;> by_cases a2 : t a ∈ T <;> by_cases b1 : hin h S a <;>
    by_cases b2 : hin h T a <;> simp [a1, a2, b1, b2]

lemma cut_erase_of_not (t : A → V) (h : A → Option V) (B : Finset A) (a : A) (S : Finset V)
    (hl : ¬ (t a ∈ S ∧ ¬ hin h S a)) : cut t h (B.erase a) S = cut t h B S := by
  unfold cut
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp only [Finset.mem_filter, not_and]
  intro _ h1 h2
  exact hl ⟨h1, h2⟩

lemma cut_erase_of_mem (t : A → V) (h : A → Option V) (B : Finset A) (a : A) (S : Finset V)
    (haB : a ∈ B) (hl : t a ∈ S ∧ ¬ hin h S a) : cut t h (B.erase a) S + 1 = cut t h B S := by
  unfold cut
  rw [Finset.filter_erase, Finset.card_erase_of_mem]
  · have : 0 < (B.filter fun a => t a ∈ S ∧ ¬ hin h S a).card :=
      Finset.card_pos.2 ⟨a, by simpa [haB] using hl⟩
    omega
  · simpa [haB] using hl

lemma cut_sel_eq (t : A → V) (h : A → Option V) (B Sel : Finset A) (R : Finset V)
    (hSel : ∀ a ∈ Sel, t a ∈ R) (X : Finset V) (hX : ∀ x ∈ X, x ∉ R) :
    cut t h (B \ Sel) X = cut t h B X := by
  unfold cut
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun hs => hX _ h2.1 (hSel a hs)⟩, h2⟩

lemma peel_step (t : A → V) (h : A → Option V) (k : ℕ) (B Sel : Finset A) (R : Finset V)
    (hstat : ∀ S : Finset V, S.Nonempty → k + 1 ≤ cut t h B S)
    (hSelR : ∀ a ∈ Sel, t a ∈ R)
    (hinv : ∀ S : Finset V, S.Nonempty → k ≤ cut t h (B \ Sel) S)
    (hR : R ≠ Finset.univ) :
    ∃ a ∈ B \ Sel, t a ∉ R ∧ (∀ w, h a = some w → w ∈ R) ∧
      ∀ S : Finset V, S.Nonempty → k ≤ cut t h ((B \ Sel).erase a) S := by
  by_contra hcon
  push_neg at hcon
  set Res := B \ Sel with hRes
  -- tight sets
  have key : ∀ a ∈ Res, t a ∉ R → (∀ w, h a = some w → w ∈ R) →
      ∃ S : Finset V, S.Nonempty ∧ cut t h Res S = k ∧ t a ∈ S ∧ ¬ hin h S a := by
    intro a ha h1 h2
    obtain ⟨S, hS, hlt⟩ := hcon a ha h1 h2
    by_cases hl : t a ∈ S ∧ ¬ hin h S a
    · have := cut_erase_of_mem t h Res a S ha hl
      have := hinv S hS
      exact ⟨S, hS, by omega, hl⟩
    · rw [cut_erase_of_not t h Res a S hl] at hlt
      exact absurd (hinv S hS) (by omega)
  -- a candidate exists
  have hUne : (Finset.univ \ R).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hR (Finset.eq_univ_of_forall fun x => hsub (Finset.mem_univ x))
  have hUR : ∀ x ∈ (Finset.univ \ R), x ∉ R := fun x hx => (Finset.mem_sdiff.1 hx).2
  have hcU : cut t h Res (Finset.univ \ R) = cut t h B (Finset.univ \ R) :=
    cut_sel_eq t h B Sel R hSelR _ hUR
  have hcU' := hstat _ hUne
  have hpos : 0 < cut t h Res (Finset.univ \ R) := by omega
  obtain ⟨a0, ha0⟩ : ∃ a0, a0 ∈ Res ∧ t a0 ∈ Finset.univ \ R ∧ ¬ hin h (Finset.univ \ R) a0 := by
    unfold cut at hpos
    obtain ⟨a0, ha0⟩ := Finset.card_pos.1 hpos
    rw [Finset.mem_filter] at ha0
    exact ⟨a0, ha0.1, ha0.2⟩
  have cand0 : t a0 ∉ R ∧ ∀ w, h a0 = some w → w ∈ R := by
    refine ⟨(Finset.mem_sdiff.1 ha0.2.1).2, fun w hw => ?_⟩
    by_contra hwR
    exact ha0.2.2 ⟨w, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hwR⟩, hw⟩
  -- minimal tight set containing a candidate tail
  let P : Finset V → Prop := fun X => X.Nonempty ∧ cut t h Res X = k ∧
    ∃ a ∈ Res, t a ∉ R ∧ (∀ w, h a = some w → w ∈ R) ∧ t a ∈ X
  obtain ⟨S0, hS0⟩ := key a0 ha0.1 cand0.1 cand0.2
  have hPne : (Finset.univ.filter P).Nonempty :=
    ⟨S0, by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hS0.1, hS0.2.1, a0, ha0.1, cand0.1, cand0.2, hS0.2.2.1⟩⟩
  obtain ⟨X, hXmem, hXmin⟩ := Finset.exists_min_image _ Finset.card hPne
  rw [Finset.mem_filter] at hXmem
  obtain ⟨_, hXne, hXk, aX, haXR, haX1, haX2, haXX⟩ := hXmem
  have hXmin' : ∀ Z, P Z → X.card ≤ Z.card := fun Z hZ =>
    hXmin Z (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hZ⟩)
  -- (P1)
  have P1 : ∀ a ∈ Res, t a ∉ R → (∀ w, h a = some w → w ∈ R) → t a ∈ X →
      ∀ S : Finset V, S.Nonempty → cut t h Res S = k → t a ∈ S → X ⊆ S := by
    intro a ha h1 h2 haX S hSne hSk haS
    have hsm := cut_submod t h Res X S
    have hi : (X ∩ S).Nonempty := ⟨t a, Finset.mem_inter.2 ⟨haX, haS⟩⟩
    have hu : (X ∪ S).Nonempty := ⟨t a, Finset.mem_union_left _ haX⟩
    have c1 := hinv _ hi
    have c2 := hinv _ hu
    have hk : cut t h Res (X ∩ S) = k := by omega
    have hcard := hXmin' (X ∩ S) ⟨hi, hk, a, ha, h1, h2, Finset.mem_inter.2 ⟨haX, haS⟩⟩
    have heq : X ∩ S = X :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard
    rw [← heq]; exact Finset.inter_subset_right
  -- Y = X \ R
  set Y := X.filter (fun x => x ∉ R) with hY
  have haY : t aX ∈ Y := Finset.mem_filter.2 ⟨haXX, haX1⟩
  have hYne : Y.Nonempty := ⟨_, haY⟩
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYle : cut t h Res Y ≤ cut t h Res X := by
    unfold cut
    apply Finset.card_le_card
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    obtain ⟨haRes, haY1, haY2⟩ := ha
    refine ⟨haRes, hYX haY1, fun hX => ?_⟩
    obtain ⟨w, hwX, hw⟩ := hX
    by_cases hwR : w ∈ R
    · have hY1 := (Finset.mem_filter.1 haY1).2
      obtain ⟨S, hSne, hSk, haS, hnS⟩ := key a haRes hY1
        (fun w' hw' => by rw [hw] at hw'; cases hw'; exact hwR)
      exact hnS ⟨w, P1 a haRes hY1 (fun w' hw' => by rw [hw] at hw'; cases hw'; exact hwR)
        (hYX haY1) S hSne hSk haS hwX, hw⟩
    · exact haY2 ⟨w, Finset.mem_filter.2 ⟨hwX, hwR⟩, hw⟩
  have hYk : cut t h Res Y = k := by
    have := hinv Y hYne
    omega
  have hYcard := hXmin' Y ⟨hYne, hYk, aX, haXR, haX1, haX2, haY⟩
  have hYeq : Y = X := Finset.eq_of_subset_of_card_le hYX hYcard
  have hXU : ∀ x ∈ X, x ∉ R := by
    intro x hx
    rw [← hYeq] at hx
    exact (Finset.mem_filter.1 hx).2
  have e1 := cut_sel_eq t h B Sel R hSelR X hXU
  rw [← hRes] at e1
  have e2 := hstat X hXne
  omega


lemma peel (t : A → V) (h : A → Option V) (k : ℕ) (B : Finset A)
    (hstat : ∀ S : Finset V, S.Nonempty → k + 1 ≤ cut t h B S) :
    ∃ Sel : Finset A, Sel ⊆ B ∧ (∀ v, (Sel.filter fun a => t a = v).card = 1) ∧
      (∃ ρ : V → ℕ, ∀ a ∈ Sel, ∀ w, h a = some w → ρ w < ρ (t a)) ∧
      ∀ S : Finset V, S.Nonempty → k ≤ cut t h (B \ Sel) S := by
  have aux : ∀ m : ℕ, ∀ (R : Finset V) (Sel : Finset A) (ρ : V → ℕ),
      (Finset.univ \ R).card ≤ m → Sel ⊆ B → (∀ a ∈ Sel, t a ∈ R) →
      (∀ v ∈ R, (Sel.filter fun a => t a = v).card = 1) →
      (∀ a ∈ Sel, ∀ w, h a = some w → w ∈ R ∧ ρ w < ρ (t a)) →
      (∀ S : Finset V, S.Nonempty → k ≤ cut t h (B \ Sel) S) →
      ∃ Sel : Finset A, Sel ⊆ B ∧ (∀ v, (Sel.filter fun a => t a = v).card = 1) ∧
        (∃ ρ : V → ℕ, ∀ a ∈ Sel, ∀ w, h a = some w → ρ w < ρ (t a)) ∧
        ∀ S : Finset V, S.Nonempty → k ≤ cut t h (B \ Sel) S := by
    intro m
    induction m with
    | zero =>
      intro R Sel ρ hm hSB hSR hcard hρ hinv
      have hR : R = Finset.univ := by
        have h0 : (Finset.univ \ R) = ∅ := Finset.card_eq_zero.1 (by omega)
        exact Finset.eq_univ_of_forall fun x => by
          by_contra hx
          have : x ∈ Finset.univ \ R := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx⟩
          rw [h0] at this; simp at this
      subst hR
      exact ⟨Sel, hSB, fun v => hcard v (Finset.mem_univ _),
        ⟨ρ, fun a ha w hw => (hρ a ha w hw).2⟩, hinv⟩
    | succ m ih =>
      intro R Sel ρ hm hSB hSR hcard hρ hinv
      by_cases hR : R = Finset.univ
      · subst hR
        exact ⟨Sel, hSB, fun v => hcard v (Finset.mem_univ _),
          ⟨ρ, fun a ha w hw => (hρ a ha w hw).2⟩, hinv⟩
      · obtain ⟨a, haRes, htR, hhR, hcut⟩ := peel_step t h k B Sel R hstat hSR hinv hR
        have haB : a ∈ B := (Finset.mem_sdiff.1 haRes).1
        have haS : a ∉ Sel := (Finset.mem_sdiff.1 haRes).2
        let ρ' : V → ℕ := Function.update ρ (t a) (Option.elim (h a) 0 (fun w => ρ w + 1))
        have hρ'R : ∀ x ∈ R, ρ' x = ρ x := fun x hx =>
          Function.update_of_ne (fun e => htR (by rw [← e]; exact hx)) _ _
        apply ih (insert (t a) R) (insert a Sel) ρ'
        · have hss : (Finset.univ \ insert (t a) R) ⊂ (Finset.univ \ R) := by
            rw [Finset.ssubset_iff_of_subset]
            · exact ⟨t a, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, htR⟩, by simp⟩
            · exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (Finset.subset_insert _ _)
          have := Finset.card_lt_card hss
          omega
        · exact Finset.insert_subset haB hSB
        · intro a' ha'
          rcases Finset.mem_insert.1 ha' with rfl | ha'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hSR a' ha')
        · intro v hv
          have hnone : ∀ a' ∈ Sel, t a' ≠ t a := fun a' ha' e => htR (e ▸ hSR a' ha')
          rcases Finset.mem_insert.1 hv with rfl | hvR
          · have : (insert a Sel).filter (fun a' => t a' = t a) = {a} := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | hx, hx2⟩
                · rfl
                · exact absurd hx2 (hnone x hx)
              · rintro rfl; exact ⟨Or.inl rfl, rfl⟩
            rw [this]; simp
          · have : (insert a Sel).filter (fun a' => t a' = v) = Sel.filter (fun a' => t a' = v) := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨rfl | hx, hx2⟩
                · exact absurd (by rw [hx2]; exact hvR) htR
                · exact ⟨hx, hx2⟩
              · rintro ⟨hx, hx2⟩; exact ⟨Or.inr hx, hx2⟩
            rw [this]; exact hcard v hvR
        · intro a' ha' w hw
          rcases Finset.mem_insert.1 ha' with rfl | ha'
          · have hwR := hhR w hw
            refine ⟨Finset.mem_insert_of_mem hwR, ?_⟩
            rw [hρ'R w hwR]
            simp only [ρ', Function.update_self, hw, Option.elim]
            omega
          · obtain ⟨h1, h2⟩ := hρ a' ha' w hw
            refine ⟨Finset.mem_insert_of_mem h1, ?_⟩
            rw [hρ'R w h1, hρ'R _ (hSR a' ha')]
            exact h2
        · intro S hS
          have : B \ insert a Sel = (B \ Sel).erase a := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
            tauto
          rw [this]; exact hcut S hS
  apply aux (Finset.univ \ (∅ : Finset V)).card ∅ ∅ (fun _ => 0) le_rfl (Finset.empty_subset _)
  · simp
  · simp
  · simp
  · intro S hS
    simpa using le_trans (Nat.le_succ k) (hstat S hS)

theorem core (t : A → V) (h : A → Option V) : ∀ k : ℕ, ∀ B : Finset A,
    (∀ v, (B.filter fun a => t a = v).card = k) →
    (∀ S : Finset V, S.Nonempty → k ≤ cut t h B S) →
    ∃ c : A → ℕ, (∀ a ∈ B, c a < k) ∧ ∀ i < k,
      (∀ v, (B.filter fun a => t a = v ∧ c a = i).card = 1) ∧
      ∃ ρ : V → ℕ, ∀ a ∈ B, c a = i → ∀ w, h a = some w → ρ w < ρ (t a) := by
  intro k
  induction k with
  | zero =>
    intro B hdeg _
    refine ⟨fun _ => 0, fun a ha => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    exfalso
    have := hdeg (t a)
    rw [Finset.card_eq_zero] at this
    have hmem : a ∈ B.filter fun a' => t a' = t a := Finset.mem_filter.2 ⟨ha, rfl⟩
    rw [this] at hmem; simp at hmem
  | succ k ih =>
    intro B hdeg hcut
    obtain ⟨Sel, hSB, hSdeg, ⟨ρ, hρ⟩, hres⟩ := peel t h k B hcut
    have hdeg' : ∀ v, ((B \ Sel).filter fun a => t a = v).card = k := by
      intro v
      have e : (B.filter fun a => t a = v) =
          ((B \ Sel).filter fun a => t a = v) ∪ (Sel.filter fun a => t a = v) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro ⟨hx, hv⟩
          by_cases hxs : x ∈ Sel
          · exact Or.inr ⟨hxs, hv⟩
          · exact Or.inl ⟨⟨hx, hxs⟩, hv⟩
        · rintro (⟨⟨hx, _⟩, hv⟩ | ⟨hx, hv⟩)
          · exact ⟨hx, hv⟩
          · exact ⟨hSB hx, hv⟩
      have hd : Disjoint ((B \ Sel).filter fun a => t a = v) (Sel.filter fun a => t a = v) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hx).1).2 (Finset.mem_filter.1 hx').1
      have := hdeg v
      rw [e, Finset.card_union_of_disjoint hd, hSdeg v] at this
      omega
    obtain ⟨c', hc'lt, hc'⟩ := ih (B \ Sel) hdeg' hres
    refine ⟨fun a => if a ∈ Sel then k else c' a, ?_, ?_⟩
    · intro a ha
      by_cases has : a ∈ Sel
      · simp [has]
      · have := hc'lt a (Finset.mem_sdiff.2 ⟨ha, has⟩)
        simp [has]; omega
    · intro i hi
      by_cases hik : i = k
      · subst hik
        refine ⟨fun v => ?_, ρ, ?_⟩
        · have : (B.filter fun a => t a = v ∧ (if a ∈ Sel then i else c' a) = i) =
              Sel.filter fun a => t a = v := by
            ext x
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hx, hv, hc⟩
              by_cases hxs : x ∈ Sel
              · exact ⟨hxs, hv⟩
              · rw [if_neg hxs] at hc
                have := hc'lt x (Finset.mem_sdiff.2 ⟨hx, hxs⟩)
                omega
            · rintro ⟨hx, hv⟩
              exact ⟨hSB hx, hv, by simp [hx]⟩
          rw [this]; exact hSdeg v
        · intro a ha hc w hw
          dsimp only at hc
          have has : a ∈ Sel := by
            by_contra hxs
            have := hc'lt a (Finset.mem_sdiff.2 ⟨ha, hxs⟩)
            rw [if_neg hxs] at hc
            omega
          exact hρ a has w hw
      · have hik' : i < k := by omega
        obtain ⟨hcard, ρ', hρ'⟩ := hc' i hik'
        refine ⟨fun v => ?_, ρ', ?_⟩
        · have : (B.filter fun a => t a = v ∧ (if a ∈ Sel then k else c' a) = i) =
              (B \ Sel).filter fun a => t a = v ∧ c' a = i := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · rintro ⟨hx, hv, hc⟩
              by_cases hxs : x ∈ Sel
              · rw [if_pos hxs] at hc; omega
              · rw [if_neg hxs] at hc; exact ⟨⟨hx, hxs⟩, hv, hc⟩
            · rintro ⟨⟨hx, hxs⟩, hv, hc⟩
              exact ⟨hx, hv, by rw [if_neg hxs]; exact hc⟩
          rw [this]; exact hcard v
        · intro a ha hc w hw
          dsimp only at hc
          by_cases has : a ∈ Sel
          · rw [if_pos has] at hc; omega
          · rw [if_neg has] at hc
            exact hρ' a (Finset.mem_sdiff.2 ⟨ha, has⟩) hc w hw

end RootedCore

namespace RootedDig
open MinCostArbPacking.Main

variable {V E : Type}

lemma joins_symm (D : Digraph V E) {e : E} {a b : V} (h : D.Joins e a b) : D.Joins e b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

lemma joins_tail_of_le (D : Digraph (Option V) E) (F : Finset E) (R : Option V → ℕ)
    (hR : ∀ e ∈ F, R (D.head e) < R (D.tail e)) {e : E} (he : e ∈ F) {a b : Option V}
    (hj : D.Joins e a b) (hle : R b ≤ R a) : D.tail e = a := by
  rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have := hR e he
    rw [h1, h2] at this
    omega

lemma forest_of_rank (D : Digraph (Option V) E) (F : Finset E) (R : Option V → ℕ)
    (hR : ∀ e ∈ F, R (D.head e) < R (D.tail e))
    (hu : ∀ e ∈ F, ∀ e' ∈ F, D.tail e = D.tail e' → e = e') : D.IsForest F := by
  rintro ⟨l, hl, es, vs, hes, hvs, hcy⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => R (vs i))
    ⟨⟨0, hl⟩, Finset.mem_univ _⟩
  set p : Fin l := ⟨(j.val + l - 1) % l, Nat.mod_lt _ hl⟩ with hpdef
  have hp : (⟨((p.val) + 1) % l, Nat.mod_lt _ hl⟩ : Fin l) = j := by
    apply Fin.ext
    have hjl := j.isLt
    simp only [hpdef]
    rcases Nat.eq_zero_or_pos j.val with h0 | h0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : l - 1 < l),
        Nat.sub_add_cancel hl, Nat.mod_self]
    · rw [show j.val + l - 1 = (j.val - 1) + l by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : j.val - 1 < l), Nat.sub_add_cancel h0,
        Nat.mod_eq_of_lt hjl]
  obtain ⟨he1F, he1⟩ := hcy j
  obtain ⟨he0F, he0⟩ := hcy p
  rw [hp] at he0
  have t1 : D.tail (es j) = vs j :=
    joins_tail_of_le D F R hR he1F he1 (hj _ (Finset.mem_univ _))
  have t0 : D.tail (es p) = vs j :=
    joins_tail_of_le D F R hR he0F (joins_symm D he0) (hj _ (Finset.mem_univ _))
  have hpj : es p = es j := hu _ he0F _ he1F (by rw [t0, t1])
  have hpj' : p = j := hes hpj
  have h0 := hR _ he0F
  rw [t0] at h0
  have hh : D.head (es p) = vs p := by
    rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [t0] at h1; rw [h2]; exact h1
    · exact h2
  rw [hh, hpj'] at h0
  omega

def reachN (D : Digraph (Option V) E) (F : Finset E) : ℕ → Option V → Prop
  | 0, x => x = none
  | (j + 1), x => ∃ e ∈ F, D.tail e = x ∧ reachN D F j (D.head e)

lemma rtg_symm {α : Type} {r : α → α → Prop} (hs : ∀ a b, r a b → r b a) {x y : α}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (hs _ _ hbc)).trans ih

lemma conn_of_rank (D : Digraph (Option V) E) (F : Finset E) (R : Option V → ℕ)
    (hR : ∀ e ∈ F, R (D.head e) < R (D.tail e))
    (hex : ∀ v : V, ∃ e ∈ F, D.tail e = some v) : ∀ x y, D.Conn F x y := by
  have symm : ∀ a b : Option V, (∃ e ∈ F, D.Joins e a b) → (∃ e ∈ F, D.Joins e b a) := by
    rintro a b ⟨e, he, hj⟩
    exact ⟨e, he, joins_symm D hj⟩
  have h1 : ∀ n, ∀ x : Option V, R x = n → D.Conn F x none := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx
      cases x with
      | none => exact Relation.ReflTransGen.refl
      | some v =>
        obtain ⟨e, heF, het⟩ := hex v
        have hlt := hR e heF
        rw [het] at hlt
        have := ih (R (D.head e)) (by rw [← hx]; exact hlt) (D.head e) rfl
        exact Relation.ReflTransGen.head ⟨e, heF, Or.inl ⟨het, rfl⟩⟩ this
  intro x y
  exact (h1 _ x rfl).trans (rtg_symm symm (h1 _ y rfl))

lemma rank_of_conn (D : Digraph (Option V) E) (F : Finset E)
    (hconn : ∀ x y, D.Conn F x y) (htail : ∀ e, ∃ v, D.tail e = some v)
    (hu : ∀ e ∈ F, ∀ e' ∈ F, D.tail e = D.tail e' → e = e') :
    ∃ R : Option V → ℕ, ∀ e ∈ F, R (D.head e) < R (D.tail e) := by
  have hD : ∀ x : Option V, ∃ j, reachN D F j x := by
    have hQ : ∀ a b : Option V, (∃ e ∈ F, D.Joins e a b) →
        (a ≠ none ∧ ¬ ∃ j, reachN D F j a) → (b ≠ none ∧ ¬ ∃ j, reachN D F j b) := by
      rintro a b ⟨e, heF, hj⟩ ⟨ha, hna⟩
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hnb : ¬ ∃ j, reachN D F j b := by
          rintro ⟨j, hjb⟩
          exact hna ⟨j + 1, e, heF, h1, by rw [h2]; exact hjb⟩
        exact ⟨fun hbn => hnb ⟨0, hbn⟩, hnb⟩
      · obtain ⟨v, hv⟩ := htail e
        have hnb : ¬ ∃ j, reachN D F j b := by
          rintro ⟨j, hjb⟩
          cases j with
          | zero =>
            have hb : b = none := hjb
            rw [← h1, hv] at hb; cases hb
          | succ j =>
            obtain ⟨e', he'F, ht', hr⟩ := hjb
            have : e' = e := hu _ he'F _ heF (by rw [ht', h1])
            subst this
            exact hna ⟨j, by rw [h2] at hr; exact hr⟩
        exact ⟨fun hbn => hnb ⟨0, hbn⟩, hnb⟩
    intro x
    by_contra hx
    have hQx : x ≠ none ∧ ¬ ∃ j, reachN D F j x :=
      ⟨fun h => hx ⟨0, h⟩, hx⟩
    have key : ∀ y, Relation.ReflTransGen (fun a b : Option V => ∃ e ∈ F, D.Joins e a b) x y →
        (y ≠ none ∧ ¬ ∃ j, reachN D F j y) := by
      intro y hy
      induction hy with
      | refl => exact hQx
      | tail _ hbc ih => exact hQ _ _ hbc ih
    have := (key none (hconn x none)).1
    exact this rfl
  refine ⟨fun x => Nat.find (hD x), ?_⟩
  intro e heF
  obtain ⟨v, hv⟩ := htail e
  have hspec := Nat.find_spec (hD (D.tail e))
  rw [hv] at hspec ⊢
  generalize hj : Nat.find (hD (some v)) = j at hspec
  cases j with
  | zero => simp [reachN] at hspec
  | succ j =>
    obtain ⟨e', he'F, ht', hr⟩ := hspec
    have : e' = e := hu _ he'F _ heF (by rw [ht', hv])
    subst this
    have hle := Nat.find_min' (hD (D.head e')) hr
    show Nat.find (hD (D.head e')) < Nat.find (hD (some v))
    rw [hj]; omega

end RootedDig

namespace ConstructiveArboricity.Exact.Supplement
open ConstructiveArboricity.Exact MinCostArbPacking.Main

section App
variable (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n)

def tl : RootArc G k tail → Fin G.n := Sum.elim tail (fun s => s.1)

def hd : RootArc G k tail → Option (Fin G.n) :=
  Sum.elim (fun e => some (G.head tail e)) (fun _ => none)

lemma rg_tail (a : RootArc G k tail) :
    (rootedGraph G k tail).tail a = some (tl G k tail a) := by
  rcases a with e | ⟨v, j⟩ <;> rfl

lemma rg_head (a : RootArc G k tail) : (rootedGraph G k tail).head a = hd G k tail a := by
  rcases a with e | ⟨v, j⟩ <;> rfl

lemma deg_eq (h : G.IsKOut k tail) (v : Fin G.n) :
    ((Finset.univ : Finset (RootArc G k tail)).filter fun a => tl G k tail a = v).card = k := by
  rw [Finset.card_filter, Fintype.sum_sum_type]
  have h1 : (∑ e : Fin G.m, if tl G k tail (Sum.inl e) = v then 1 else 0) =
      G.outdegree tail v := by
    unfold Graph.outdegree
    rw [Finset.card_filter]
    rfl
  have h2 : (∑ s : (Σ u : Fin G.n, Fin (k - G.outdegree tail u)),
      if tl G k tail (Sum.inr s) = v then 1 else 0) = k - G.outdegree tail v := by
    rw [Fintype.sum_sigma]
    have : ∀ x : Fin G.n, (∑ y : Fin (k - G.outdegree tail x),
        if tl G k tail (Sum.inr ⟨x, y⟩) = v then 1 else 0) =
        if x = v then k - G.outdegree tail x else 0 := by
      intro x; by_cases hx : x = v <;> simp [tl, hx]
    rw [Finset.sum_congr rfl (fun x _ => this x)]
    simp
  rw [h1, h2]
  have := h.2 v
  omega

lemma head_of_tail_fst (hor : G.IsOrientation tail) (e : Fin G.m) :
    (tail e = (G.ends e).1 → G.head tail e = (G.ends e).2) ∧
    (tail e = (G.ends e).2 → G.head tail e = (G.ends e).1) := by
  constructor
  · intro h1; simp [Graph.head, h1]
  · intro h1
    have hne := G.noLoops e
    have : tail e ≠ (G.ends e).1 := by rw [h1]; exact fun h => hne h.symm
    simp [Graph.head, this]

lemma forest_edges_le {n : ℕ} (H : SimpleGraph (Fin n)) (hH : H.IsAcyclic) (S : Finset (Fin n))
    (hS : S.Nonempty) (E : Finset (Sym2 (Fin n)))
    (hE : ∀ x ∈ E, x ∈ H.edgeSet ∧ ∀ v ∈ x, v ∈ S) : E.card ≤ S.card - 1 := by
  obtain ⟨s0, hs0⟩ := hS
  haveI : Nonempty (↥(S : Set (Fin n))) := ⟨⟨s0, hs0⟩⟩
  have hac : (H.induce (S : Set (Fin n))).IsAcyclic := hH.induce _
  obtain ⟨T, hle, -, hT⟩ := (SimpleGraph.connected_top (V := ↥(S : Set (Fin n)))).exists_isTree_le_of_le_of_isAcyclic
    (le_top (a := H.induce (S : Set (Fin n)))) hac
  have h1 := hT.card_edgeFinset
  have h2 : (H.induce (S : Set (Fin n))).edgeFinset.card ≤ T.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)
  have h3 : E.card ≤ (H.edgeFinset.filter fun e => e.toFinset ⊆ S).card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    refine ⟨(hE x hx).1, ?_⟩
    intro v hv
    exact (hE x hx).2 v (by simpa using hv)
  rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset] at h3
  have h4 : Fintype.card ↥(S : Set (Fin n)) = S.card := by simp
  omega

lemma edge_mem_onEdges (C : Set (Fin G.m)) (e : Fin G.m) (he : e ∈ C) :
    G.edge e ∈ (G.onEdges C).edgeSet := by
  unfold Graph.onEdges
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨⟨e, he, rfl⟩, ?_⟩
  unfold Graph.edge
  intro hd
  exact G.noLoops e (Sym2.mk_isDiag_iff.1 hd)

lemma inside_le (c : Fin G.m → Fin k) (hc : G.ForestPartition k c) (S : Finset (Fin G.n))
    (hS : S.Nonempty) :
    (Finset.univ.filter fun e : Fin G.m => (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S).card ≤
      k * (S.card - 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := c) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  calc _ ≤ ∑ _i : Fin k, (S.card - 1) := by
        apply Finset.sum_le_sum
        intro i _
        have key := forest_edges_le (G.onEdges {e | c e = i}) (hc i) S hS
          (((Finset.univ.filter fun e : Fin G.m => (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S).filter
            fun e => c e = i).image G.edge) (by
            intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨e, he, rfl⟩ := hx
            rw [Finset.mem_filter, Finset.mem_filter] at he
            refine ⟨edge_mem_onEdges G _ e he.2, ?_⟩
            intro v hv
            unfold Graph.edge at hv
            rw [Sym2.mem_iff] at hv
            rcases hv with rfl | rfl
            · exact he.1.2.1
            · exact he.1.2.2)
        rw [Finset.card_image_of_injective _ (show Function.Injective G.edge from G.simple)] at key
        exact key
    _ = k * (S.card - 1) := by simp

lemma cut_ge (h : G.IsKOut k tail) (hF : G.Feasible k) (S : Finset (Fin G.n)) (hS : S.Nonempty) :
    k ≤ RootedCore.cut (tl G k tail) (hd G k tail) Finset.univ S := by
  obtain ⟨c, hc⟩ := hF
  set tot := (Finset.univ.filter fun a : RootArc G k tail => tl G k tail a ∈ S).card with htot
  have htot' : tot = k * S.card := by
    rw [htot, Finset.card_eq_sum_card_fiberwise (f := tl G k tail) (t := S)
      (s := Finset.univ.filter fun a : RootArc G k tail => tl G k tail a ∈ S)
      (fun x hx => by simpa using hx)]
    have : ∀ v ∈ S, ((Finset.univ.filter fun a : RootArc G k tail => tl G k tail a ∈ S).filter
        fun a => tl G k tail a = v).card = k := by
      intro v hv
      have hh : ((Finset.univ.filter fun a : RootArc G k tail => tl G k tail a ∈ S).filter
          fun a => tl G k tail a = v) = Finset.univ.filter fun a => tl G k tail a = v := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h'; exact ⟨h' ▸ hv, h'⟩
      rw [hh]
      exact deg_eq G k tail h v
    rw [Finset.sum_congr rfl this]
    simp [mul_comm]
  set ins := (Finset.univ.filter fun a : RootArc G k tail =>
    tl G k tail a ∈ S ∧ RootedCore.hin (hd G k tail) S a).card with hins
  have hsum : RootedCore.cut (tl G k tail) (hd G k tail) Finset.univ S + ins = tot := by
    unfold RootedCore.cut
    rw [htot, hins]
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h1 : tl G k tail a ∈ S <;> by_cases h2 : RootedCore.hin (hd G k tail) S a <;>
      simp [h1, h2]
  have hins_le : ins ≤ (Finset.univ.filter fun e : Fin G.m =>
      (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S).card := by
    calc ins ≤ ((Finset.univ.filter fun e : Fin G.m =>
          (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S).image
          (Sum.inl : Fin G.m → RootArc G k tail)).card := by
          apply Finset.card_le_card
          intro a ha
          rw [Finset.mem_filter] at ha
          rw [Finset.mem_image]
          rcases a with e | ⟨v, j⟩
          · refine ⟨e, ?_, rfl⟩
            obtain ⟨h1, w, hw, hh⟩ := ha.2
            have h1' : tail e ∈ S := h1
            have hh' : G.head tail e = w := by simpa [hd] using hh
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rcases h.1 e with h2 | h2
            · have h3 := (head_of_tail_fst G tail h.1 e).1 h2
              rw [h2] at h1'
              exact ⟨h1', by rw [← h3, hh']; exact hw⟩
            · have h3 := (head_of_tail_fst G tail h.1 e).2 h2
              rw [h2] at h1'
              exact ⟨by rw [← h3, hh']; exact hw, h1'⟩
          · exfalso
            obtain ⟨_, w, _, hh⟩ := ha.2
            simp [hd] at hh
      _ ≤ _ := Finset.card_image_le
  have h3 := inside_le G k c hc S hS
  obtain ⟨s', hs'⟩ : ∃ s', S.card = s' + 1 := ⟨S.card - 1, by have := hS.card_pos; omega⟩
  rw [hs'] at htot' h3
  simp only [Nat.add_sub_cancel] at h3
  rw [Nat.mul_succ] at htot'
  omega

lemma acyclic_of_rank (hor : G.IsOrientation tail) (C : Set (Fin G.m)) (R : Fin G.n → ℕ)
    (hR : ∀ e ∈ C, R (G.head tail e) < R (tail e))
    (hu : ∀ e ∈ C, ∀ e' ∈ C, tail e = tail e' → e = e') : (G.onEdges C).IsAcyclic := by
  intro u p hp
  obtain ⟨x, hxm, hmax⟩ := Finset.exists_max_image p.support.toFinset R
    ⟨u, by simp⟩
  have hx : x ∈ p.support := by simpa using hxm
  have h2 := hp.ncard_neighborSet_toSubgraph_eq_two hx
  obtain ⟨y1, y2, hne, hset⟩ := Set.ncard_eq_two.1 h2
  have hnb : ∀ y ∈ ({y1, y2} : Set (Fin G.n)), (G.onEdges C).Adj x y ∧ y ∈ p.support := by
    intro y hy
    rw [← hset] at hy
    have hadj : p.toSubgraph.Adj x y := hy
    refine ⟨p.toSubgraph.adj_sub hadj, ?_⟩
    have := hadj.snd_mem
    rw [SimpleGraph.Walk.verts_toSubgraph] at this
    exact this
  have key : ∀ y, (G.onEdges C).Adj x y → R y ≤ R x → ∃ e ∈ C, tail e = x ∧ G.head tail e = y := by
    intro y hadj hy
    unfold Graph.onEdges at hadj
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨⟨e, heC, hee⟩, hxy⟩ := hadj
    refine ⟨e, heC, ?_⟩
    unfold Graph.edge at hee
    rw [Sym2.eq_iff] at hee
    rcases hor e with h1 | h1
    · have hh := (head_of_tail_fst G tail hor e).1 h1
      rcases hee with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨h1.trans a, hh.trans b⟩
      · exfalso
        have := hR e heC
        rw [hh, h1, a, b] at this
        omega
    · have hh := (head_of_tail_fst G tail hor e).2 h1
      rcases hee with ⟨a, b⟩ | ⟨a, b⟩
      · exfalso
        have := hR e heC
        rw [hh, h1, a, b] at this
        omega
      · exact ⟨h1.trans b, hh.trans a⟩
  obtain ⟨hy1, hy1s⟩ := hnb y1 (by simp)
  obtain ⟨hy2, hy2s⟩ := hnb y2 (by simp)
  obtain ⟨e1, he1, ht1, hh1⟩ := key y1 hy1 (hmax _ (by simpa using hy1s))
  obtain ⟨e2, he2, ht2, hh2⟩ := key y2 hy2 (hmax _ (by simpa using hy2s))
  have : e1 = e2 := hu _ he1 _ he2 (by rw [ht1, ht2])
  subst this
  exact hne (hh1.symm.trans hh2)

end App
end ConstructiveArboricity.Exact.Supplement

namespace ConstructiveArboricity.Exact.Supplement
open ConstructiveArboricity.Exact MinCostArbPacking.Main

lemma fwd (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n) (h : G.IsKOut k tail)
    (hF : G.Feasible k) : RootedPartition G k tail := by
  obtain ⟨c, hc, hcρ⟩ := RootedCore.core (tl G k tail) (hd G k tail) k Finset.univ
    (deg_eq G k tail h) (cut_ge G k tail h hF)
  refine ⟨fun a => ⟨c a, hc a (Finset.mem_univ _)⟩, fun i => ?_⟩
  obtain ⟨hcard, ρ, hρ⟩ := hcρ i.val i.isLt
  have hmem : ∀ a : RootArc G k tail,
      a ∈ (Finset.univ.filter fun a : RootArc G k tail =>
        (⟨c a, hc a (Finset.mem_univ _)⟩ : Fin k) = i) ↔ c a = i.val := by
    intro a; simp [Fin.ext_iff]
  set F := Finset.univ.filter fun a : RootArc G k tail =>
    (⟨c a, hc a (Finset.mem_univ _)⟩ : Fin k) = i with hFdef
  let R : Option (Fin G.n) → ℕ := fun x => Option.elim x 0 (fun v => ρ v + 1)
  have hR : ∀ e ∈ F, R ((rootedGraph G k tail).head e) < R ((rootedGraph G k tail).tail e) := by
    intro e he
    rw [rg_head, rg_tail]
    have := hρ e (Finset.mem_univ _) ((hmem e).1 he)
    cases hh : hd G k tail e with
    | none => simp [R]
    | some w => simp only [R, Option.elim]; have := this w hh; omega
  have hu : ∀ e ∈ F, ∀ e' ∈ F,
      (rootedGraph G k tail).tail e = (rootedGraph G k tail).tail e' → e = e' := by
    intro e he e' he' ht
    rw [rg_tail, rg_tail] at ht
    have ht' : tl G k tail e = tl G k tail e' := Option.some.inj ht
    apply Finset.card_le_one.1 (hcard (tl G k tail e)).le
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl, (hmem e).1 he⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, ht'.symm, (hmem e').1 he'⟩
  have hex : ∀ v : Fin G.n, ∃ e ∈ F, (rootedGraph G k tail).tail e = some v := by
    intro v
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by rw [hcard v]; exact Nat.one_pos)
    rw [Finset.mem_filter] at he
    exact ⟨e, (hmem e).2 he.2.2, by rw [rg_tail, he.2.1]⟩
  show InArborescence G k tail F
  refine ⟨⟨fun e _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
    RootedDig.forest_of_rank _ F R hR hu,
    fun x _ y _ => RootedDig.conn_of_rank _ F R hR hex x y⟩, ?_⟩
  intro v
  have : F.filter (fun e => (rootedGraph G k tail).tail e = some v) =
      Finset.univ.filter (fun a => tl G k tail a = v ∧ c a = i.val) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rg_tail, Option.some.injEq, hmem]
    tauto
  rw [this]; exact hcard v

lemma bwd (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n) (h : G.IsKOut k tail)
    (hP : RootedPartition G k tail) : G.Feasible k := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨fun e => c (Sum.inl e), fun i => ?_⟩
  obtain ⟨⟨_, _, hconn⟩, hdeg⟩ := hc i
  set F := Finset.univ.filter fun a : RootArc G k tail => c a = i with hFdef
  have hu : ∀ e ∈ F, ∀ e' ∈ F,
      (rootedGraph G k tail).tail e = (rootedGraph G k tail).tail e' → e = e' := by
    intro e he e' he' ht
    apply Finset.card_le_one.1 (hdeg (tl G k tail e)).le
    · rw [Finset.mem_filter]; exact ⟨he, rg_tail G k tail e⟩
    · rw [Finset.mem_filter]; exact ⟨he', by rw [← ht]; exact rg_tail G k tail e⟩
  obtain ⟨R, hR⟩ := RootedDig.rank_of_conn (rootedGraph G k tail) F
    (fun x y => hconn x (Finset.mem_univ _) y (Finset.mem_univ _))
    (fun e => ⟨tl G k tail e, rg_tail G k tail e⟩) hu
  show (G.onEdges {e | c (Sum.inl e) = i}).IsAcyclic
  refine acyclic_of_rank G tail h.1 {e | c (Sum.inl e) = i} (fun v => R (some v)) ?_ ?_
  · intro e he
    have := hR (Sum.inl e) (by rw [hFdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, he⟩)
    rw [rg_head, rg_tail] at this
    simpa [hd, tl] using this
  · intro e he e' he' ht
    have := hu (Sum.inl e) (by rw [hFdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, he⟩)
      (Sum.inl e') (by rw [hFdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, he'⟩)
      (by rw [rg_tail, rg_tail]; simp only [tl, Sum.elim_inl]; rw [ht])
    exact Sum.inl_injective this

theorem rooted_equivalence (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n)
    (h : G.IsKOut k tail) : G.Feasible k ↔ RootedPartition G k tail :=
  ⟨fwd G k tail h, bwd G k tail h⟩

end ConstructiveArboricity.Exact.Supplement

theorem solution (G : ConstructiveArboricity.Exact.Graph) (k : ℕ) (tail : Fin G.m → Fin G.n)
    (h : G.IsKOut k tail) :
    G.Feasible k ↔ ConstructiveArboricity.Exact.Supplement.RootedPartition G k tail :=
  ConstructiveArboricity.Exact.Supplement.rooted_equivalence G k tail h
