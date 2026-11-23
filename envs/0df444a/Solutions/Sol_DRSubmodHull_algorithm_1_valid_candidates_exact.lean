-- Prove2me | solution 1 for DRSubmodHull.algorithm_1_valid_candidates_exact
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:36:55.683203+00:00
-- url     : https://prove2.me/submissions/92bb7c43-ebd3-4b18-9cc9-9e8e6821e10d

import Mathlib
import Definitions.Def_DRSubmodHull_IsPermFinderOutput

set_option autoImplicit false

open DRSubmodHull Relation

namespace DRSubmodHull.Alg1Proof

theorem mem_take_ofFn {V : Type*} {n : ℕ} (δ : Fin n ≃ V) (ℓ : ℕ) (x : V) :
    x ∈ (List.ofFn δ).take ℓ ↔ ((δ.symm x : Fin n) : ℕ) < ℓ := by
  rw [List.mem_take_iff_getElem]
  simp only [List.getElem_ofFn, List.length_ofFn]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [Equiv.symm_apply_apply]
    exact (lt_min_iff.mp hk).1
  · intro h
    exact ⟨δ.symm x, lt_min h (δ.symm x).isLt, by simp⟩

end DRSubmodHull.Alg1Proof

open DRSubmodHull.Alg1Proof in
theorem solution {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (L : List V) (hL : IsValidPartialPerm A N u L) (hlen : L.length < Fintype.card V) :
    validCandidates A N u L = {i | i ∉ L ∧ IsValidPartialPerm A N u (L ++ [i])} := by
  classical
  obtain ⟨⟨hpar, hacyc⟩, -, hupos, -⟩ := hstd
  have hchild : ∀ ψ ∈ Psi A N u, A ψ (child A ψ) := by
    intro ψ hψ
    obtain ⟨ρ, hρ, -, -⟩ := hP42 ψ hψ
    have hex : ∃ j, A ψ j := ⟨ρ, (hρ ρ).mpr rfl⟩
    unfold child
    rw [dif_pos hex]
    exact hex.choose_spec
  have hne_of_A : ∀ a b, A a b → a ≠ b := by
    intro a b h hab
    subst hab
    exact hacyc a (TransGen.single h)
  have htrans_of : ∀ a b, ReflTransGen A a b → a ≠ b → TransGen A a b := by
    intro a b h hab
    rcases reflTransGen_iff_eq_or_transGen.mp h with h | h
    · exact absurd h.symm hab
    · exact h
  ext i
  simp only [validCandidates, Set.mem_ofPred_eq]
  constructor
  · -- a candidate extends to a valid permutation
    rintro ⟨hiL, hT4, hT8, hT11⟩
    obtain ⟨δ0, hδ0, hL0⟩ := hL
    set ℓ := L.length with hℓ
    have hmem : ∀ x, x ∈ L ↔ ((δ0.symm x : Fin _) : ℕ) < ℓ := by
      intro x
      conv_lhs => rw [hL0]
      exact mem_take_ofFn δ0 ℓ x
    have hnodup : L.Nodup := by
      rw [hL0]
      exact (List.nodup_ofFn.mpr δ0.injective).sublist (List.take_sublist _ _)
    -- ascendant counts
    let κ : V → ℕ := fun x => (Finset.univ.filter (fun y => ReflTransGen A y x)).card
    have hκ : ∀ x y, ReflTransGen A x y → x ≠ y → κ x < κ y := by
      intro x y hxy hne
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨y, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ReflTransGen.refl, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hyx
        exact hacyc x ((htrans_of x y hxy hne).trans_left hyx)
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact hz.trans hxy
    -- a strict total order: more ascendants first, ties by δ0
    let prec : V → V → Prop := fun a b => κ b < κ a ∨ (κ a = κ b ∧ δ0.symm a < δ0.symm b)
    have prec_irrefl : ∀ a, ¬ prec a a := by
      intro a h
      rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
    have prec_trans : ∀ a b c, prec a b → prec b c → prec a c := by
      intro a b c h1 h2
      rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
      · left; omega
      · left; omega
      · left; omega
      · right; exact ⟨h1.trans h2, h1'.trans h2'⟩
    have prec_total : ∀ a b, a ≠ b → prec a b ∨ prec b a := by
      intro a b hab
      rcases lt_trichotomy (κ a) (κ b) with h | h | h
      · right; left; exact h
      · rcases lt_trichotomy (δ0.symm a) (δ0.symm b) with h' | h' | h'
        · left; right; exact ⟨h, h'⟩
        · exact absurd (δ0.symm.injective h') hab
        · right; right; exact ⟨h.symm, h'⟩
      · left; left; exact h
    have prec_desc : ∀ a b, ReflTransGen A a b → a ≠ b → prec b a := fun a b h hne =>
      Or.inl (hκ a b h hne)
    -- the remaining vertices and the rank function
    let R : Finset V := Finset.univ.filter (fun x => x ∉ L ∧ x ≠ i)
    let cnt : V → ℕ := fun x => (R.filter (fun y => prec y x)).card
    let rank : V → ℕ := fun x =>
      if x ∈ L then ((δ0.symm x : Fin _) : ℕ) else if x = i then ℓ else ℓ + 1 + cnt x
    have rank_L : ∀ x, x ∈ L → rank x = ((δ0.symm x : Fin _) : ℕ) := fun x hx => by
      simp only [rank, if_pos hx]
    have rank_i : rank i = ℓ := by simp only [rank, if_neg hiL, if_true]
    have rank_R : ∀ x, x ∉ L → x ≠ i → rank x = ℓ + 1 + cnt x := fun x h1 h2 => by
      simp only [rank, if_neg h1, if_neg h2]
    have hRcard : R.card + (ℓ + 1) = Fintype.card V := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
        (fun x => x ∉ L ∧ x ≠ i)
      have hcompl : (Finset.univ.filter (fun x => ¬ (x ∉ L ∧ x ≠ i))) = insert i L.toFinset := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          List.mem_toFinset]
        tauto
      rw [hcompl, Finset.card_insert_of_notMem (by simpa using hiL),
        List.toFinset_card_of_nodup hnodup, Finset.card_univ] at h
      exact h
    have cnt_lt : ∀ x, x ∈ R → cnt x < R.card := by
      intro x hx
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      refine ⟨x, hx, ?_⟩
      simp only [Finset.mem_filter, not_and]
      intro _
      exact prec_irrefl x
    have cnt_mono : ∀ x y, x ∈ R → prec x y → cnt x < cnt y := by
      intro x y hx hxy
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨x, ?_, ?_⟩
        · simp only [Finset.mem_filter]; exact ⟨hx, hxy⟩
        · simp only [Finset.mem_filter, not_and]; intro _; exact prec_irrefl x
      · intro z hz
        simp only [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, prec_trans _ _ _ hz.2 hxy⟩
    have memR : ∀ x, x ∈ R ↔ x ∉ L ∧ x ≠ i := fun x => by simp [R]
    -- classification by rank
    have rank_ltL : ∀ x, rank x < ℓ ↔ x ∈ L := by
      intro x
      by_cases hx : x ∈ L
      · simp only [rank_L x hx, hx, iff_true]; exact (hmem x).mp hx
      · by_cases hxi : x = i
        · subst hxi; simp [rank_i, hx]
        · rw [rank_R x hx hxi]; simp only [hx, iff_false, not_lt]; omega
    have rank_gtR : ∀ x, ℓ < rank x ↔ x ∉ L ∧ x ≠ i := by
      intro x
      by_cases hx : x ∈ L
      · have := (hmem x).mp hx
        simp only [rank_L x hx, hx, not_true_eq_false, false_and, iff_false, not_lt]
        omega
      · by_cases hxi : x = i
        · subst hxi; simp [rank_i]
        · rw [rank_R x hx hxi]; simp only [hx, not_false_eq_true, ne_eq, hxi, and_self, iff_true]
          omega
    have rank_lt : ∀ x, rank x < Fintype.card V := by
      intro x
      by_cases hx : x ∈ L
      · rw [rank_L x hx]; exact (δ0.symm x).isLt
      · by_cases hxi : x = i
        · subst hxi; rw [rank_i]; exact hlen
        · rw [rank_R x hx hxi]
          have := cnt_lt x ((memR x).mpr ⟨hx, hxi⟩)
          omega
    have rank_inj : Function.Injective rank := by
      intro x y hxy
      by_cases hx : x ∈ L
      · have hy : y ∈ L := (rank_ltL y).mp (hxy ▸ (rank_ltL x).mpr hx)
        rw [rank_L x hx, rank_L y hy] at hxy
        exact δ0.symm.injective (Fin.ext hxy)
      · by_cases hxi : x = i
        · subst hxi
          by_contra hne
          have hyL : y ∉ L := fun hy => by
            have := (rank_ltL y).mpr hy; rw [← hxy, rank_i] at this; exact lt_irrefl _ this
          have := (rank_gtR y).mpr ⟨hyL, Ne.symm hne⟩
          rw [← hxy, rank_i] at this
          exact lt_irrefl _ this
        · have hxR := (rank_gtR x).mpr ⟨hx, hxi⟩
          obtain ⟨hy, hyi⟩ := (rank_gtR y).mp (hxy ▸ hxR)
          by_contra hne
          rw [rank_R x hx hxi, rank_R y hy hyi] at hxy
          rcases prec_total x y hne with h | h
          · have := cnt_mono x y ((memR x).mpr ⟨hx, hxi⟩) h; omega
          · have := cnt_mono y x ((memR y).mpr ⟨hy, hyi⟩) h; omega
    let rk : V → Fin (Fintype.card V) := fun x => ⟨rank x, rank_lt x⟩
    have rk_inj : Function.Injective rk := fun x y h => rank_inj (Fin.mk.inj h)
    have rk_bij : Function.Bijective rk :=
      (Fintype.bijective_iff_injective_and_card rk).mpr ⟨rk_inj, (Fintype.card_fin _).symm⟩
    let δ' : Fin (Fintype.card V) ≃ V := (Equiv.ofBijective rk rk_bij).symm
    have hlt : ∀ x y, δ'.symm x < δ'.symm y ↔ rank x < rank y := fun x y => Iff.rfl
    refine ⟨hiL, δ', ⟨?_, ?_, ?_⟩, ?_⟩
    · -- (1) equal-u descendants come first
      intro a b hab hRT hu
      rw [hlt]
      by_cases ha : a ∈ L
      · have h := hδ0.1 a b hab hRT hu
        have hb : b ∈ L := (hmem b).mpr (lt_trans h ((hmem a).mp ha))
        rw [rank_L a ha, rank_L b hb]
        exact h
      · by_cases hai : a = i
        · subst hai
          have hb : b ∈ L := by
            by_contra hb
            exact hT4 ⟨b, hRT, Ne.symm hab, hb, hu.symm⟩
          rw [rank_i]
          exact (rank_ltL b).mpr hb
        · have haR := (rank_gtR a).mpr ⟨ha, hai⟩
          by_cases hb : b ∈ L
          · have := (rank_ltL b).mpr hb; omega
          · by_cases hbi : b = i
            · subst hbi; rw [rank_i]; exact haR
            · rw [rank_R a ha hai, rank_R b hb hbi]
              have := cnt_mono b a ((memR b).mpr ⟨hb, hbi⟩) (prec_desc a b hRT hab)
              omega
    · -- (2) child before ψ when ⌊u ψ⌋ = 0
      intro ψ hψ hfl
      rw [hlt]
      have hAc := hchild ψ hψ
      have hcne := hne_of_A ψ _ hAc
      by_cases hψL : ψ ∈ L
      · have h := hδ0.2.1 ψ hψ hfl
        have hc : child A ψ ∈ L := (hmem _).mpr (lt_trans h ((hmem ψ).mp hψL))
        rw [rank_L ψ hψL, rank_L _ hc]
        exact h
      · by_cases hψi : ψ = i
        · subst hψi
          have hu1 : u ψ < 1 := (Int.floor_eq_zero_iff.mp hfl).2
          have hc : child A ψ ∈ L := by
            by_contra hc
            exact hT8 ⟨hψ, hu1, hc⟩
          rw [rank_i]
          exact (rank_ltL _).mpr hc
        · have hψR := (rank_gtR ψ).mpr ⟨hψL, hψi⟩
          by_cases hc : child A ψ ∈ L
          · have := (rank_ltL _).mpr hc; omega
          · by_cases hci : child A ψ = i
            · rw [hci, rank_i]; exact hψR
            · rw [rank_R ψ hψL hψi, rank_R _ hc hci]
              have := cnt_mono _ ψ ((memR _).mpr ⟨hc, hci⟩)
                (prec_desc ψ _ (ReflTransGen.single hAc) hcne)
              omega
    · -- (3) no ascendant at ⌊u ψ⌋ before ψ before its child
      intro ψ hψ j hjψ hu ⟨h1, h2⟩
      rw [hlt] at h1 h2
      have hAc := hchild ψ hψ
      have hcne := hne_of_A ψ _ hAc
      by_cases hψL : ψ ∈ L
      · have hψpos := (hmem ψ).mp hψL
        rw [rank_L ψ hψL] at h1 h2
        have hjL : j ∈ L := (rank_ltL j).mp (by omega)
        rw [rank_L j hjL] at h1
        apply hδ0.2.2 ψ hψ j hjψ hu
        refine ⟨h1, ?_⟩
        by_cases hc : child A ψ ∈ L
        · rw [rank_L _ hc] at h2; exact h2
        · have := (hmem _).not.mp hc
          show ((δ0.symm ψ : Fin _) : ℕ) < ((δ0.symm (child A ψ) : Fin _) : ℕ)
          omega
      · by_cases hψi : ψ = i
        · subst hψi
          rw [rank_i] at h1 h2
          have hjL : j ∈ L := (rank_ltL j).mp h1
          have hcL : child A ψ ∉ L := ((rank_gtR _).mp h2).1
          exact hT11 ⟨hψ, ⟨j, hjψ, hjL, hu⟩, hcL⟩
        · have hψR := (rank_gtR ψ).mpr ⟨hψL, hψi⟩
          obtain ⟨hc, hci⟩ := (rank_gtR _).mp (lt_trans hψR h2)
          rw [rank_R ψ hψL hψi, rank_R _ hc hci] at h2
          have := cnt_mono _ ψ ((memR _).mpr ⟨hc, hci⟩)
            (prec_desc ψ _ (ReflTransGen.single hAc) hcne)
          omega
    · -- the prefix is L ++ [i]
      have hlen1 : (L ++ [i]).length = ℓ + 1 := by simp [hℓ]
      rw [hlen1]
      apply List.ext_getElem
      · simp only [List.length_append, List.length_singleton, List.length_take, List.length_ofFn]
        omega
      · intro k hk1 hk2
        rw [List.getElem_take, List.getElem_ofFn, eq_comm, Equiv.symm_apply_eq]
        apply Fin.ext
        show k = rank ((L ++ [i])[k])
        have hk : k < ℓ + 1 := by simpa [hℓ] using hk1
        rcases Nat.lt_or_ge k ℓ with hkl | hkl
        · rw [List.getElem_append_left hkl]
          have hmemk : L[k] ∈ L := List.getElem_mem hkl
          rw [rank_L _ hmemk]
          have hget := List.getElem_of_eq hL0 hkl
          simp only [List.getElem_take, List.getElem_ofFn] at hget
          rw [hget, Equiv.symm_apply_apply]
        · have hk' : k = ℓ := by omega
          subst hk'
          rw [List.getElem_append_right (le_refl _)]
          simp [rank_i]
  · -- a valid extension passes the three tests
    rintro ⟨hiL, δ, hδ, hpre⟩
    have hlen' : (L ++ [i]).length = L.length + 1 := by simp
    rw [hlen'] at hpre
    have hL' : L = (List.ofFn δ).take L.length := by
      have h := congrArg (List.take L.length) hpre
      rw [List.take_take, min_eq_left (Nat.le_succ _)] at h
      rw [← h]
      simp
    have hmem : ∀ x, x ∈ L ↔ ((δ.symm x : Fin _) : ℕ) < L.length := by
      intro x
      conv_lhs => rw [hL']
      exact mem_take_ofFn δ L.length x
    have hiPos : ((δ.symm i : Fin _) : ℕ) = L.length := by
      have h := congrArg (fun l : List V => l[L.length]?) hpre
      simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_singleton,
        List.getElem?_take, List.getElem?_ofFn] at h
      simp only [lt_add_one, if_true, hlen, dite_true] at h
      rw [Option.some_inj] at h
      rw [h]
      simp
    refine ⟨hiL, ?_, ?_, ?_⟩
    · rintro ⟨j, hij, hji, hjL, huj⟩
      have h := hδ.1 i j (Ne.symm hji) hij huj.symm
      rw [Fin.lt_def, hiPos] at h
      exact hjL ((hmem j).mpr h)
    · rintro ⟨hψ, hu1, hcL⟩
      have hfl : Int.floor (u i) = 0 := Int.floor_eq_zero_iff.mpr ⟨(hupos i).le, hu1⟩
      have h := hδ.2.1 i hψ hfl
      rw [Fin.lt_def, hiPos] at h
      exact hcL ((hmem _).mpr h)
    · rintro ⟨hψ, ⟨j, hji, hjL, huj⟩, hcL⟩
      apply hδ.2.2 i hψ j hji huj
      constructor
      · rw [Fin.lt_def, hiPos]
        exact (hmem j).mp hjL
      · rw [Fin.lt_def, hiPos]
        have hcne : child A i ≠ i := (hne_of_A i _ (hchild i hψ)).symm
        have h1 : ¬ ((δ.symm (child A i) : Fin _) : ℕ) < L.length := fun h => hcL ((hmem _).mpr h)
        have h2 : ((δ.symm (child A i) : Fin _) : ℕ) ≠ L.length := by
          intro h
          apply hcne
          rw [← hiPos] at h
          exact δ.symm.injective (Fin.ext h)
        omega
