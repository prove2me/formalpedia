-- Prove2me | solution 1 for DeltaEpsNFailureAtBreakpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:24.681498+00:00
-- url     : https://prove2.me/submissions/deedcbbb-381f-4c24-a1af-aabeb03cabb2

import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_MinimizingResolutionStrict
import Definitions.Def_Tablet_BigEdgeWindowPacking
import Definitions.Def_Tablet_DeltaEpsNFailureAtBreakpoints
import Theorems.Thm_BigEdgeWindowPacking
import Theorems.Thm_MinimizingResolutionStrict


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (δ ε : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ)
    (n : ℕ) (hfail : ¬ IsDeltaEpsN γ δ ε n) :
    ∃ (k : ℕ) (s : ℕ → ℝ) (p q : ℕ),
      IsGeodesicResolution γ k s ∧
      ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card = smallPieceCount γ δ ∧
      StrictMonoOn s (Set.Icc 0 k) ∧
      p ≤ k ∧ q ≤ k ∧ s p ≠ s q ∧
      ((Finset.Icc 1 k).filter (fun j =>
          (if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j) ∧ s j - s (j - 1) < δ)).card = n + 1 ∧
      (((Finset.Icc 1 k).filter (fun j =>
          if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)).card : ℝ)
        ≤ 2 * ε⁻¹ + ((n : ℝ) + 1) ∧
      (if p < q then s q - s p else (γ.len - s p) + s q) ≤ 2 * ε⁻¹ * δ := by
-- BODY
  -- Step 0: a resolution of `γ` attaining `smallPieceCount γ δ`, which is then strictly monotone.
  obtain ⟨k0, s0, hres0⟩ := hpg
  have hmem : smallPieceCount γ δ ∈ { c : ℕ | ∃ k : ℕ, ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧
      c = ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card } :=
    Nat.sInf_mem ⟨((Finset.Icc 1 k0).filter (fun j => s0 j - s0 (j - 1) < δ)).card,
      k0, s0, hres0, rfl⟩
  obtain ⟨k, s, hres, hattain⟩ := hmem
  have hmin : ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card
      = smallPieceCount γ δ := hattain.symm
  have hstrict : StrictMonoOn s (Set.Icc 0 k) :=
    MinimizingResolutionStrict γ δ hδ k s hres hmin
  obtain ⟨hmono, hs0, hsk, hedge⟩ := id hres
  have hmono' : ∀ a b : ℕ, a ≤ b → b ≤ k → s a ≤ s b := by
    intro a b hab hbk
    exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hab hbk⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hbk⟩) hab
  have hstrict' : ∀ a b : ℕ, a < b → b ≤ k → s a < s b := by
    intro a b hab hbk
    exact hstrict (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hbk⟩) hab
  -- (F3): a finite set of naturals with at least `m+1` elements has an element `q` with exactly
  -- `m+1` of its elements below or equal to `q`.
  have key : ∀ (m : ℕ) (S : Finset ℕ), m + 1 ≤ S.card →
      ∃ q ∈ S, (S.filter (fun j => j ≤ q)).card = m + 1 := by
    intro m
    induction m with
    | zero =>
      intro S hS
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      refine ⟨S.min' hne, S.min'_mem hne, ?_⟩
      have hset : S.filter (fun j => j ≤ S.min' hne) = {S.min' hne} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hj, hle⟩
          exact le_antisymm hle (Finset.min'_le S j hj)
        · rintro rfl
          exact ⟨S.min'_mem hne, le_rfl⟩
      rw [hset, Finset.card_singleton]
    | succ m ih =>
      intro S hS
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hamem : S.min' hne ∈ S := S.min'_mem hne
      have hcard' : (S.erase (S.min' hne)).card + 1 = S.card :=
        Finset.card_erase_add_one hamem
      obtain ⟨q, hqS', hqcard⟩ := ih (S.erase (S.min' hne)) (by omega)
      have hqS : q ∈ S := Finset.mem_of_mem_erase hqS'
      have haq : S.min' hne ≤ q := Finset.min'_le S q hqS
      refine ⟨q, hqS, ?_⟩
      have hsplit : S.filter (fun j => j ≤ q)
          = insert (S.min' hne) ((S.erase (S.min' hne)).filter (fun j => j ≤ q)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hj, hle⟩
          by_cases h : j = S.min' hne
          · exact Or.inl h
          · exact Or.inr ⟨⟨h, hj⟩, hle⟩
        · rintro (rfl | ⟨⟨_, hj⟩, hle⟩)
          · exact ⟨hamem, haq⟩
          · exact ⟨hj, hle⟩
      rw [hsplit, Finset.card_insert_of_notMem (by simp), hqcard]
  -- Dividing an edge-count bound by `δ`.
  have divide : ∀ F : ℕ, ((F : ℝ) - ((n : ℝ) + 1)) * δ ≤ 2 * ε⁻¹ * δ →
      (F : ℝ) ≤ 2 * ε⁻¹ + ((n : ℝ) + 1) := by
    intro F h
    have h2 : ((F : ℝ) - ((n : ℝ) + 1)) * δ ≤ (2 * ε⁻¹) * δ := by linarith
    have h3 := le_of_mul_le_mul_right h2 hδ
    linarith
  -- The shared core of Case A and Sub-case B1: an interval-closed set `S` of small edges with at
  -- least `n+1` members produces the two breakpoints of an ordinary (non-wrapping) window.
  have common : ∀ S : Finset ℕ,
      (∀ j ∈ S, 1 ≤ j ∧ j ≤ k ∧ s j - s (j - 1) < δ) →
      (∀ j1 ∈ S, ∀ j2 ∈ S, ∀ j, j1 ≤ j → j ≤ j2 → s j - s (j - 1) < δ → j ∈ S) →
      n + 1 ≤ S.card →
      ∃ p q : ℕ, p < q ∧ q ≤ k ∧ p + 1 ∈ S ∧ q ∈ S ∧
        ((Finset.Icc 1 k).filter
          (fun j => (p < j ∧ j ≤ q) ∧ s j - s (j - 1) < δ)).card = n + 1 ∧
        ((((Finset.Icc 1 k).filter (fun j => p < j ∧ j ≤ q)).card : ℝ) - ((n : ℝ) + 1)) * δ
          ≤ s q - s p := by
    intro S hSmem hSclosed hScard
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have haS : S.min' hne ∈ S := S.min'_mem hne
    obtain ⟨ha1, hak, hasm⟩ := hSmem _ haS
    obtain ⟨q, hqS, hqcard⟩ := key n S hScard
    obtain ⟨hq1, hqk, hqsm⟩ := hSmem _ hqS
    have haq : S.min' hne ≤ q := Finset.min'_le S q hqS
    obtain ⟨p, hp⟩ : ∃ p : ℕ, p + 1 = S.min' hne := ⟨S.min' hne - 1, by omega⟩
    have hpq : p < q := by omega
    have hpk : p ≤ k := by omega
    have hexact : ((Finset.Icc 1 k).filter
        (fun j => (p < j ∧ j ≤ q) ∧ s j - s (j - 1) < δ)).card = n + 1 := by
      have hset : (Finset.Icc 1 k).filter (fun j => (p < j ∧ j ≤ q) ∧ s j - s (j - 1) < δ)
          = S.filter (fun j => j ≤ q) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hj1, hjk⟩, ⟨hpj, hjq⟩, hjsm⟩
          exact ⟨hSclosed _ haS q hqS j (by omega) hjq hjsm, hjq⟩
        · rintro ⟨hjS, hjq⟩
          obtain ⟨hj1, hjk, hjsm⟩ := hSmem j hjS
          have hle := Finset.min'_le S j hjS
          exact ⟨⟨hj1, hjk⟩, ⟨by omega, hjq⟩, hjsm⟩
      rw [hset, hqcard]
    refine ⟨p, q, hpq, hqk, by rw [hp]; exact haS, hqS, hexact, ?_⟩
    have hsmalleq : ((Finset.Icc 1 k).filter (fun j => p < j ∧ j ≤ q)).filter
          (fun j => s j - s (j - 1) < δ)
        = (Finset.Icc 1 k).filter (fun j => (p < j ∧ j ≤ q) ∧ s j - s (j - 1) < δ) :=
      Finset.filter_filter _ _ _
    have hsplit : (((Finset.Icc 1 k).filter (fun j => p < j ∧ j ≤ q)).filter
          (fun j => s j - s (j - 1) < δ)).card
        + (((Finset.Icc 1 k).filter (fun j => p < j ∧ j ≤ q)).filter
          (fun j => ¬ (s j - s (j - 1) < δ))).card
        = ((Finset.Icc 1 k).filter (fun j => p < j ∧ j ≤ q)).card :=
      Finset.card_filter_add_card_filter_not (p := fun j => s j - s (j - 1) < δ)
    rw [hsmalleq, hexact] at hsplit
    have hbigsub : ((Finset.Icc 1 k).filter (fun j => p < j ∧ j ≤ q)).filter
          (fun j => ¬ (s j - s (j - 1) < δ))
        ⊆ (Finset.Icc 1 k).filter
          (fun j => s p ≤ s (j - 1) ∧ s j ≤ s q ∧ δ ≤ s j - s (j - 1)) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc, not_lt] at hj ⊢
      obtain ⟨⟨⟨hj1, hjk⟩, hpj, hjq⟩, hjbig⟩ := hj
      exact ⟨⟨hj1, hjk⟩, hmono' p (j - 1) (by omega) (by omega), hmono' j q hjq hqk, hjbig⟩
    have hpack := BigEdgeWindowPacking k s δ (s p) (s q) hδ hmono (hmono' p q (by omega) hqk)
    have hcardle : ((((Finset.Icc 1 k).filter (fun j => p < j ∧ j ≤ q)).filter
        (fun j => ¬ (s j - s (j - 1) < δ))).card : ℝ)
      ≤ (((Finset.Icc 1 k).filter
          (fun j => s p ≤ s (j - 1) ∧ s j ≤ s q ∧ δ ≤ s j - s (j - 1))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hbigsub
    have hFB : (((Finset.Icc 1 k).filter (fun j => p < j ∧ j ≤ q)).card : ℝ)
        = ((n : ℝ) + 1) + ((((Finset.Icc 1 k).filter (fun j => p < j ∧ j ≤ q)).filter
          (fun j => ¬ (s j - s (j - 1) < δ))).card : ℝ) := by
      rw [← hsplit]; push_cast; ring
    rw [hFB]
    have hmul := mul_le_mul_of_nonneg_right hcardle hδ.le
    linarith [hpack]
  -- Extract the two breakpoints, then assemble the conclusion.
  obtain ⟨p, q, hpk, hqk, hsne, hexact, htotal, harc⟩ :
      ∃ p q : ℕ, p ≤ k ∧ q ≤ k ∧ s p ≠ s q ∧
        ((Finset.Icc 1 k).filter (fun j =>
            (if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)
              ∧ s j - s (j - 1) < δ)).card = n + 1 ∧
        (((Finset.Icc 1 k).filter (fun j =>
            if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)).card : ℝ)
          ≤ 2 * ε⁻¹ + ((n : ℝ) + 1) ∧
        (if p < q then s q - s p else (γ.len - s p) + s q) ≤ 2 * ε⁻¹ * δ := by
    have hkey : ¬ ((∀ t t' : ℝ, 0 ≤ t → t ≤ t' → t' ≤ γ.len → t' - t ≤ 2 * ε⁻¹ * δ →
        ((Finset.Icc 1 k).filter
          (fun j => t ≤ s (j - 1) ∧ s j ≤ t' ∧ s j - s (j - 1) < δ)).card ≤ n) ∧
      (IsClosedCurve γ → ∀ t t' : ℝ, 0 ≤ t' → t' < t → t ≤ γ.len →
        (γ.len - t) + t' ≤ 2 * ε⁻¹ * δ →
        ((Finset.Icc 1 k).filter
          (fun j => (t ≤ s (j - 1) ∨ s j ≤ t') ∧ s j - s (j - 1) < δ)).card ≤ n)) := by
      intro h
      exact hfail ⟨k, s, hres, h.1, h.2⟩
    rcases not_and_or.mp hkey with hc1 | hc2
    · -- Case A: the non-wrapping clause fails.
      push_neg at hc1
      obtain ⟨t, t', ht0, htt', ht'len, hwin, hcount⟩ := hc1
      obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = (Finset.Icc 1 k).filter
        (fun j => t ≤ s (j - 1) ∧ s j ≤ t' ∧ s j - s (j - 1) < δ) := ⟨_, rfl⟩
      rw [← hS] at hcount
      have hSmem : ∀ j ∈ S, 1 ≤ j ∧ j ≤ k ∧ s j - s (j - 1) < δ := by
        intro j hj
        rw [hS] at hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        exact ⟨hj.1.1, hj.1.2, hj.2.2.2⟩
      have hSclosed : ∀ j1 ∈ S, ∀ j2 ∈ S, ∀ j, j1 ≤ j → j ≤ j2 →
          s j - s (j - 1) < δ → j ∈ S := by
        intro j1 hj1 j2 hj2 j hle1 hle2 hsm
        rw [hS] at hj1 hj2 ⊢
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj1 hj2 ⊢
        obtain ⟨⟨h11, h1k⟩, h1t, h1t', h1sm⟩ := hj1
        obtain ⟨⟨h21, h2k⟩, h2t, h2t', h2sm⟩ := hj2
        refine ⟨⟨by omega, by omega⟩, ?_, ?_, hsm⟩
        · exact le_trans h1t (hmono' (j1 - 1) (j - 1) (by omega) (by omega))
        · exact le_trans (hmono' j j2 hle2 h2k) h2t'
      obtain ⟨p, q, hpq, hqk, hpS, hqS, hexact, hbig⟩ := common S hSmem hSclosed (by omega)
      rw [hS] at hpS hqS
      have htp : t ≤ s p := by
        have h := (Finset.mem_filter.mp hpS).2.1
        simpa using h
      have hqt' : s q ≤ t' := (Finset.mem_filter.mp hqS).2.2.1
      have harc : s q - s p ≤ 2 * ε⁻¹ * δ := by linarith
      refine ⟨p, q, by omega, hqk, (hstrict' p q hpq hqk).ne, ?_, ?_, ?_⟩
      · simp only [if_pos hpq]
        exact hexact
      · simp only [if_pos hpq]
        exact divide _ (le_trans hbig harc)
      · rw [if_pos hpq]
        exact harc
    · -- Case B: the wrapping clause fails.
      push_neg at hc2
      obtain ⟨-, t, t', ht'0, ht't, htlen, hwin, hcount⟩ := hc2
      obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = (Finset.Icc 1 k).filter
        (fun j => t ≤ s (j - 1) ∧ s j - s (j - 1) < δ) := ⟨_, rfl⟩
      obtain ⟨H, hH⟩ : ∃ H : Finset ℕ, H = (Finset.Icc 1 k).filter
        (fun j => s j ≤ t' ∧ s j - s (j - 1) < δ) := ⟨_, rfl⟩
      have hUsub : (Finset.Icc 1 k).filter
          (fun j => (t ≤ s (j - 1) ∨ s j ≤ t') ∧ s j - s (j - 1) < δ) ⊆ T ∪ H := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨hjk, hor, hsm⟩ := hj
        rcases hor with h | h
        · refine Finset.mem_union_left _ ?_
          rw [hT]
          simp only [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨hjk, h, hsm⟩
        · refine Finset.mem_union_right _ ?_
          rw [hH]
          simp only [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨hjk, h, hsm⟩
      have hTH : n + 1 ≤ T.card + H.card := by
        have h1 := Finset.card_le_card hUsub
        have h2 := Finset.card_union_le T H
        omega
      have hTfull : ∀ j ∈ T, (1 ≤ j ∧ j ≤ k) ∧ t ≤ s (j - 1) ∧ s j - s (j - 1) < δ := by
        intro j hj
        rw [hT] at hj
        simpa only [Finset.mem_filter, Finset.mem_Icc] using hj
      by_cases hTbig : n + 1 ≤ T.card
      · -- Sub-case B1: the small tail edges already number `n+1`.
        have hTmem : ∀ j ∈ T, 1 ≤ j ∧ j ≤ k ∧ s j - s (j - 1) < δ := by
          intro j hj
          rw [hT] at hj
          simp only [Finset.mem_filter, Finset.mem_Icc] at hj
          exact ⟨hj.1.1, hj.1.2, hj.2.2⟩
        have hTclosed : ∀ j1 ∈ T, ∀ j2 ∈ T, ∀ j, j1 ≤ j → j ≤ j2 →
            s j - s (j - 1) < δ → j ∈ T := by
          intro j1 hj1 j2 hj2 j hle1 hle2 hsm
          rw [hT] at hj1 hj2 ⊢
          simp only [Finset.mem_filter, Finset.mem_Icc] at hj1 hj2 ⊢
          obtain ⟨⟨h11, h1k⟩, h1t, h1sm⟩ := hj1
          obtain ⟨⟨h21, h2k⟩, h2t, h2sm⟩ := hj2
          exact ⟨⟨by omega, by omega⟩,
            le_trans h1t (hmono' (j1 - 1) (j - 1) (by omega) (by omega)), hsm⟩
        obtain ⟨p, q, hpq, hqk, hpT, hqT, hexact, hbig⟩ := common T hTmem hTclosed hTbig
        rw [hT] at hpT
        have htp : t ≤ s p := by
          have h := (Finset.mem_filter.mp hpT).2.1
          simpa using h
        have hqlen : s q ≤ γ.len := by
          rw [← hsk]
          exact hmono' q k hqk le_rfl
        have harc : s q - s p ≤ 2 * ε⁻¹ * δ := by linarith
        refine ⟨p, q, by omega, hqk, (hstrict' p q hpq hqk).ne, ?_, ?_, ?_⟩
        · simp only [if_pos hpq]
          exact hexact
        · simp only [if_pos hpq]
          exact divide _ (le_trans hbig harc)
        · rw [if_pos hpq]
          exact harc
      · -- Sub-case B2: the violating window wraps around the basepoint.
        push_neg at hTbig
        obtain ⟨q, hqH, hqcard⟩ := key (n - T.card) H (by omega)
        have hqH' := hqH
        rw [hH] at hqH'
        simp only [Finset.mem_filter, Finset.mem_Icc] at hqH'
        obtain ⟨⟨hq1, hqk⟩, hqt', hqsm⟩ := hqH'
        obtain ⟨p, hpk, hqp, hlen, hP2⟩ : ∃ p : ℕ, p ≤ k ∧ q < p ∧ γ.len - s p ≤ γ.len - t ∧
            ((Finset.Icc 1 k).filter (fun j => p < j ∧ s j - s (j - 1) < δ)) = T := by
          by_cases hTne : T.Nonempty
          · have haT : T.min' hTne ∈ T := T.min'_mem hTne
            obtain ⟨⟨ha1, hak⟩, hat, hasm⟩ := hTfull _ haT
            obtain ⟨p, hp⟩ : ∃ p : ℕ, p + 1 = T.min' hTne := ⟨T.min' hTne - 1, by omega⟩
            have hpk : p ≤ k := by omega
            have htp : t ≤ s p := by
              have hpe : p = T.min' hTne - 1 := by omega
              rw [hpe]
              exact hat
            have hqp : q < p := by
              by_contra hcon
              push_neg at hcon
              have hle := hmono' p q hcon hqk
              linarith
            refine ⟨p, hpk, hqp, by linarith, ?_⟩
            ext j
            rw [hT]
            simp only [Finset.mem_filter, Finset.mem_Icc]
            constructor
            · rintro ⟨⟨hj1, hjk⟩, hpj, hjsm⟩
              exact ⟨⟨hj1, hjk⟩, le_trans htp (hmono' p (j - 1) (by omega) (by omega)), hjsm⟩
            · rintro ⟨⟨hj1, hjk⟩, hjt, hjsm⟩
              have hjT : j ∈ T := by
                rw [hT]
                simp only [Finset.mem_filter, Finset.mem_Icc]
                exact ⟨⟨hj1, hjk⟩, hjt, hjsm⟩
              have hle : T.min' hTne ≤ j := Finset.min'_le T j hjT
              exact ⟨⟨hj1, hjk⟩, by omega, hjsm⟩
          · have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
            have hqk' : q < k := by
              rcases lt_or_eq_of_le hqk with h | h
              · exact h
              · exfalso
                rw [h, hsk] at hqt'
                linarith
            refine ⟨k, le_rfl, hqk', by rw [hsk]; linarith, ?_⟩
            rw [hTe]
            refine Finset.filter_eq_empty_iff.mpr ?_
            intro j hj
            simp only [Finset.mem_Icc] at hj
            rintro ⟨h1, -⟩
            omega
        have hnotpq : ¬ (p < q) := by omega
        have hP1 : (Finset.Icc 1 k).filter (fun j => j ≤ q ∧ s j - s (j - 1) < δ)
            = H.filter (fun j => j ≤ q) := by
          ext j
          rw [hH]
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨hj1, hjk⟩, hjq, hjsm⟩
            exact ⟨⟨⟨hj1, hjk⟩, le_trans (hmono' j q hjq hqk) hqt', hjsm⟩, hjq⟩
          · rintro ⟨⟨⟨hj1, hjk⟩, hjt', hjsm⟩, hjq⟩
            exact ⟨⟨hj1, hjk⟩, hjq, hjsm⟩
        have hdisjS : Disjoint
            ((Finset.Icc 1 k).filter (fun j => j ≤ q ∧ s j - s (j - 1) < δ))
            ((Finset.Icc 1 k).filter (fun j => p < j ∧ s j - s (j - 1) < δ)) := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          have h1 : j ≤ q := (Finset.mem_filter.mp hj1).2.1
          have h2 : p < j := (Finset.mem_filter.mp hj2).2.1
          omega
        have hunionS : (Finset.Icc 1 k).filter
            (fun j => (j ≤ q ∨ p < j) ∧ s j - s (j - 1) < δ)
            = ((Finset.Icc 1 k).filter (fun j => j ≤ q ∧ s j - s (j - 1) < δ))
              ∪ ((Finset.Icc 1 k).filter (fun j => p < j ∧ s j - s (j - 1) < δ)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_union]
          tauto
        have hsum : ((Finset.Icc 1 k).filter (fun j => j ≤ q ∧ s j - s (j - 1) < δ)).card
            + ((Finset.Icc 1 k).filter (fun j => p < j ∧ s j - s (j - 1) < δ)).card = n + 1 := by
          rw [hP1, hqcard, hP2]
          omega
        have hexact : ((Finset.Icc 1 k).filter
            (fun j => (j ≤ q ∨ p < j) ∧ s j - s (j - 1) < δ)).card = n + 1 := by
          rw [hunionS, Finset.card_union_of_disjoint hdisjS]
          exact hsum
        have hdisjF : Disjoint ((Finset.Icc 1 k).filter (fun j => j ≤ q))
            ((Finset.Icc 1 k).filter (fun j => p < j)) := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          have h1 : j ≤ q := (Finset.mem_filter.mp hj1).2
          have h2 : p < j := (Finset.mem_filter.mp hj2).2
          omega
        have hunionF : (Finset.Icc 1 k).filter (fun j => j ≤ q ∨ p < j)
            = ((Finset.Icc 1 k).filter (fun j => j ≤ q))
              ∪ ((Finset.Icc 1 k).filter (fun j => p < j)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_union]
          tauto
        have hff1 : ((Finset.Icc 1 k).filter (fun j => j ≤ q)).filter
              (fun j => s j - s (j - 1) < δ)
            = (Finset.Icc 1 k).filter (fun j => j ≤ q ∧ s j - s (j - 1) < δ) :=
          Finset.filter_filter _ _ _
        have hff2 : ((Finset.Icc 1 k).filter (fun j => p < j)).filter
              (fun j => s j - s (j - 1) < δ)
            = (Finset.Icc 1 k).filter (fun j => p < j ∧ s j - s (j - 1) < δ) :=
          Finset.filter_filter _ _ _
        have hs1 : (((Finset.Icc 1 k).filter (fun j => j ≤ q)).filter
              (fun j => s j - s (j - 1) < δ)).card
            + (((Finset.Icc 1 k).filter (fun j => j ≤ q)).filter
              (fun j => ¬ (s j - s (j - 1) < δ))).card
            = ((Finset.Icc 1 k).filter (fun j => j ≤ q)).card :=
          Finset.card_filter_add_card_filter_not (p := fun j => s j - s (j - 1) < δ)
        have hs2 : (((Finset.Icc 1 k).filter (fun j => p < j)).filter
              (fun j => s j - s (j - 1) < δ)).card
            + (((Finset.Icc 1 k).filter (fun j => p < j)).filter
              (fun j => ¬ (s j - s (j - 1) < δ))).card
            = ((Finset.Icc 1 k).filter (fun j => p < j)).card :=
          Finset.card_filter_add_card_filter_not (p := fun j => s j - s (j - 1) < δ)
        rw [hff1] at hs1
        rw [hff2] at hs2
        have hbigsub1 : ((Finset.Icc 1 k).filter (fun j => j ≤ q)).filter
              (fun j => ¬ (s j - s (j - 1) < δ))
            ⊆ (Finset.Icc 1 k).filter
              (fun j => s 0 ≤ s (j - 1) ∧ s j ≤ s q ∧ δ ≤ s j - s (j - 1)) := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_Icc, not_lt] at hj ⊢
          obtain ⟨⟨⟨hj1, hjk⟩, hjq⟩, hjbig⟩ := hj
          exact ⟨⟨hj1, hjk⟩, hmono' 0 (j - 1) (Nat.zero_le _) (by omega),
            hmono' j q hjq hqk, hjbig⟩
        have hbigsub2 : ((Finset.Icc 1 k).filter (fun j => p < j)).filter
              (fun j => ¬ (s j - s (j - 1) < δ))
            ⊆ (Finset.Icc 1 k).filter
              (fun j => s p ≤ s (j - 1) ∧ s j ≤ s k ∧ δ ≤ s j - s (j - 1)) := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_Icc, not_lt] at hj ⊢
          obtain ⟨⟨⟨hj1, hjk⟩, hpj⟩, hjbig⟩ := hj
          exact ⟨⟨hj1, hjk⟩, hmono' p (j - 1) (by omega) (by omega),
            hmono' j k hjk le_rfl, hjbig⟩
        have hpack1 := BigEdgeWindowPacking k s δ (s 0) (s q) hδ hmono
          (hmono' 0 q (Nat.zero_le _) hqk)
        have hpack2 := BigEdgeWindowPacking k s δ (s p) (s k) hδ hmono (hmono' p k hpk le_rfl)
        have hc1' : ((((Finset.Icc 1 k).filter (fun j => j ≤ q)).filter
            (fun j => ¬ (s j - s (j - 1) < δ))).card : ℝ)
          ≤ (((Finset.Icc 1 k).filter
              (fun j => s 0 ≤ s (j - 1) ∧ s j ≤ s q ∧ δ ≤ s j - s (j - 1))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hbigsub1
        have hc2' : ((((Finset.Icc 1 k).filter (fun j => p < j)).filter
            (fun j => ¬ (s j - s (j - 1) < δ))).card : ℝ)
          ≤ (((Finset.Icc 1 k).filter
              (fun j => s p ≤ s (j - 1) ∧ s j ≤ s k ∧ δ ≤ s j - s (j - 1))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hbigsub2
        have hm1 := mul_le_mul_of_nonneg_right hc1' hδ.le
        have hm2 := mul_le_mul_of_nonneg_right hc2' hδ.le
        have harc : (γ.len - s p) + s q ≤ 2 * ε⁻¹ * δ := by linarith
        have hFcard : ((Finset.Icc 1 k).filter (fun j => j ≤ q ∨ p < j)).card
            = (n + 1) + (((((Finset.Icc 1 k).filter (fun j => j ≤ q)).filter
                (fun j => ¬ (s j - s (j - 1) < δ))).card)
              + ((((Finset.Icc 1 k).filter (fun j => p < j)).filter
                (fun j => ¬ (s j - s (j - 1) < δ))).card)) := by
          rw [hunionF, Finset.card_union_of_disjoint hdisjF]
          omega
        refine ⟨p, q, hpk, hqk, (hstrict' q p hqp hpk).ne', ?_, ?_, ?_⟩
        · simp only [if_neg hnotpq]
          exact hexact
        · simp only [if_neg hnotpq]
          refine divide _ ?_
          rw [hFcard]
          push_cast
          linarith [hpack1, hpack2, hm1, hm2, harc]
        · rw [if_neg hnotpq]
          exact harc
  exact ⟨k, s, p, q, hres, hmin, hstrict, hpk, hqk, hsne, hexact, htotal, harc⟩
