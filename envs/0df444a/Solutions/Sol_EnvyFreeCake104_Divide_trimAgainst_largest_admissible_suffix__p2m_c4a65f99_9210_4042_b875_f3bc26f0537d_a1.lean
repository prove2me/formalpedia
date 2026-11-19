-- Prove2me | solution 1 for EnvyFreeCake104.Divide.trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T18:58:46.773261+00:00
-- url     : https://prove2.me/submissions/3257bafa-5ce1-4711-baa1-f8e455d3da79

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Theorems.Thm_EnvyFreeCake104_Divide_ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

private theorem valuation_order__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 (v : Valuation) :
    (∀ S : Set ℝ, 0 ≤ v.value S) ∧
    (∀ S T : Set ℝ, S ⊆ T → v.value S ≤ v.value T) := by
  have hn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)] v.density :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun x hx ↦ v.nonneg x hx)
  have hnS (S : Set ℝ) :
      0 ≤ᵐ[MeasureTheory.volume.restrict (S ∩ Set.Icc (0 : ℝ) 1)] v.density :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hn
  constructor
  · intro S
    exact MeasureTheory.integral_nonneg_of_ae (hnS S)
  · intro S T hST
    exact MeasureTheory.setIntegral_mono_set
      (v.integrable.mono_set Set.inter_subset_right) (hnS T)
      (Filter.Eventually.of_forall fun x hx ↦ ⟨hST hx.1, hx.2⟩)

private theorem run_bind_of_success__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
    {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (p : Prog ι α) (f : α → Prog ι β) (tr₀ tr₁ : List (Event ι)) (x : α)
    (h : Prog.run V o p tr₀ = some (x, tr₁)) :
    Prog.run V o (Prog.bind p f) tr₀ = Prog.run V o (f x) tr₁ := by
  induction p generalizing tr₀ with
  | ret y =>
      simp only [Prog.run, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | fail => simp only [Prog.run, reduceCtorEq] at h
  | eval i a b k ih => exact ih (evalAnswer V i a b) _ h
  | cut i a w k ih => exact ih (cutAnswer V i a w) _ h
  | choose m k ih => exact ih (o tr₀ m) _ h

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hcut : ∀ (i : ι) (hi : i ∈ N) (Q : Piece) (hQ : Q.WF)
    (s : Rec ι) (hs : s.Valid V N) (hQs : s.Aligned Q)
    (w : ℝ) (hw : 0 ≤ w) (hwQ : w ≤ (V i).value Q.toSet)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
    ∃ (p : Pos) (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((prefixCut N i Q w).run s) tr₀ = some ((p, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧
      (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
      s'.Aligned (prefixList Q p) ∧ s'.Aligned (suffixList Q p) ∧
      (V i).value (prefixList Q p).toSet = w ∧
      (V i).value (suffixList Q p).toSet = (V i).value Q.toSet - w ∧
      IsSuffix (suffixList Q p).toSet Q ∧
      ∀ S : Set ℝ, IsSuffix S Q →
        (V i).value S ≤ (V i).value Q.toSet - w →
        S ⊆ (suffixList Q p).toSet)
    (Y : ι → Piece) (hY : ∀ i ∈ N, (Y i).WF)
    (earlier : List ι) (hearlier : ∀ i ∈ earlier, i ∈ N)
    (Q removed : Piece) (hQ : Q.WF)
    (s : Rec ι) (hs : s.Valid V N)
    (hYs : ∀ i ∈ N, s.Aligned (Y i)) (hQs : s.Aligned Q)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    ∃ (B rem : Piece) (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((trimAgainst N Y earlier Q removed).run s) tr₀ =
        some (((B, rem), s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ B.WF ∧ s'.Aligned B ∧
      IsSuffix B.toSet Q ∧
      (∀ i ∈ earlier, (V i).value B.toSet ≤ (V i).value (Y i).toSet) ∧
      ∀ S : Set ℝ, IsSuffix S Q →
        (∀ i ∈ earlier, (V i).value S ≤ (V i).value (Y i).toSet) →
        S ⊆ B.toSet ∧ ∀ i ∈ N, (V i).value S ≤ (V i).value B.toSet := by
  classical
  have hmono (i : ι) (S T : Set ℝ) (hST : S ⊆ T) :
      (V i).value S ≤ (V i).value T :=
    (valuation_order__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 (V i)).2 S T hST
  have hnonneg (i : ι) (S : Set ℝ) : 0 ≤ (V i).value S :=
    (valuation_order__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 (V i)).1 S
  revert hearlier Q removed hQ s hs hYs hQs tr₀
  induction earlier with
  | nil =>
      intro hearlier Q removed hQ s hs hYs hQs tr₀
      obtain ⟨hself, hsub, hnest⟩ :=
        ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 Q hQ
      refine ⟨Q, removed, s, tr₀, ?_, hs, Set.Subset.rfl, hQ, hQs, hself, ?_, ?_⟩
      · rfl
      · intro i hi
        simp only [List.not_mem_nil] at hi
      · intro S hS hbound
        exact ⟨hsub S hS, fun i hi ↦ hmono i S Q.toSet (hsub S hS)⟩
  | cons a rest ih =>
      intro hearlier Q removed hQ s hs hYs hQs tr₀
      have ha : a ∈ N := hearlier a (List.mem_cons_self)
      have hrest : ∀ i ∈ rest, i ∈ N :=
        fun i hi ↦ hearlier i (List.mem_cons_of_mem a hi)
      have hvalQ : s.pieceVal a Q = (V a).value Q.toSet :=
        recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 V N s hs a ha Q hQ hQs
      have hvalY : s.pieceVal a (Y a) = (V a).value (Y a).toSet :=
        recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 V N s hs a ha (Y a) (hY a ha) (hYs a ha)
      by_cases hd : 0 < s.pieceVal a Q - s.pieceVal a (Y a)
      · have hw : 0 ≤ s.pieceVal a Q - s.pieceVal a (Y a) := le_of_lt hd
        have hwQ : s.pieceVal a Q - s.pieceVal a (Y a) ≤ (V a).value Q.toSet := by
          rw [hvalQ, hvalY]
          linarith [hnonneg a (Y a).toSet]
        obtain ⟨p, s₁, tr₁, hrun₁, hs₁, hpts₁, hpwf, hqwf,
            hpal, hqal, hpval, hqval, hqsuf, hmax⟩ :=
          hcut a ha Q hQ s hs hQs _ hw hwQ o tr₀
        have hYs₁ : ∀ i ∈ N, s₁.Aligned (Y i) := by
          intro i hi I hI
          exact ⟨hpts₁ (hYs i hi I hI).1, hpts₁ (hYs i hi I hI).2⟩
        obtain ⟨B, rem, s₂, tr₂, hrun₂, hs₂, hpts₂, hBwf, hBal, hBsuf,
            hbounds, hlargest⟩ :=
          ih hrest (suffixList Q p) (removed ++ prefixList Q p) hqwf s₁ hs₁ hYs₁ hqal tr₁
        obtain ⟨hself, hsub, hnest⟩ :=
          ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 Q hQ
        obtain ⟨hlift, hrestrict⟩ := hnest p hpwf hqwf
        have hBsub : B.toSet ⊆ (suffixList Q p).toSet :=
          (ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 (suffixList Q p) hqwf).2.1 B.toSet hBsuf
        refine ⟨B, rem, s₂, tr₂, ?_, hs₂, hpts₁.trans hpts₂, hBwf, hBal,
          hlift B.toSet hBsuf, ?_, ?_⟩
        · change Prog.run V o
            ((if 0 < s.pieceVal a Q - s.pieceVal a (Y a) then
                (do
                  let p ← prefixCut N a Q (s.pieceVal a Q - s.pieceVal a (Y a))
                  trimAgainst N Y rest (suffixList Q p) (removed ++ prefixList Q p))
              else trimAgainst N Y rest Q removed).run s) tr₀ = _
          rw [if_pos hd]
          exact (run_bind_of_success__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 V o _ _ tr₀ tr₁ (p, s₁) hrun₁).trans hrun₂
        · intro i hi
          rcases List.mem_cons.mp hi with hia | hi
          · subst i
            have hle := hmono a B.toSet (suffixList Q p).toSet hBsub
            rw [hqval, hvalQ, hvalY] at hle
            linarith
          · exact hbounds i hi
        · intro S hS hbound
          have hle : (V a).value S ≤
              (V a).value Q.toSet - (s.pieceVal a Q - s.pieceVal a (Y a)) := by
            have hb := hbound a (List.mem_cons_self)
            rw [hvalQ, hvalY]
            linarith
          have hSQ := hmax S hS hle
          exact hlargest S (hrestrict S hS hSQ)
            (fun i hi ↦ hbound i (List.mem_cons_of_mem a hi))
      · obtain ⟨B, rem, s₂, tr₂, hrun₂, hs₂, hpts₂, hBwf, hBal, hBsuf,
            hbounds, hlargest⟩ :=
          ih hrest Q removed hQ s hs hYs hQs tr₀
        have hBsub : B.toSet ⊆ Q.toSet :=
          (ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 Q hQ).2.1 B.toSet hBsuf
        refine ⟨B, rem, s₂, tr₂, ?_, hs₂, hpts₂, hBwf, hBal, hBsuf, ?_, ?_⟩
        · change Prog.run V o
            ((if 0 < s.pieceVal a Q - s.pieceVal a (Y a) then
                (do
                  let p ← prefixCut N a Q (s.pieceVal a Q - s.pieceVal a (Y a))
                  trimAgainst N Y rest (suffixList Q p) (removed ++ prefixList Q p))
              else trimAgainst N Y rest Q removed).run s) tr₀ = _
          rw [if_neg hd]
          exact hrun₂
        · intro i hi
          rcases List.mem_cons.mp hi with hia | hi
          · subst i
            have hle := hmono a B.toSet Q.toSet hBsub
            rw [hvalQ, hvalY] at hd
            linarith
          · exact hbounds i hi
        · intro S hS hbound
          exact hlargest S hS (fun i hi ↦ hbound i (List.mem_cons_of_mem a hi))
