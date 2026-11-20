-- Prove2me | solution 1 for EnvyFreeCake104.Divide.equalCuts_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T07:17:57.45903+00:00
-- url     : https://prove2.me/submissions/7c4413d3-ba46-47bd-8fc4-3a3df943cd38

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

private theorem run_bind_eq__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
    {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (a : Prog ι α) (f : α → Prog ι β) (tr₀ : List (Event ι)) :
    Prog.run V o (Prog.bind a f) tr₀ =
      match Prog.run V o a tr₀ with
      | none => none
      | some (x, tr) => Prog.run V o (f x) tr := by
  induction a generalizing tr₀ with
  | ret x => rfl
  | fail => rfl
  | eval i a b k ih => exact ih (evalAnswer V i a b) _
  | cut i x w k ih => exact ih (cutAnswer V i x w) _
  | choose m k ih => exact ih (o tr₀ m) _

private theorem value_nonneg__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
    (v : Valuation) (S : Set ℝ) : 0 ≤ v.value S := by
  unfold Valuation.value
  apply MeasureTheory.integral_nonneg_of_ae
  exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
    ((MeasureTheory.ae_restrict_mem measurableSet_Icc).mono
      (fun x hx ↦ v.nonneg x hx))

/-- The induction keeps both the transcript prefix and the recorded endpoints. -/
private theorem equalCuts_invariant__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (c : ι) (hc : c ∈ N) (w : ℝ) (hw : 0 ≤ w)
    (o : ChoiceOracle ι) (m : ℕ) :
    ∀ (Q : Piece), Q.WF → ∀ (s : Rec ι), s.Valid V N → s.Aligned Q →
      (V c).value Q.toSet = ((m + 1 : ℕ) : ℝ) * w →
      ∀ (tr₀ : List (Event ι)),
      ∃ (ps : List Piece) (s₁ : Rec ι) (tr₁ : List (Event ι)),
        Prog.run V o ((equalCuts N c w m Q).run s) tr₀ =
          some ((ps, s₁), tr₁) ∧
        s₁.Valid V N ∧ s.pts ⊆ s₁.pts ∧ ps.length = m + 1 ∧
        (∀ P ∈ ps, P.WF) ∧ (∀ P ∈ ps, s₁.Aligned P) ∧
        ps.Pairwise (fun P R ↦ Disjoint P.toSet R.toSet) ∧
        (⋃ P ∈ ps, P.toSet) = Q.toSet ∧
        (∀ P ∈ ps, (V c).value P.toSet = w) ∧
        queryCount tr₁ ≤ queryCount tr₀ + m * (N.card + 1) := by
  classical
  induction m with
  | zero =>
      intro Q hQ s hs hQs hmass tr₀
      refine ⟨[Q], s, tr₀, ?_, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · exact fun _ hx ↦ hx
      · simp
      · simpa only [List.mem_singleton, forall_eq] using hQ
      · simpa only [List.mem_singleton, forall_eq] using hQs
      · simp
      · ext x
        simp
      · simpa only [List.mem_singleton, forall_eq, Nat.cast_one, zero_add, one_mul]
          using hmass
      · simp
  | succ m ih =>
      intro Q hQ s hs hQs hmass tr₀
      have hmass' : (V c).value Q.toSet = ((m : ℝ) + 2) * w := by
        calc
          (V c).value Q.toSet = ((m + 1 + 1 : ℕ) : ℝ) * w := hmass
          _ = ((m : ℝ) + 2) * w := by push_cast; ring
      have hwQ : w ≤ (V c).value Q.toSet := by
        nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ)) hw]
      obtain ⟨p, s₀, trA, hrA, hs₀, hptsA, hP, hR, hAP, hAR, hvP, hvR, _⟩ :=
        prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
          V N c hc Q hQ s hs hQs w hw hwQ o tr₀
      obtain ⟨q, t, trB, hrB, _, _, hpos, _⟩ :=
        prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
          V N c hc Q hQ s hs hQs w hw hwQ o tr₀
      have he : ((q, t), trB) = ((p, s₀), trA) :=
        Option.some.inj (hrB.symm.trans hrA)
      have hqp : q = p := congrArg (fun z ↦ z.1.1) he
      subst q
      have hgeom :
          Disjoint (prefixList Q p).toSet (suffixList Q p).toSet ∧
          (prefixList Q p).toSet ∪ (suffixList Q p).toSet = Q.toSet := by
        rcases hpos with hnil | hp
        · subst Q
          simp [prefixList, suffixList, Piece.toSet]
        · exact
            (cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
              Q hQ p hp).2.2
      have hmassR :
          (V c).value (suffixList Q p).toSet = ((m + 1 : ℕ) : ℝ) * w := by
        rw [hvR, hmass']
        push_cast
        ring
      obtain ⟨ps, s₁, tr₁, hrT, hs₁, hptsT, hlen, hWF, hAl, hPair, hUnion,
        hValues, hCount⟩ :=
        ih (suffixList Q p) hR s₀ hs₀ hAR hmassR trA
      have hCountA : queryCount trA ≤ queryCount tr₀ + (N.card + 1) :=
        prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
          V N c Q w s o tr₀ p s₀ trA hrA
      refine ⟨prefixList Q p :: ps, s₁, tr₁, ?_, hs₁, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      · change Prog.run V o
          (Prog.bind ((prefixCut N c Q w).run s)
            (fun z ↦ Prog.bind ((equalCuts N c w m (suffixList Q z.1)).run z.2)
              (fun u ↦ Prog.ret ((prefixList Q z.1 :: u.1), u.2)))) tr₀ = _
        simp only [run_bind_eq__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1,
          hrA, hrT, Prog.run]
      · exact fun x hx ↦ hptsT (hptsA hx)
      · simpa only [List.length_cons] using congrArg Nat.succ hlen
      · intro P hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hP
        · exact hWF P hmem
      · intro P hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · intro I hI
          exact ⟨hptsT (hAP I hI).1, hptsT (hAP I hI).2⟩
        · exact hAl P hmem
      · apply List.pairwise_cons.mpr
        refine ⟨?_, hPair⟩
        intro R hmem
        have hsub : R.toSet ⊆ (suffixList Q p).toSet := by
          intro x hx
          rw [← hUnion]
          exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hmem, hx⟩⟩
        exact Disjoint.mono_right hsub hgeom.1
      · calc
          (⋃ P ∈ prefixList Q p :: ps, P.toSet) =
              (prefixList Q p).toSet ∪ (⋃ P ∈ ps, P.toSet) := by
                ext x
                simp only [Set.mem_iUnion, List.mem_cons, Set.mem_union]
                aesop
          _ = (prefixList Q p).toSet ∪ (suffixList Q p).toSet := by rw [hUnion]
          _ = Q.toSet := hgeom.2
      · intro P hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hvP
        · exact hValues P hmem
      · calc
          queryCount tr₁ ≤ queryCount trA + m * (N.card + 1) := hCount
          _ ≤ (queryCount tr₀ + (N.card + 1)) + m * (N.card + 1) :=
            Nat.add_le_add_right hCountA _
          _ = queryCount tr₀ + (m + 1) * (N.card + 1) := by ring

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (c : ι) (hc : c ∈ N) (m : ℕ) (Q : Piece) (hQ : Q.WF)
    (s : Rec ι) (hs : s.Valid V N) (hQs : s.Aligned Q) (o : ChoiceOracle ι) :
    ∃ (ps : List Piece) (s₁ : Rec ι) (tr₁ : List (Event ι)),
      exec V o (equalCuts N c ((V c).value Q.toSet / ((m + 1 : ℕ) : ℝ)) m Q) s =
        some (ps, s₁, tr₁) ∧
      s₁.Valid V N ∧ ps.length = m + 1 ∧
      (∀ P ∈ ps, P.WF) ∧ (∀ P ∈ ps, s₁.Aligned P) ∧
      ps.Pairwise (fun P R ↦ Disjoint P.toSet R.toSet) ∧
      (⋃ P ∈ ps, P.toSet) = Q.toSet ∧
      (∀ P ∈ ps, (V c).value P.toSet = (V c).value Q.toSet / ((m + 1 : ℕ) : ℝ)) ∧
      queryCount tr₁ ≤ m * (N.card + 1) := by
  have hd : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hw : 0 ≤ (V c).value Q.toSet / ((m + 1 : ℕ) : ℝ) :=
    div_nonneg (value_nonneg__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1 (V c) Q.toSet) hd.le
  have hmass : (V c).value Q.toSet =
      ((m + 1 : ℕ) : ℝ) * ((V c).value Q.toSet / ((m + 1 : ℕ) : ℝ)) := by
    exact (mul_div_cancel₀ _ (ne_of_gt hd)).symm
  obtain ⟨ps, s₁, tr₁, hr, hs₁, _, hlen, hWF, hAl, hPair, hUnion, hValues, hCount⟩ :=
    equalCuts_invariant__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
      V N c hc ((V c).value Q.toSet / ((m + 1 : ℕ) : ℝ)) hw o m
      Q hQ s hs hQs hmass []
  refine ⟨ps, s₁, tr₁, ?_, hs₁, hlen, hWF, hAl, hPair, hUnion, hValues, ?_⟩
  · unfold exec
    rw [hr]
  · simpa only [queryCount, List.countP_nil, zero_add] using hCount

