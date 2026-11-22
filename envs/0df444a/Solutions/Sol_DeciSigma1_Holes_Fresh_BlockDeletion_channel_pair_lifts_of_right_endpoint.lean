-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.channel_pair_lifts_of_right_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:36:49.771782+00:00
-- url     : https://prove2.me/submissions/7a2cb7f0-b151-4361-9859-99d1cd86b710

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_apply_of_inactive
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_terminal
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_le_windowLength
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_label_window
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_junction_not_in_labelWindow
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_tail_window
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_anchor_ne_site
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_contextAnchors_apply
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_delta_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_junction_window
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_runPrefix_apply
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_strictlySeparated
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_upperCutLength_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_StrictlySeparated_ne_right
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_eq_singleton
public import Theorems.Thm_DeciSigma1_Holes_Fresh_greatestPreimage_add_eq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_marker_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_ne_nil
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_occurrences_in_next_marker
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_of_mem_anchors_of_lt_length
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_occ_of_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_prefix_drop_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_retained_of_mem_sites
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_drop_deleteSites
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Readers_Table_pair_mem_channel
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_le
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {i j : Fin k} {a b L d : ℕ} (hL : (m.apply j).length = b + L)
    (hpre : (m.apply j).drop b <+: (m.apply i).drop a) (hd0 : 0 < d) (hdL : d < L)
    (hJ : IsJunction m.deletionLength (m.sites i) (a + d)) (hlt : L < d + m.upperCutLength) :
    (T.runPrefix m.apply i a, T.runPrefix m.apply j b) ∈ T.channel W i j := by
  have hδ := m.delta_pos
  obtain ⟨c, hc, hce⟩ := hJ
  obtain ⟨o, ho, hol, hth, hoc⟩ := m.site_occ hc
  obtain ⟨jk2, jsep, jlen, jwin⟩ := m.junction_window hc
  rw [hce] at jk2 jlen jwin
  have hsi := m.strictlySeparated i
  have hcret := retained_of_mem_sites hsi hc
  have hcne : ∀ c' ∈ m.sites i, c ≠ c' + m.deletionLength := fun c' hc' => hsi.ne_right hδ hc hc'
  obtain ⟨hnt1, hnt2, hnpos⟩ := m.upperCutLength_spec ho hth
  rw [hoc] at hnt2
  have hsp := m.site_spec ho hth
  rw [hoc] at hsp
  have hEl := (upperOcc_spec ho).2.1
  rw [hol] at hEl
  obtain ⟨r, hr⟩ := hpre
  have hlenx : a + L ≤ (m.apply i).length := by
    have := congrArg List.length hr
    simp only [List.length_append, List.length_drop] at this
    omega
  have hY : (m.apply j).drop b = ((m.apply i).drop a).take L := by
    rw [← hr, List.take_append_of_le_length (by simp; omega),
        List.take_of_length_le (by simp; omega)]
  -- no junction of the host strictly inside `(a + d, a + L)`
  have hfreeR : ∀ J', IsJunction m.deletionLength (m.sites i) J' →
      ¬ (a + d < J' ∧ J' < a + d + (L - d)) := by
    rintro J' hJ' ⟨h1, h2⟩
    rcases jsep J' hJ' with h | h <;> omega
  -- the target suffix is original text, shorter than the last marker of its word
  have hT : (m.apply j).drop b = (W j).drop ((W j).length - L) ∧
      T.runPrefix m.apply j b = T.runPrefix W j ((W j).length - L) ∧
      ((j ∈ active W (t + 1) ∧ L < (marker W (t + 1) j).length) ∨
        (1 ≤ t ∧ j ∉ active W (t + 1))) := by
    by_cases hj : j ∈ active W (t + 1)
    · have hσ := marker_suffix W (t + 1) j
      have hterm := fun c' hc' => m.terminal hfr hj (c := c') hc'
      have hσl := hσ.length_le
      have hlenj : (m.apply j).length ≤ (W j).length := by
        rw [BlockDeletion.apply, length_deletePositions]; exact retainedCount_le _
      have hLs : L < (marker W (t + 1) j).length := by
        refine Nat.lt_of_not_le fun hge => ?_
        obtain ⟨hw1, -⟩ := m.tail_window hterm hσl (b' := (m.apply j).length -
          (marker W (t + 1) j).length) le_rfl (by omega)
        rw [show (m.apply j).length - ((m.apply j).length - (marker W (t + 1) j).length) =
          (marker W (t + 1) j).length by omega, ← List.suffix_iff_eq_drop.mp hσ] at hw1
        -- the terminal marker is a suffix of the target suffix, hence ends at `a + L` in the host
        have hσY : marker W (t + 1) j <:+ (m.apply j).drop b := by
          rw [← hw1, show (m.apply j).length - (marker W (t + 1) j).length = b + (L -
            (marker W (t + 1) j).length) by omega, ← List.drop_drop]
          exact List.drop_suffix _ _
        have hσU : marker W (t + 1) j <:+ (m.apply i).take (a + L) := by
          rw [List.take_add, ← hY]
          exact hσY.trans (List.suffix_append _ _)
        have hanc : a + L ∈ contextAnchors W (t + 1) (m.apply i) :=
          (mem_contextAnchors_succ W).mpr ⟨hlenx, j, hj, hσU⟩
        obtain ⟨p, hp, hret, hkp⟩ :=
          (m.contextAnchors_apply (r := t + 1) (by omega) le_rfl i _).mp hanc
        have hpA : p ∈ anchors W (t + 1) i := mem_insert_of_mem hp
        have hka := greatestPreimage_add_eq (show 0 < L - d by omega) hfreeR hret
          (fun c' hc' => (m.anchor_ne_site hpA hc').2) (by rw [hkp]; omega)
        rw [jk2] at hka
        have hno := (upperOcc_spec ho).2.2.2.2 p (hol ▸ hpA)
        exact hno ⟨by omega, by omega⟩
      obtain ⟨hw1, hw2⟩ := m.tail_window hterm hσl (b' := b) (by omega) (by omega)
      rw [show (m.apply j).length - b = L by omega] at hw1 hw2
      refine ⟨hw1, ?_, Or.inl ⟨hj, hLs⟩⟩
      rw [m.runPrefix_apply j b, hw2]
    · have ht : 1 ≤ t := by
        -- at level `0` an inactive word is empty, and so is its edited word
        by_contra h0
        have hnil : W j = [] := not_not.mp fun h =>
          hj (by rw [show t = 0 by omega]; exact (mem_active_one W).mpr h)
        have hlen := congrArg List.length (m.apply_of_inactive hj).2
        rw [hnil, List.length_nil] at hlen
        omega
      obtain ⟨hnil, happ⟩ := m.apply_of_inactive hj
      have hb : b = (W j).length - L := by rw [happ] at hL; omega
      refine ⟨by rw [happ, hb], ?_, Or.inr ⟨ht, hj⟩⟩
      rw [m.runPrefix_apply j b, hnil, hb]; simp [sitePositions]
  obtain ⟨hYold, hqj, hcase⟩ := hT
  -- the comparison starts at most `w` letters left of the junction
  set w := windowLength W t (W i) c with hwdef
  have hlab := m.labels_eq o ho hth
  rw [hoc, hol] at hlab
  have hdi : depthCut W t o m.minDepth = c + m.deletionLength := by omega
  rw [hdi] at hlab
  have hdw : d ≤ w := by
    refine Nat.le_of_not_lt fun hwd => ?_
    have ht : 1 ≤ t := by
      rcases hcase with ⟨hj, hLs⟩ | ⟨ht, -⟩
      · by_contra h0
        have h1 : (marker W (t + 1) j).length = 1 := by
          rw [show t = 0 by omega] at hj ⊢; exact length_marker_one hj
        omega
      · exact ht
    -- the level-`t` marker `τ` ending at the site
    have hcA : c ∈ contextAnchors W t (W i) := by
      have := hsp.2.2.2.2.2.1
      rw [hol] at this
      exact mem_contextAnchors_of_mem_anchors_of_lt_length this (by omega)
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨-, h, hh, hτ⟩ := (mem_contextAnchors_succ W).mp hcA
    have hτw : (marker W (t' + 1) h).length ≤ w := le_windowLength (by omega) le_rfl hh hτ
    set τ := marker W (t' + 1) h with hτdef
    have hτpos : 1 ≤ τ.length := List.length_pos_iff.mpr (marker_ne_nil (by omega) hh)
    -- the window left of the junction is original text
    have hfreeS : ∀ J', IsJunction m.deletionLength (m.sites i) J' →
        ¬ (a + d - τ.length < J' ∧ J' < a + d - τ.length + τ.length) :=
      fun J' hJ' h => m.junction_not_in_labelWindow hfr hc hJ' (by omega) (by omega)
    have hka := greatestPreimage_add_eq hτpos hfreeS hcret hcne (by rw [hce]; omega)
    have hwinS : ((m.apply i).drop (a + d - τ.length)).take τ.length =
        ((W i).drop (greatestPreimage (sitePositions m.deletionLength (m.sites i))
          (a + d - τ.length))).take τ.length := take_drop_deleteSites _ hfreeS
    rw [show greatestPreimage (sitePositions m.deletionLength (m.sites i))
        (a + d - τ.length) = c - τ.length by omega] at hwinS
    have hcW : c ≤ (W i).length := by omega
    have hτold : ((W i).drop (c - τ.length)).take τ.length = τ :=
      (List.prefix_iff_eq_take.mp ((suffix_take_iff hcW).mp hτ).2).symm
    have hτU : τ <+: (m.apply i).drop (a + (d - τ.length)) := by
      rw [show a + (d - τ.length) = a + d - τ.length by omega]
      rw [← List.take_append_drop τ.length ((m.apply i).drop (a + d - τ.length)), hwinS, hτold]
      exact List.prefix_append _ _
    -- `τ` lies strictly inside the target suffix
    have hτY : τ <+: ((m.apply j).drop b).drop (d - τ.length) := by
      rw [hY, List.drop_take, List.drop_drop, List.prefix_iff_eq_take, List.take_take,
        Nat.min_eq_left (by omega)]
      exact List.prefix_iff_eq_take.mp hτU
    have hLW : L ≤ (W j).length := by
      have := congrArg List.length hYold; simp at this; omega
    rw [hYold, List.drop_drop] at hτY
    rcases hcase with ⟨hj, hLs⟩ | ⟨-, hj⟩
    · have hσ := marker_suffix W (t' + 1 + 1) j
      have hσo := occ_of_suffix hσ
      have hσl := hσ.length_le
      have hτlen : (marker W (t' + 1) h).length = τ.length := rfl
      have hin := prefix_drop_of_occ hσo hτY (by omega) (by omega)
      rcases (marker_occurrences_in_next_marker (by omega) hj).2.2 h hh _ hin with h1 | h1 <;>
        omega
    · have hanc : (W j).length - L + (d - τ.length) + τ.length ∈ contextAnchors W (t' + 1) (W j) :=
        (mem_contextAnchors_succ W).mpr ⟨by omega, h, hh, suffix_take_of_occ hτY⟩
      have hA : (W j).length - L + (d - τ.length) + τ.length ∈ anchors W (t' + 1) j :=
        mem_insert_of_mem hanc
      rw [anchors_eq_singleton (t := t' + 1) (by omega) hj, mem_singleton] at hA
      omega
  -- the original pair, read from the right cut `c + δ`
  have hcW : c ≤ (W i).length := by omega
  have hcW' : c + m.deletionLength ≤ (W i).length := by omega
  obtain ⟨-, -, hlw, hlq⟩ := label_window hcW hcW' hlab (e := d) hdw
  have hfreeD : ∀ J', IsJunction m.deletionLength (m.sites i) J' → ¬ (a < J' ∧ J' < a + d) :=
    fun J' hJ' h => m.junction_not_in_labelWindow hfr hc hJ' (by omega) (by omega)
  have hkaD := greatestPreimage_add_eq hd0 hfreeD hcret hcne hce
  have hkRa : greatestPreimage (sitePositions m.deletionLength (m.sites i)) a = c - d := by omega
  have hwinD : ((m.apply i).drop a).take d = ((W i).drop (c - d)).take d := by
    have := take_drop_deleteSites (W i) hfreeD
    rw [hkRa] at this
    exact this
  have hwinR : ((m.apply i).drop (a + d)).take (L - d) =
      ((W i).drop (c + m.deletionLength)).take (L - d) := by
    rw [show L - d = min (L - d) m.upperCutLength by omega, ← List.take_take, jwin, List.take_take]
  have hYsplit : (m.apply j).drop b =
      ((W i).drop (c + m.deletionLength - d)).take d ++
          ((W i).drop (c + m.deletionLength)).take (L - d) := by
    rw [hY, ← List.take_append_drop d (((m.apply i).drop a).take L), List.take_take,
      Nat.min_eq_left hdL.le, hwinD, hlw, List.drop_take, List.drop_drop, hwinR]
  have hold : (W j).drop ((W j).length - L) <+: (W i).drop (c + m.deletionLength - d) := by
    rw [← hYold, hYsplit]
    conv_rhs =>
        rw [← List.take_append_drop d ((W i).drop (c + m.deletionLength - d)), List.drop_drop,
      show c + m.deletionLength - d + d = c + m.deletionLength by omega]
    exact (List.prefix_append_right_inj _).mpr (List.take_prefix _ _)
  have hqi : T.runPrefix m.apply i a = T.runPrefix W i (c + m.deletionLength - d) := by
    rw [m.runPrefix_apply i a, hkRa, hlq]
  rw [hqi, hqj]
  exact Table.pair_mem_channel (by omega) (by omega) hold
end DeciSigma1.Holes.Fresh.BlockDeletion
