-- Prove2me | solution 1 for Finset.mul_kneser
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:39.054058+00:00
-- url     : https://prove2.me/submissions/d1da45f2-d3c2-4900-9ad0-2d7501f9013b

module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Theorems.Thm_Finset_mulStab_mul_ssubset_mulStab
public import Theorems.Thm_Finset_mulStab_union
public import Theorems.Thm_Finset_mul_aux1
public import Theorems.Thm_Finset_disjoint_smul_mulStab
public import Theorems.Thm_Finset_disjoint_mul_sub_card_le
public import Theorems.Thm_Finset_inter_mul_sub_card_le
public import Theorems.Thm_Finset_card_mulStab_dvd_card_mulStab
public import Theorems.Thm_Finset_card_mul_card_eq_mulStab_card_mul_coe
public import Theorems.Thm_P2M_Finset_card_mulStab_mul_card_image_coe__56c0b835d7e6

section
public section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
namespace Finset
set_option linter.dupNamespace false in
@[to_additive]
private lemma card_mul_add_card_lt (hC : C.Nonempty) (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hCst : C ⊆ s * t) (hCst' : Disjoint C (s' * t')) :
    #(s' * t') + #s' < #(s * t) + #s :=
  add_lt_add_of_lt_of_le
      (by
        rw [← tsub_pos_iff_lt, ← card_sdiff_of_subset (mul_subset_mul hs ht), card_pos]
        exact hC.mono (subset_sdiff.2 ⟨hCst, hCst'⟩)) <|
    card_le_card hs
variable (s t)
end Finset
end
end

set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
open Finset
variable (s t)
namespace Finset
theorem _root_.solution :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab)
      ≤ #(s * t) + #(s * t).mulStab := by
  -- We're doing induction on `#(s * t) + #s` generalizing the group. This is a bit tricky
  -- in Lean.
  set n : ℕ := #(s * t) + #s with hn
  clear_value n
  induction n using Nat.strong_induction_on generalizing α with | h n ih =>
  subst hn
  -- The cases `s = ∅` and `t = ∅` are easily taken care of.
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  classical
  -- We distinguish whether `s * t` has trivial stabilizer.
  obtain hstab | hstab := ne_or_eq (s * t).mulStab 1
  · have image_coe_mul :
      ((s * t).image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) =
        s.image (↑) * t.image (↑) :=
      image_mul (QuotientGroup.mk' _ : α →* α ⧸ stabilizer α (↑(s * t) : Set α))
    suffices hineq :
      #(s * t).mulStab *
          (#(s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) +
              #(t.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) -  1) ≤
        #(s * t) by
    -- now to prove that `#(s * (s * t).mulStab) = #(s * t).mulStab * #(s.image (↑))` and
    -- the analogous statement for `s` and `t` interchanged
    -- this will conclude the proof of the first case immediately
      rw [mul_tsub, mul_one, mul_add, tsub_le_iff_left, card_mulStab_mul_card_image_coe',
        card_mulStab_mul_card_image_coe'] at hineq
      convert! hineq using 1
      exact add_comm _ _
    refine le_of_le_of_eq (mul_le_mul_right ?_ _) (card_mul_card_eq_mulStab_card_mul_coe s t).symm
    have := ih _ ?_ (s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) (t.image (↑)) rfl
    · classical
      simpa only [← image_coe_mul, mulStab_image_coe_quotient (hs.mul ht), mul_one,
        tsub_le_iff_right, card_one] using this
    rw [← image_coe_mul, card_mul_card_eq_mulStab_card_mul_coe]
    exact
      add_lt_add_of_lt_of_le
        (lt_mul_left ((hs.mul ht).image _).card_pos <|
          Finset.one_lt_card.2 ((hs.mul ht).mulStab_nontrivial.2 hstab))
        card_image_le
  -- Simplify the induction hypothesis a bit. We will only need it over `α` from now on.
  simp only [hstab, mul_one, card_one] at ih ⊢
  replace ih := fun s' t' h => @ih _ h α _ _ s' t' rfl
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial
  · rw [card_singleton, card_singleton_mul, add_comm]
  have : b / a ∉ t.mulStab := by
    refine fun h => hab (Eq.symm (eq_of_div_eq_one ?_))
    replace h := subset_mulStab_mul_right hs h
    rw [hstab, mem_one] at h
    exact h
  simp only [mem_mulStab' ht, smul_eq_mul, Classical.not_forall, exists_prop] at this
  obtain ⟨c, hc, hbac⟩ := this
  set t' := (a / c) • t with ht'
  clear_value t'
  rw [← inv_smul_eq_iff] at ht'
  subst ht'
  rename' t' => t
  rw [mem_inv_smul_finset_iff, smul_eq_mul, div_mul_cancel] at hc
  rw [div_mul_comm, mem_inv_smul_finset_iff, smul_eq_mul, ← mul_assoc, div_mul_div_cancel',
    div_self', one_mul] at hbac
  rw [smul_finset_nonempty] at ht
  simp only [mul_smul_comm, mulStab_smul, card_smul_finset] at *
  have hst : (s ∩ t).Nonempty := ⟨_, mem_inter.2 ⟨ha, hc⟩⟩
  have hsts : s ∩ t ⊂ s :=
    ⟨inter_subset_left, not_subset.2 ⟨_, hb, fun h => hbac <| inter_subset_right h⟩⟩
  clear! a b
  set convergent : Set (Finset α) :=
    {C | C ⊆ s * t ∧ #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab}
  have convergent_nonempty : convergent.Nonempty := by
    refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_left (card_le_card <|
      subset_mul_left _ <| one_mem_mulStab.2 <| hst.mul <| hs.mono subset_union_left) _).trans <|
        ih (s ∩ t) (s ∪ t) ?_⟩
    exact add_lt_add_of_le_of_lt (card_le_card inter_mul_union_subset) (card_lt_card hsts)
  let C := argminOn (fun C : Finset α => #C.mulStab) _ convergent_nonempty
  set H := C.mulStab with hH
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argminOn_mem _ _ _
  have hCmin (D : Finset α) (hDH : D.mulStab ⊂ H) : D ∉ convergent := fun hD ↦
    (card_lt_card hDH).not_ge <| argminOn_le (fun D : Finset α => #D.mulStab) _ hD
  clear_value C
  clear convergent_nonempty
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp [hst.ne_empty] at hCcard
  -- If the stabilizer of `C` is trivial, then
  -- `#s + #t - 1 = #(s ∩ t) + #(s ∪ t) - 1 = ≤ #C ≤ #(s * t)`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_mulStab.2 hC)
  · simp only [hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard
    grw [hCcard, hCst]
  exfalso
  have : ¬s * t * H ⊆ s * t := by
    rw [mul_subset_left_iff (hs.mul ht), hstab, ← coe_subset, coe_one]
    exact hCstab.coe.not_subset_singleton
  simp_rw [mul_subset_iff_left, Classical.not_forall, mem_mul] at this
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hab⟩ := this
  set s₁ := s ∩ a • H with hs₁
  set s₂ := s ∩ b • H with hs₂
  set t₁ := t ∩ b • H with ht₁
  set t₂ := t ∩ a • H with ht₂
  have hs₁s : s₁ ⊆ s := inter_subset_left
  have hs₂s : s₂ ⊆ s := inter_subset_left
  have ht₁t : t₁ ⊆ t := inter_subset_left
  have ht₂t : t₂ ⊆ t := inter_subset_left
  have has₁ : a ∈ s₁ := mem_inter.mpr ⟨ha, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hbt₁ : b ∈ t₁ := mem_inter.mpr ⟨hb, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hs₁ne : s₁.Nonempty := ⟨_, has₁⟩
  have ht₁ne : t₁.Nonempty := ⟨_, hbt₁⟩
  set C₁ := C ∪ s₁ * t₁
  set C₂ := C ∪ s₂ * t₂
  set H₁ := (s₁ * t₁).mulStab with hH₁
  set H₂ := (s₂ * t₂).mulStab
  have hC₁st : C₁ ⊆ s * t := union_subset hCst (mul_subset_mul hs₁s ht₁t)
  have hC₂st : C₂ ⊆ s * t := union_subset hCst (mul_subset_mul hs₂s ht₂t)
  have hstabH₁ : s₁ * t₁ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hstabH₂ : s₂ * t₂ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm, mul_comm s₂ t₂]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hCst₁ := disjoint_of_subset_right hstabH₁ (disjoint_smul_mulStab hCst hab)
  have hCst₂ := disjoint_of_subset_right hstabH₂ (disjoint_smul_mulStab hCst hab)
  have hst₁ : #(s₁ * t₁) + #s₁ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₁s ht₁t hCst hCst₁
  have hst₂ : #(s₂ * t₂) + #s₂ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₂s ht₂t hCst hCst₂
  have hC₁stab : C₁.mulStab = H₁ := mulStab_union hs₁ne ht₁ne hab hCst₁
  have hH₁H : H₁ ⊂ H := mulStab_mul_ssubset_mulStab hs₁ne ht₁ne hab
  have aux1₁ :=
    mul_aux1 (ih _ _ hst₁) hCcard
      (not_le.1 fun h => hCmin _ (hC₁stab.trans_ssubset hH₁H) ⟨hC₁st, h⟩) hC₁stab hCst₁
  obtain ht₂ | ht₂ne := t₂.eq_empty_or_nonempty
  · have aux₁_contr :=
      disjoint_mul_sub_card_le b (hs₁s has₁) (disjoint_iff_inter_eq_empty.2 ht₂) hH₁H.subset
    linarith [aux1₁, aux₁_contr, Int.natCast_nonneg #(t₁ * (s₁ * t₁).mulStab)]
  obtain hs₂ | hs₂ne := s₂.eq_empty_or_nonempty
  · have aux1₁_contr :
      (#C.mulStab : ℤ) - #(t₁ * (s₁ * t₁).mulStab) ≤
        #((s ∪ t) * C.mulStab) - #((s ∪ t) * (s₁ * t₁).mulStab) := by
      simpa [union_comm, mul_comm s₁ t₁] using
        disjoint_mul_sub_card_le a (ht₁t hbt₁) (disjoint_iff_inter_eq_empty.2 hs₂)
          (by rw [mul_comm]; exact hH₁H.subset)
    linarith [aux1₁, aux1₁_contr, Int.natCast_nonneg #(s₁ * (s₁ * t₁).mulStab)]
  have hC₂stab : C₂.mulStab = H₂ := mulStab_union hs₂ne ht₂ne (by rwa [mul_comm]) hCst₂
  have hH₂H : H₂ ⊂ H := mulStab_mul_ssubset_mulStab hs₂ne ht₂ne (by rwa [mul_comm])
  have aux1₂ :=
    mul_aux1 (ih _ _ hst₂) hCcard
      (not_le.1 fun h => hCmin _ (hC₂stab.trans_ssubset hH₂H) ⟨hC₂st, h⟩) hC₂stab hCst₂
  obtain habH | habH := eq_or_ne (a • H) (b • H)
  · rw [hH₁, hs₁, ht₁, ← habH, hH] at hH₁H
    refine aux1₁.not_ge ?_
    simp only [hs₁, ht₁, ← habH, inter_mul_sub_card_le (hs₁s has₁) hH₁H.subset, H]
  -- temporarily skipping deduction of inequality (2)
  set S := a • H \ (s₁ ∪ t₂) with hS
  set T := b • H \ (s₂ ∪ t₁) with hT
  have hST : Disjoint S T :=
    (C.pairwiseDisjoint_smul_finset_mulStab (Set.mem_range_self _) (Set.mem_range_self _)
          habH).mono
      sdiff_le sdiff_le
  have hSst : S ⊆ a • H \ (s ∪ t) := by
    simp only [hS, hs₁, ht₂, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hTst : T ⊆ b • H \ (s ∪ t) := by
    simp only [hT, hs₂, ht₁, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hSTst : Disjoint (S ∪ T) (s ∪ t) := (subset_sdiff.1 hSst).2.sup_left (subset_sdiff.1 hTst).2
  have hstconv : s * t ∉ convergent := by
    apply hCmin (s * t)
    rw [hstab]
    refine (hC.mulStab_nontrivial.mp hCstab).symm.ssubset_of_subset ?_
    simp only [one_subset, one_mem_mulStab, hC]
  simp only [Set.mem_ofPred_eq, Subset.rfl, true_and, not_le, hstab, mul_one, card_one,
    convergent] at hstconv
  zify at hstconv
  have hSTcard : (#S : ℤ) + #T + #(s ∪ t) ≤ #((s ∪ t) * H) := by
    norm_cast
    conv_lhs => rw [← card_union_of_disjoint hST, ← card_union_of_disjoint hSTst, ← mul_one (s ∪ t)]
    refine card_le_card
      (union_subset (union_subset ?_ ?_) <| mul_subset_mul_left <| one_subset.2 hC.one_mem_mulStab)
    · exact hSst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_left _ ha)
    · exact hTst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_right _ hb)
  have hH₁ne : H₁.Nonempty := (hs₁ne.mul ht₁ne).mulStab
  have hH₂ne : H₂.Nonempty := (hs₂ne.mul ht₂ne).mulStab
  -- Now we prove inequality (2)
  have aux2₁ : (#s₁ : ℤ) + #t₁ + #H₁ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₁H.subset).trans_lt aux1₁) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₁ne.mul ht₁ne) hH₁H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    gcongr _ - (Nat.cast ?_ + Nat.cast ?_) <;> exact card_le_card_mul_right hH₁ne
  have aux2₂ : (#s₂ : ℤ) + #t₂ + #H₂ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₂H.subset).trans_lt aux1₂) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₂ne.mul ht₂ne) hH₂H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    exact sub_le_sub_left (add_le_add (Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) <|
      Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) _
  -- Now we deduce inequality (3) using the above lemma in addition to the facts that `s * t` is not
  -- convergent and then induction hypothesis applied to `sᵢ` and `tᵢ`
  have aux3₁ : (#S : ℤ) + #T + #s₁ + #t₁ - #H₁ < #H :=
    calc
      (#S : ℤ) + #T + #s₁ + #t₁ - #H₁
        < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₁ * t₁) := by
        have ih₁ :=
          (add_le_add (card_le_card_mul_right hH₁ne) <| card_le_card_mul_right hH₁ne).trans
            (ih _ _ hst₁)
        zify at ih₁
        linarith [hstconv, ih₁]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₁ * t₁) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₁] using card_le_card hC₁st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux3₂ : (#S : ℤ) + #T + #s₂ + #t₂ - #H₂ < #H :=
    calc
      (#S : ℤ) + #T + #s₂ + #t₂ - #H₂
       < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₂ * t₂) := by
        have ih₂ :=
          (add_le_add (card_le_card_mul_right hH₂ne) <| card_le_card_mul_right hH₂ne).trans
            (ih _ _ hst₂)
        zify at hstconv ih₂
        linarith [ih₂]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₂ * t₂) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₂] using card_le_card hC₂st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux4₁ : #H ≤ #S + (#s₁ + #t₂) := by
    grw [← card_smul_finset a H, card_le_card_sdiff_add_card, card_union_le]
  have aux4₂ : #H ≤ #T + (#s₂ + #t₁) := by
    grw [← card_smul_finset b H, card_le_card_sdiff_add_card, card_union_le]
  linarith [aux2₁, aux2₂, aux3₁, aux3₂, aux4₁, aux4₂]
end Finset
